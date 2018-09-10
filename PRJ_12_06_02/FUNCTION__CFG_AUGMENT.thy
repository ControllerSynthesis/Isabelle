section {*FUNCTION\_\_CFG\_AUGMENT*}
theory
  FUNCTION__CFG_AUGMENT

imports
  PRJ_12_06_02__ENTRY

begin

definition F_CFG_AUGMENT__input :: "
  ('nonterminal DT_symbol, 'event DT_symbol) cfg
  \<Rightarrow> 'event DT_symbol
  \<Rightarrow> 'nonterminal DT_symbol
  \<Rightarrow> ('nonterminal DT_symbol, 'event DT_symbol) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_AUGMENT__input G Do S' G' \<equiv>
  valid_cfg G
  \<and> Do = F_FRESH (cfg_events G)
  \<and> S' = F_FRESH (cfg_nonterminals G)
  \<and> G' = F_CFG_AUGMENT G S' Do"

theorem F_CFG_AUGMENT__makes_CFG: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> valid_cfg G'"
  apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   apply(auto)
  done

lemma F_CFG_AUGMENT__FirstStep: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfgSTD.derivation G' d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)
  \<Longrightarrow> d (Suc n) \<noteq> None
  \<Longrightarrow> d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = cfg_initial G', prod_rhs = [teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf = [teB Do, teA (cfg_initial G), teB Do]\<rparr>)"
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   prefer 2
   apply(case_tac "d (Suc 0)")
    apply(case_tac n)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(rule_tac
      n="Suc n"
      and i="Suc 0"
      in cfgSTD.derivationNoFromNone2)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b y)(*strict*)
   apply(case_tac option)
    apply(rename_tac option b y)(*strict*)
    apply(clarsimp)
    apply(rename_tac b y)(*strict*)
    apply(rule cfgSTD.derivation_Always_PreEdge_prime)
     apply(rename_tac b y)(*strict*)
     apply(force)
    apply(rename_tac b y)(*strict*)
    apply(force)
   apply(rename_tac option b y a)(*strict*)
   apply(force)
  apply(erule exE)+
  apply(rename_tac e c)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G' \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr> e c")
   apply(rename_tac e c)(*strict*)
   prefer 2
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac e c)(*strict*)
     apply(force)
    apply(rename_tac e c)(*strict*)
    apply(force)
   apply(rename_tac e c)(*strict*)
   apply(force)
  apply(rename_tac e c)(*strict*)
  apply(case_tac e)
  apply(rename_tac e c prod_lhs prod_rhs)(*strict*)
  apply(case_tac c)
  apply(rename_tac e c prod_lhs prod_rhs cfg_conf)(*strict*)
  apply(rename_tac A w s)
  apply(rename_tac e c A w s)(*strict*)
  apply(subgoal_tac "A=cfg_initial G' \<and> w=[teB Do, teA (cfg_initial G), teB Do] \<and> s=[teB Do, teA (cfg_initial G), teB Do]")
   apply(rename_tac e c A w s)(*strict*)
   apply(force)
  apply(rename_tac e c A w s)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac e c A w s y l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac e c A w s y l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac w y)(*strict*)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(clarsimp)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = w\<rparr>"
      and P="\<lambda>x. prod_lhs x \<in> cfg_nonterminals G \<and> setA (prod_rhs x) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs x) \<subseteq> cfg_events G"
      in ballE)
    apply(rename_tac w y)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac w y)(*strict*)
     apply(force)
    apply(rename_tac w y)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(force)
   apply(rename_tac w y)(*strict*)
   apply(force)
  apply(rename_tac e c A w s y l r a list)(*strict*)
  apply(force)
  done

lemma F_CFG_AUGMENT__later_at_old_grammar: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)
  \<Longrightarrow> d (Suc n) = Some (pair e \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G"
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(force)
   apply(blast)
  apply(subgoal_tac "\<forall>n. (case d (Suc n) of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> setA (cfg_conf c) \<subseteq> cfg_nonterminals G)")
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
  apply(rule allI)
  apply(rename_tac na)(*strict*)
  apply(rule_tac
      m="Suc 0"
      and n="na"
      in cfgRM.property_preseved_under_steps_is_invariant2)
      apply(rename_tac na)(*strict*)
      apply(force)
     apply(rename_tac na)(*strict*)
     apply(clarsimp)
     apply(simp add: valid_cfg_def)
    apply(rename_tac na)(*strict*)
    apply(force)
   apply(rename_tac na)(*strict*)
   apply(force)
  apply(rename_tac na)(*strict*)
  apply(rule allI)
  apply(rename_tac na i)(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(case_tac "d (Suc i)")
   apply(rename_tac na i)(*strict*)
   apply(clarsimp)
  apply(rename_tac na i a)(*strict*)
  apply(subgoal_tac "\<exists>e c. a = pair (Some e) c")
   apply(rename_tac na i a)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_after_0)
    apply(rename_tac na i a)(*strict*)
    apply(force)
   apply(rename_tac na i a)(*strict*)
   apply(force)
  apply(rename_tac na i a)(*strict*)
  apply(erule exE)+
  apply(rename_tac na i a ea c)(*strict*)
  apply(subgoal_tac "setA (cfg_conf c) \<subseteq> cfg_nonterminals G")
   apply(rename_tac na i a ea c)(*strict*)
   apply(force)
  apply(rename_tac na i a ea c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac na i a ea c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in cfgRM.pre_some_position_is_some_position)
     apply(rename_tac na i a ea c)(*strict*)
     apply(force)
    apply(rename_tac na i a ea c)(*strict*)
    apply(force)
   apply(rename_tac na i a ea c)(*strict*)
   apply(force)
  apply(rename_tac na i a ea c)(*strict*)
  apply(erule exE)+
  apply(rename_tac na i a ea c eaa ca)(*strict*)
  apply(subgoal_tac "cfgRM_step_relation G' ca ea c")
   apply(rename_tac na i a ea c eaa ca)(*strict*)
   prefer 2
   apply(rule cfgRM.position_change_due_to_step_relation)
     apply(rename_tac na i a ea c eaa ca)(*strict*)
     apply(force)
    apply(rename_tac na i a ea c eaa ca)(*strict*)
    apply(force)
   apply(rename_tac na i a ea c eaa ca)(*strict*)
   apply(force)
  apply(rename_tac na i a ea c eaa ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac na i a ea c eaa ca cfg_confa)(*strict*)
  apply(case_tac ca)
  apply(rename_tac na i a ea c eaa ca cfg_confa cfg_confaa)(*strict*)
  apply(case_tac ea)
  apply(rename_tac na i a ea c eaa ca cfg_confa cfg_confaa prod_lhs prod_rhs)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(rename_tac na i a ea c eaa ca cfg_conf cfg_confa prod_lhs prod_rhs)(*strict*)
  apply(clarsimp)
  apply(rename_tac na i ea prod_lhs prod_rhs x l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac na i ea prod_lhs prod_rhs x l r)(*strict*)
   apply(force)
  apply(rename_tac na i ea prod_lhs prod_rhs x l r)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(erule disjE)
   apply(rename_tac na i ea prod_lhs prod_rhs x l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac na i ea l r)(*strict*)
   apply(simp add: valid_cfg_def)
  apply(rename_tac na i ea prod_lhs prod_rhs x l r)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(rename_tac na i ea prod_lhsa prod_rhsa x l r)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>prod_lhs = prod_lhsa, prod_rhs = prod_rhsa\<rparr>"
      and P="\<lambda>x. prod_lhs x \<in> cfg_nonterminals G \<and> setA (prod_rhs x) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs x) \<subseteq> cfg_events G"
      in ballE)
   apply(rename_tac na i ea prod_lhsa prod_rhsa x l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac na i ea prod_lhs prod_rhsa x l r)(*strict*)
   apply(force)
  apply(rename_tac na i ea prod_lhs prod_rhsa x l r)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__initial_not_in_nonterms: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfg_initial G' \<notin> cfg_nonterminals G"
  apply(rule_tac
      t="cfg_initial G'"
      and s="F_FRESH (cfg_nonterminals G)"
      in ssubst)
   apply(simp add: F_CFG_AUGMENT_def)
  apply(rule F_FRESH_is_fresh)
  apply(simp add: valid_cfg_def)
  done

lemma F_CFG_AUGMENT__preserves_derivation: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> cfgSTD.derivation G' d"
  apply(simp add: cfgSTD.derivation_def)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(auto)
  apply(rename_tac nat option b)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat option b)(*strict*)
   apply(auto)
  apply(rename_tac nat option b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat option b a optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac nat b optiona ba a l r)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  done

lemma F_CFG_AUGMENT__preserves_RMderivation: "
    valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.derivation G' d"
  apply(simp add: cfgRM.derivation_def)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(auto)
  apply(rename_tac nat option b)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat option b)(*strict*)
   apply(auto)
  apply(rename_tac nat option b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat option b a optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(auto)
  apply(rename_tac nat b optiona ba a l r)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  done

lemma F_CFG_AUGMENT__reflects_derivation_hlp: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD.derivation G' d
  \<Longrightarrow> d (i + j) = Some (pair e2 \<lparr>cfg_conf = w'\<rparr>)
  \<Longrightarrow> setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G"
  apply(subgoal_tac " \<forall>e2 w'. d (i+j)=Some (pair e2 \<lparr>cfg_conf=w'\<rparr>) \<longrightarrow> (setA w' \<subseteq> cfg_nonterminals G \<and> setB w' \<subseteq> cfg_events G) ")
   apply(clarsimp)
  apply(rule_tac
      m="i"
      and n="j"
      in cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(blast)+
     apply(clarsimp)
    apply(arith)
   apply(arith)
  apply(rule allI)
  apply(rename_tac ia)(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(rule allI)+
  apply(rename_tac ia e2a w'nonterminal)(*strict*)
  apply(rule impI)
  apply(subgoal_tac "\<exists>e. Some e=e2a")
   apply(rename_tac ia e2a w'nonterminal)(*strict*)
   prefer 2
   apply(case_tac e2a)
    apply(rename_tac ia e2a w'nonterminal)(*strict*)
    apply(rule cfgSTD.derivation_Always_PreEdge_prime)
     apply(rename_tac ia e2a w'nonterminal)(*strict*)
     apply(blast)+
  apply(rename_tac ia e2a w'nonterminal)(*strict*)
  apply(erule exE)+
  apply(rename_tac ia e2a w'nonterminal e)(*strict*)
  apply(subgoal_tac "\<exists>e c. d ia = Some (pair e c)")
   apply(rename_tac ia e2a w'nonterminal e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc ia"
      in cfgSTD.pre_some_position_is_some_position)
     apply(rename_tac ia e2a w'nonterminal e)(*strict*)
     apply(blast)
    apply(rename_tac ia e2a w'nonterminal e)(*strict*)
    apply(blast)
   apply(rename_tac ia e2a w'nonterminal e)(*strict*)
   apply(force)
  apply(rename_tac ia e2a w'nonterminal e)(*strict*)
  apply(erule exE)+
  apply(rename_tac ia e2a w'nonterminal e ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac ia e2a w'nonterminal e ea c cfg_conf)(*strict*)
  apply(rename_tac cw)
  apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
  apply(erule_tac
      x="ea"
      in allE)
  apply(erule_tac
      x="cw"
      in allE)
  apply(erule impE)
   apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
   apply(blast)
  apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "cfgSTD_step_relation G' \<lparr>cfg_conf = cw\<rparr> e \<lparr>cfg_conf = w'nonterminal\<rparr>")
   apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
   prefer 2
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
     apply(blast)+
  apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = cw\<rparr> e \<lparr>cfg_conf = w'nonterminal\<rparr>")
   apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
   prefer 2
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac ia e ea l r)(*strict*)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(clarsimp)
   apply(rename_tac ia ea l r)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac ia ea l r)(*strict*)
    apply(force)
   apply(rename_tac ia ea l r)(*strict*)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> cfg_nonterminals G")
    apply(rename_tac ia ea l r)(*strict*)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac ia ea l r)(*strict*)
     apply(force)
    apply(rename_tac ia ea l r)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac ia ea l r)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
  apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ia e ea l r)(*strict*)
  apply(simp only: setAConcat concat_asso setBConcat)
  apply(simp add: valid_cfg_def)
  done

lemma F_CFG_AUGMENT__reflects_derivation: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD.derivation G' d
  \<Longrightarrow> cfgSTD.derivation G d"
  apply(subgoal_tac "\<forall>i e2 w'. d i = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>) \<longrightarrow> setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G")
   prefer 2
   apply(rule allI)+
   apply(rename_tac i e2 w')(*strict*)
   apply(rule impI)
   apply(rule_tac
      d="d"
      in F_CFG_AUGMENT__reflects_derivation_hlp)
           apply(rename_tac i e2 w')(*strict*)
           apply(force)
          apply(rename_tac i e2 w')(*strict*)
          apply(force)
         apply(rename_tac i e2 w')(*strict*)
         apply(force)
        apply(rename_tac i e2 w')(*strict*)
        apply(force)
       apply(rename_tac i e2 w')(*strict*)
       apply(force)
      apply(rename_tac i e2 w')(*strict*)
      apply(force)
     apply(rename_tac i e2 w')(*strict*)
     apply(force)
    apply(rename_tac i e2 w')(*strict*)
    apply(force)
   apply(rename_tac i e2 w')(*strict*)
   apply(force)
  apply(simp add: cfgSTD.derivation_def)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (d 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) i'2 i1v i2)) (d i'))) (d i)"
      in allE)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(auto)
  apply(rename_tac nat option b)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat option b)(*strict*)
   apply(auto)
  apply(rename_tac nat option b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat option b a optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac nat b optiona ba a l r)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(erule disjE)
   apply(rename_tac nat b optiona ba a l r)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac nat b optiona ba a l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat b optiona ba l r)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac nat b optiona ba l r)(*strict*)
   apply(force)
  apply(rename_tac nat b optiona ba l r)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(case_tac ba)
  apply(rename_tac nat b optiona ba l r cfg_confa)(*strict*)
  apply(auto)
  apply(rename_tac nat b optiona l r)(*strict*)
  apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> cfg_nonterminals G")
   apply(rename_tac nat b optiona l r)(*strict*)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    apply(rename_tac nat b optiona l r)(*strict*)
    apply(force)
   apply(rename_tac nat b optiona l r)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac nat b optiona l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  done

lemma cfgSTD_first_F_CFG_AUGMENT__no_change_on_old_input: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD_first G k w = cfgSTD_first G' k w"
  apply(rule_tac
      t="cfgSTD_first G k w"
      and s="(\<lambda>x. take k x) ` {r. \<exists>d e1 n. cfgSTD.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=liftB r\<rparr>) }"
      in ssubst)
   apply(rule cfgSTD_first_sound)
  apply(rule_tac
      t="cfgSTD_first G' k w"
      and s="(\<lambda>x. take k x) ` {r. \<exists>d e1 n. cfgSTD.derivation G' d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=liftB r\<rparr>) }"
      in ssubst)
   apply(rule cfgSTD_first_sound)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(rule inMap)
   apply(clarsimp)
   apply(rule_tac
      x="xa"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(rule F_CFG_AUGMENT__preserves_derivation)
        apply(rename_tac xa d e1 n)(*strict*)
        apply(force)
       apply(rename_tac xa d e1 n)(*strict*)
       apply(force)
      apply(rename_tac xa d e1 n)(*strict*)
      apply(force)
     apply(rename_tac xa d e1 n)(*strict*)
     apply(force)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(rule_tac
      x="e1"
      in exI)
   apply(rule_tac
      x="n"
      in exI)
   apply(auto)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule inMap)
  apply(auto)
  apply(rule_tac
      x="xa"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac xa d e1 n)(*strict*)
   prefer 2
   apply(rule_tac
      x="e1"
      in exI)
   apply(rule_tac
      x="n"
      in exI)
   apply(auto)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule F_CFG_AUGMENT__reflects_derivation)
         apply(rename_tac xa d e1 n)(*strict*)
         apply(force)
        apply(rename_tac xa d e1 n)(*strict*)
        apply(force)
       apply(rename_tac xa d e1 n)(*strict*)
       apply(force)
      apply(rename_tac xa d e1 n)(*strict*)
      apply(force)
     apply(rename_tac xa d e1 n)(*strict*)
     apply(force)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(force)
  done

lemma F_CFG_AUGMENT__two_elements_construct_domain_subset: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
  apply(simp add: F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(force)
  done

lemma F_CFG_AUGMENT__cfg_events: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfg_events G' - {Do} = cfg_events G"
  apply(simp add: F_CFG_AUGMENT_def)
  apply(rule order_antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "F_FRESH (cfg_events G) \<notin> cfg_events G")
   apply(force)
  apply(rule F_FRESH_is_fresh)
  apply(simp add: valid_cfg_def)
  done

lemma F_CFG_AUGMENT__on_old_grammar_basically: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfgSTD.derivation G' d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)
  \<Longrightarrow> d (Suc n) \<noteq> None
  \<Longrightarrow> maximum_of_domain d x
  \<Longrightarrow> \<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>)"
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(force)+
  apply(subgoal_tac "x\<ge>Suc 0")
   prefer 2
   apply(rule cfgSTD.allPreMaxDomSome_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "x\<ge>Suc n")
   prefer 2
   apply(rule cfgSTD.allPreMaxDomSome_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      x="Suc n"
      and m="Suc 0"
      and n="x-Suc 0"
      in cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(force)
     apply(rule_tac
      x="Some \<lparr>prod_lhs = cfg_initial G', prod_rhs = [teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in exI)
     apply(rule_tac
      x="[teA (cfg_initial G)]"
      in exI)
     apply(clarsimp)
     apply(rename_tac y)(*strict*)
     apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
      apply(rename_tac y)(*strict*)
      apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
       apply(rename_tac y)(*strict*)
       apply(force)
      apply(rename_tac y)(*strict*)
      apply(rule F_FRESH_is_fresh)
      apply(simp add: valid_cfg_def)
     apply(rename_tac y)(*strict*)
     apply(simp add: valid_cfg_def)
    apply(force)
   apply(force)
  apply(rule allI)
  apply(rename_tac i)(*strict*)
  apply(rule impI)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac i)(*strict*)
     apply(blast)
    apply(rename_tac i)(*strict*)
    apply(blast)
   apply(rename_tac i)(*strict*)
   apply(arith)
  apply(rename_tac i)(*strict*)
  apply(erule exE)+
  apply(rename_tac i e c)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac i e c ea w)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "cfgSTD_step_relation G' \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr> e c")
   apply(rename_tac i e c ea w)(*strict*)
   prefer 2
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac i e c ea w)(*strict*)
     apply(blast)
    apply(rename_tac i e c ea w)(*strict*)
    apply(blast)
   apply(rename_tac i e c ea w)(*strict*)
   apply(blast)
  apply(rename_tac i e c ea w)(*strict*)
  apply(case_tac c)
  apply(rename_tac i e c ea w cfg_conf)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i e ea w y l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac i e ea w y l r)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e ea w y l r a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea w y r list)(*strict*)
  apply(case_tac r)
   apply(rename_tac i e ea w y r list)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e ea w y r list a lista)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
   apply(rename_tac i e ea w y r list a lista)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac i e ea w y r list a lista)(*strict*)
  apply(thin_tac "r=a#lista")
  apply(clarsimp)
  apply(rename_tac i e ea y list w')(*strict*)
  apply(subgoal_tac "e \<in> cfg_productions G")
   apply(rename_tac i e ea y list w')(*strict*)
   prefer 2
   apply(subgoal_tac "e \<noteq> \<lparr>prod_lhs=cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>")
    apply(rename_tac i e ea y list w')(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rename_tac i e ea y list w')(*strict*)
   apply(clarsimp)
   apply(rename_tac i ea y list w')(*strict*)
   apply(simp add: F_CFG_AUGMENT_def)
  apply(rename_tac i e ea y list w')(*strict*)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      and P="\<lambda>e. prod_lhs e \<in> cfg_nonterminals G \<and> setA (prod_rhs e) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs e) \<subseteq> cfg_events G"
      in ballE)
   apply(rename_tac i e ea y list w')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i e ea y list w')(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac i e ea y list w')(*strict*)
   apply(rule setB_set_not)
   apply(rule_tac
      B="cfg_events G"
      in nset_mp)
    apply(rename_tac i e ea y list w')(*strict*)
    apply(force)
   apply(rename_tac i e ea y list w')(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(force)
  apply(rename_tac i e ea y list w')(*strict*)
  apply(rule setA_set_not)
  apply(rule_tac
      B="cfg_nonterminals G"
      in nset_mp)
   apply(rename_tac i e ea y list w')(*strict*)
   apply(force)
  apply(rename_tac i e ea y list w')(*strict*)
  apply(rule F_FRESH_is_fresh)
  apply(force)
  done

lemma F_CFG_AUGMENT__cfg_nonterminals: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> A \<subseteq> cfg_nonterminals G
  \<Longrightarrow> A \<subseteq> cfg_nonterminals G'"
  apply(simp add: F_CFG_AUGMENT_def)
  apply(force)
  done

lemma F_CFG_AUGMENT__cfg_events2: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> A \<subseteq> cfg_events G
  \<Longrightarrow> A \<subseteq> cfg_events G'"
  apply(simp add: F_CFG_AUGMENT_def)
  apply(force)
  done

lemma F_CFG_AUGMENT__preserves_belongs: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> cfgSTD.belongs G d
  \<Longrightarrow> cfgSTD.belongs G' d"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule cfgSTD.some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule cfgSTD.derivation_belongs)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__preserves_derivation)
       apply(rename_tac c)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac c)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
     apply(rename_tac c)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def)
    apply(rename_tac c)(*strict*)
    apply(simp add: F_CFG_AUGMENT__input_def)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "c \<in> cfg_configurations G")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule cfgSTD.belongs_configurations)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac ca)(*strict*)
  apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
  apply(clarsimp)
  apply(force)
  done

lemma F_CFG_AUGMENT__preserves_belongsRM: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.belongs G d
  \<Longrightarrow> cfgRM.belongs G' d"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule cfgRM.some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule cfgRM.derivation_belongs)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__preserves_RMderivation)
       apply(rename_tac c)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac c)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
     apply(rename_tac c)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def)
    apply(rename_tac c)(*strict*)
    apply(simp add: F_CFG_AUGMENT__input_def)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "c \<in> cfg_configurations G")
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(rule cfgSTD.belongs_configurations)
    apply(rename_tac c)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac ca)(*strict*)
  apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
  apply(clarsimp)
  apply(force)
  done

lemma F_CFG_AUGMENT__derivation_of_input_from_effect_prime: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> cfgRM.belongs G d
  \<Longrightarrow> cfgRM.derivation G d"
  apply(simp (no_asm) add: cfgRM.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(induct_tac i rule: nat_induct)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgRM.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
  apply(rename_tac i n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(case_tac "d(Suc n)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) c1 e2 c2")
   apply(rename_tac n a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 l r)(*strict*)
  apply(simp add: cfgRM.belongs_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(clarsimp)
  apply(simp add: cfg_step_labels_def)
  done

lemma F_CFG_AUGMENT__reflects_derivationRM_hlp: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> d (i + j) = Some (pair e2 \<lparr>cfg_conf = w'\<rparr>)
  \<Longrightarrow> setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G"
  apply(subgoal_tac " \<forall>e2 w'. d (i+j)=Some (pair e2 \<lparr>cfg_conf=w'\<rparr>) \<longrightarrow> (setA w' \<subseteq> cfg_nonterminals G \<and> setB w' \<subseteq> cfg_events G) ")
   apply(clarsimp)
  apply(rule_tac
      m="i"
      and n="j"
      in cfgRM.property_preseved_under_steps_is_invariant2)
      apply(blast)+
     apply(clarsimp)
    apply(arith)
   apply(arith)
  apply(rule allI)
  apply(rename_tac ia)(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(rule allI)+
  apply(rename_tac ia e2a w'nonterminal)(*strict*)
  apply(rule impI)
  apply(subgoal_tac "\<exists>e. Some e=e2a")
   apply(rename_tac ia e2a w'nonterminal)(*strict*)
   prefer 2
   apply(case_tac e2a)
    apply(rename_tac ia e2a w'nonterminal)(*strict*)
    apply(rule cfgRM.derivation_Always_PreEdge_prime)
     apply(rename_tac ia e2a w'nonterminal)(*strict*)
     apply(blast)+
  apply(rename_tac ia e2a w'nonterminal)(*strict*)
  apply(erule exE)+
  apply(rename_tac ia e2a w'nonterminal e)(*strict*)
  apply(subgoal_tac "\<exists>e c. d ia = Some (pair e c)")
   apply(rename_tac ia e2a w'nonterminal e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc ia"
      in cfgRM.pre_some_position_is_some_position)
     apply(rename_tac ia e2a w'nonterminal e)(*strict*)
     apply(blast)
    apply(rename_tac ia e2a w'nonterminal e)(*strict*)
    apply(blast)
   apply(rename_tac ia e2a w'nonterminal e)(*strict*)
   apply(force)
  apply(rename_tac ia e2a w'nonterminal e)(*strict*)
  apply(erule exE)+
  apply(rename_tac ia e2a w'nonterminal e ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac ia e2a w'nonterminal e ea c cfg_conf)(*strict*)
  apply(rename_tac cw)
  apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
  apply(erule_tac
      x="ea"
      in allE)
  apply(erule_tac
      x="cw"
      in allE)
  apply(erule impE)
   apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
   apply(blast)
  apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "cfgRM_step_relation G' \<lparr>cfg_conf = cw\<rparr> e \<lparr>cfg_conf = w'nonterminal\<rparr>")
   apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
   prefer 2
   apply(rule cfgRM.position_change_due_to_step_relation)
     apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
     apply(blast)+
  apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
  apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = cw\<rparr> e \<lparr>cfg_conf = w'nonterminal\<rparr>")
   apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
   prefer 2
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac ia e ea l r)(*strict*)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(clarsimp)
   apply(rename_tac ia ea l r)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac ia ea l r)(*strict*)
    apply(force)
   apply(rename_tac ia ea l r)(*strict*)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> cfg_nonterminals G")
    apply(rename_tac ia ea l r)(*strict*)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac ia ea l r)(*strict*)
     apply(force)
    apply(rename_tac ia ea l r)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac ia ea l r)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
  apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ia e ea l r)(*strict*)
  apply(simp only: setAConcat concat_asso setBConcat)
  apply(simp add: valid_cfg_def)
  done

lemma F_CFG_AUGMENT__reflects_derivationRM: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> cfgRM.derivation G d"
  apply(subgoal_tac "\<forall>i e2 w'. d i = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>) \<longrightarrow> setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G")
   prefer 2
   apply(rule allI)+
   apply(rename_tac i e2 w')(*strict*)
   apply(rule impI)
   apply(rule_tac
      d="d"
      in F_CFG_AUGMENT__reflects_derivationRM_hlp)
           apply(rename_tac i e2 w')(*strict*)
           apply(force)
          apply(rename_tac i e2 w')(*strict*)
          apply(force)
         apply(rename_tac i e2 w')(*strict*)
         apply(force)
        apply(rename_tac i e2 w')(*strict*)
        apply(force)
       apply(rename_tac i e2 w')(*strict*)
       apply(force)
      apply(rename_tac i e2 w')(*strict*)
      apply(force)
     apply(rename_tac i e2 w')(*strict*)
     apply(force)
    apply(rename_tac i e2 w')(*strict*)
    apply(force)
   apply(rename_tac i e2 w')(*strict*)
   apply(force)
  apply(simp add: cfgRM.derivation_def)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(erule_tac
      x="i"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (d 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgRM_step_relation (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) i'2 i1v i2)) (d i'))) (d i)"
      in allE)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(auto)
  apply(rename_tac nat a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(auto)
  apply(rename_tac nat option b)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac nat option b)(*strict*)
   apply(auto)
  apply(rename_tac nat option b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac nat option b a optiona ba)(*strict*)
  apply(auto)
  apply(rename_tac nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac nat option b optiona ba)(*strict*)
   apply(auto)
  apply(rename_tac nat b optiona ba a)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(auto)
  apply(rename_tac nat b optiona ba a l r)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(erule disjE)
   apply(rename_tac nat b optiona ba a l r)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac nat b optiona ba a l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat b optiona ba l r)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac nat b optiona ba l r)(*strict*)
   apply(force)
  apply(rename_tac nat b optiona ba l r)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(case_tac ba)
  apply(rename_tac nat b optiona ba l r cfg_confa)(*strict*)
  apply(auto)
  apply(rename_tac nat b optiona l r)(*strict*)
  apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> cfg_nonterminals G")
   apply(rename_tac nat b optiona l r)(*strict*)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    apply(rename_tac nat b optiona l r)(*strict*)
    apply(force)
   apply(rename_tac nat b optiona l r)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac nat b optiona l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__in_nonterms_of_G: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G'
  \<Longrightarrow> teA S' \<notin> set w
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G"
  apply(simp add: F_CFG_AUGMENT_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> insert (F_FRESH (cfg_nonterminals G)) (cfg_nonterminals G)")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "setA w \<subseteq> insert (F_FRESH (cfg_nonterminals G)) (cfg_nonterminals G)")
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(force)
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a w)(*strict*)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__in_cfg_events_of_G: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> setB w \<subseteq> cfg_events G'
  \<Longrightarrow> teB Do \<notin> set w
  \<Longrightarrow> setB w \<subseteq> cfg_events G"
  apply(simp add: F_CFG_AUGMENT_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> insert (F_FRESH (cfg_events G)) (cfg_events G)")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "setB w \<subseteq> insert (F_FRESH (cfg_events G)) (cfg_events G)")
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(force)
  apply(induct w)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac a w)(*strict*)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w b)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__lang_incl1: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> (\<lambda>w. Do # w @ [Do]) ` cfgSTD.marked_language G \<subseteq> cfgSTD.marked_language G'"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__makes_CFG)
   apply(force)
  apply(simp add: cfgSTD.marked_language_def)
  apply(clarsimp)
  apply(rename_tac w d)(*strict*)
  apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr> \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr> \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) (derivation_map d (\<lambda>v. \<lparr>cfg_conf = teB Do#(cfg_conf v)@[teB Do]\<rparr>)) (Suc 0)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac w d)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac w d)(*strict*)
    apply(rule cfgSTD.derivation_concat2)
       apply(rename_tac w d)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(simp add: cfgSTD_step_relation_def)
       apply(rule conjI)
        apply(rename_tac w d)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
       apply(rename_tac w d)(*strict*)
       apply(rule_tac
      x="[]"
      in exI)
       apply(rule_tac
      x="[]"
      in exI)
       apply(clarsimp)
      apply(rename_tac w d)(*strict*)
      apply(rule der2_maximum_of_domain)
     apply(rename_tac w d)(*strict*)
     apply(rule cfgSTD.derivation_map_preserves_derivation2)
      apply(rename_tac w d)(*strict*)
      apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__preserves_derivation)
          apply(rename_tac w d)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac w d)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac w d)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac w d)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac w d)(*strict*)
      apply(force)
     apply(rename_tac w d)(*strict*)
     apply(clarsimp)
     apply(rename_tac w d a e b)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac w d a e b l r)(*strict*)
     apply(rule_tac
      x="teB Do#l"
      in exI)
     apply(rule_tac
      x="r@[teB Do]"
      in exI)
     apply(clarsimp)
    apply(rename_tac w d)(*strict*)
    apply(simp add: der2_def)
    apply(simp add: derivation_map_def)
    apply(case_tac "d 0")
     apply(rename_tac w d)(*strict*)
     apply(clarsimp)
    apply(rename_tac w d a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac w d a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac w d b)(*strict*)
    apply(simp add: cfg_initial_configurations_def)
   apply(rename_tac w d)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(simp add: cfg_initial_configurations_def)
   apply(case_tac "d 0")
    apply(rename_tac w d)(*strict*)
    apply(clarsimp)
   apply(rename_tac w d a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac w d a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w d b)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(rule cfg_initial_in_nonterms)
   apply(force)
  apply(rename_tac w d)(*strict*)
  apply(rule conjI)
   apply(rename_tac w d)(*strict*)
   apply(simp add: cfg_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac w d e c i)(*strict*)
   apply(case_tac i)
    apply(rename_tac w d e c i)(*strict*)
    apply(clarsimp)
    apply(rename_tac w d e c)(*strict*)
    apply(simp add: cfgSTD.derivation_initial_def)
    apply(clarsimp)
    apply(rename_tac w d c)(*strict*)
    apply(simp add: cfg_initial_configurations_def)
   apply(rename_tac w d e c i nat)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac w d e c nat)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(case_tac "d 0")
    apply(rename_tac w d e c nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac w d e c nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac w d e c nat a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w d e c nat b)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac w d e c nat)(*strict*)
   apply(rule_tac
      x="\<lparr>cfg_conf=teB Do # cfg_conf c @ [teB Do]\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac w d e c nat)(*strict*)
    apply(rule_tac
      x="Suc (Suc nat)"
      in exI)
    apply(simp add: derivation_append_def)
    apply(simp add: derivation_map_def)
   apply(rename_tac w d e c nat)(*strict*)
   apply(simp (no_asm) only: setAConcat concat_asso)
   apply(rule conjI)
    apply(rename_tac w d e c nat)(*strict*)
    apply(force)
   apply(rename_tac w d e c nat)(*strict*)
   apply(rule_tac
      t="cfg_conf c"
      and s="liftB w"
      in ssubst)
    apply(rename_tac w d e c nat)(*strict*)
    apply(force)
   apply(rename_tac w d e c nat)(*strict*)
   apply(rule liftB_commute_one_elem_app)
  apply(rename_tac w d)(*strict*)
  apply(rule conjI)
   apply(rename_tac w d)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
  apply(rename_tac w d)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac w d e c i)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac w d e c i ia ea ca)(*strict*)
  apply(rule_tac
      x="Suc ia"
      in exI)
  apply(rule_tac
      x="ea"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf=teB Do # cfg_conf ca @ [teB Do]\<rparr>"
      in exI)
  apply(simp add: derivation_append_def)
  apply(simp add: derivation_map_def)
  apply(case_tac ia)
   apply(rename_tac w d e c i ia ea ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac w d e c i ea ca)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac w d e c i ca)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac w d e c i)(*strict*)
   apply(simp add: cfg_marking_configuration_def)
  apply(rename_tac w d e c i ia ea ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac w d e c i ea ca nat)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(simp add: cfg_configurations_def)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac w d e c i ea nat cb)(*strict*)
  apply(simp (no_asm) only: setBConcat concat_asso)
  apply(clarsimp)
  apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
  apply(clarsimp)
  apply(rename_tac w d e c i ea nat cb x)(*strict*)
  apply(subgoal_tac "x \<in> cfg_events G")
   apply(rename_tac w d e c i ea nat cb x)(*strict*)
   apply(force)
  apply(rename_tac w d e c i ea nat cb x)(*strict*)
  apply(force)
  done

lemma F_CFG_AUGMENT__lang_incl2: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> (\<lambda>w. Do # w @ [Do]) ` cfgSTD.marked_language G \<supseteq> cfgSTD.marked_language G'"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__makes_CFG)
   apply(force)
  apply(simp add: cfgSTD.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule inMap)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(case_tac "d 0")
   apply(rename_tac x d i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d i e c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e c b)(*strict*)
  apply(case_tac i)
   apply(rename_tac x d i e c b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d c)(*strict*)
   apply(simp add: cfg_marking_configuration_def)
   apply(simp add: cfg_configurations_def)
   apply(simp add: cfg_initial_configurations_def)
  apply(rename_tac x d i e c b nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e c b nat)(*strict*)
  apply(subgoal_tac "\<exists>d. d 0 = Some (pair None b) \<and> x \<in> cfg_marked_effect G' d \<and> d (Suc nat) = Some (pair e c) \<and> cfgSTD.derivation G' d \<and> maximum_of_domain d (Suc nat) ")
   apply(rename_tac x d e c b nat)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d (Suc nat)"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d e c b nat)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac x d e c b nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d e c b nat)(*strict*)
    apply(simp add: cfg_marked_effect_def derivation_take_def)
    apply(clarsimp)
    apply(rename_tac x d e c b nat ea ca i)(*strict*)
    apply(rule_tac
      x="ea"
      in exI)
    apply(rule_tac
      x="ca"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="i"
      in exI)
    apply(clarsimp)
    apply(simp add: cfg_marking_configuration_def)
    apply(clarsimp)
    apply(rule cfgSTD.dead_end_at_some_is_max_dom_prime)
        apply(rename_tac x d e c b nat ea ca i)(*strict*)
        apply(force)
       apply(rename_tac x d e c b nat ea ca i)(*strict*)
       apply(force)
      apply(rename_tac x d e c b nat ea ca i)(*strict*)
      apply(force)
     apply(rename_tac x d e c b nat ea ca i)(*strict*)
     apply(rule cfgSTD_no_step_without_nonterms)
     apply(force)
    apply(rename_tac x d e c b nat ea ca i)(*strict*)
    apply(rule cfgSTD_no_step_without_nonterms)
    apply(force)
   apply(rename_tac x d e c b nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d e c b nat)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac x d e c b nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d e c b nat)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac x d e c b nat)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac x d e c b nat)(*strict*)
  apply(thin_tac "x \<in> cfg_marked_effect G' d")
  apply(thin_tac "cfgSTD.derivation G' d")
  apply(thin_tac "d (Suc nat) = Some (pair e c)")
  apply(thin_tac "d 0 = Some (pair None b)")
  apply(clarsimp)
  apply(rename_tac x e c b nat d)(*strict*)
  apply(subgoal_tac "\<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> d (Suc nat) = Some (pair e \<lparr>cfg_conf=teB Do#w@[teB Do]\<rparr>)")
   apply(rename_tac x e c b nat d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__on_old_grammar_basically)
           apply(rename_tac x e c b nat d)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac x e c b nat d)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac x e c b nat d)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac x e c b nat d)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac x e c b nat d)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac x e c b nat d)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
     apply(rename_tac x e c b nat d)(*strict*)
     apply(simp add: cfg_initial_configurations_def)
     apply(simp add: F_CFG_AUGMENT__input_def)
    apply(rename_tac x e c b nat d)(*strict*)
    apply(force)
   apply(rename_tac x e c b nat d)(*strict*)
   apply(force)
  apply(rename_tac x e c b nat d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x e b nat d w)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac x e b nat d w ea c i)(*strict*)
  apply(subgoal_tac "i=Suc nat")
   apply(rename_tac x e b nat d w ea c i)(*strict*)
   prefer 2
   apply(rule cfgSTD.dead_end_at_some_is_max_dom)
      apply(rename_tac x e b nat d w ea c i)(*strict*)
      apply(force)
     apply(rename_tac x e b nat d w ea c i)(*strict*)
     apply(force)
    apply(rename_tac x e b nat d w ea c i)(*strict*)
    apply(force)
   apply(rename_tac x e b nat d w ea c i)(*strict*)
   apply(rule cfgSTD_no_step_without_nonterms)
   apply(force)
  apply(rename_tac x e b nat d w ea c i)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b nat d w ea)(*strict*)
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   apply(rename_tac x b nat d w ea)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac x b nat d w ea)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac x b nat d w ea)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac x b nat d w ea)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac x b nat d w ea)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac x b nat d w ea)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
     apply(rename_tac x b nat d w ea)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def)
    apply(rename_tac x b nat d w ea)(*strict*)
    apply(simp add: cfg_initial_configurations_def)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(force)
  apply(rename_tac x b nat d w ea)(*strict*)
  apply(rule_tac
      x="filterB w"
      in exI)
  apply(rule conjI)
   apply(rename_tac x b nat d w ea)(*strict*)
   prefer 2
   apply(rule liftB_inj)
   apply(rule_tac
      t="liftB x"
      and s="teB Do # w @ [teB Do]"
      in ssubst)
    apply(rename_tac x b nat d w ea)(*strict*)
    apply(force)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="w@[teB Do]"
      and s="(liftB (filterB w)) @ [teB Do]"
      in ssubst)
    apply(rename_tac x b nat d w ea)(*strict*)
    apply(clarsimp)
    apply(rule sym)
    apply(rule liftBDeConv2)
    apply(simp only: setAConcat concat_asso)
    apply(force)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(rule liftB_commute_one_elem_app)
  apply(rename_tac x b nat d w ea)(*strict*)
  apply(rule_tac
      x="derivation_drop (derivation_map d (\<lambda>c. c\<lparr>cfg_conf:=drop(Suc 0)(butlast(cfg_conf c))\<rparr>)) (Suc 0)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(simp (no_asm_simp) add: cfgSTD.derivation_def)
   apply(clarsimp)
   apply(rename_tac x b nat d w ea i)(*strict*)
   apply(case_tac i)
    apply(rename_tac x b nat d w ea i)(*strict*)
    apply(clarsimp)
    apply(rename_tac x b nat d w ea)(*strict*)
    apply(simp add: derivation_drop_def derivation_map_def)
   apply(rename_tac x b nat d w ea i nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b nat d w ea nata)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
   apply(case_tac "d (Suc (Suc nata))")
    apply(rename_tac x b nat d w ea nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac x b nat d w ea nata a)(*strict*)
   apply(subgoal_tac "\<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> d (Suc (Suc nata)) = Some (pair e \<lparr>cfg_conf=teB Do#w@[teB Do]\<rparr>)")
    apply(rename_tac x b nat d w ea nata a)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__on_old_grammar_basically)
            apply(rename_tac x b nat d w ea nata a)(*strict*)
            apply(simp add: F_CFG_AUGMENT__input_def)
           apply(rename_tac x b nat d w ea nata a)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac x b nat d w ea nata a)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac x b nat d w ea nata a)(*strict*)
         apply(force)
        apply(rename_tac x b nat d w ea nata a)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac x b nat d w ea nata a)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac x b nat d w ea nata a)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
      apply(simp add: cfg_initial_configurations_def)
     apply(rename_tac x b nat d w ea nata a)(*strict*)
     apply(force)
    apply(rename_tac x b nat d w ea nata a)(*strict*)
    apply(force)
   apply(rename_tac x b nat d w ea nata a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b nat d w ea nata e wa)(*strict*)
   apply(case_tac "d (Suc nata)")
    apply(rename_tac x b nat d w ea nata e wa)(*strict*)
    apply(rule_tac
      n="Suc nata"
      in cfgSTD.derivationNoFromNone)
      apply(rename_tac x b nat d w ea nata e wa)(*strict*)
      apply(force)
     apply(rename_tac x b nat d w ea nata e wa)(*strict*)
     apply(force)
    apply(rename_tac x b nat d w ea nata e wa)(*strict*)
    apply(force)
   apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
   apply(subgoal_tac "\<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> d (Suc nata) = Some (pair e \<lparr>cfg_conf=teB Do#w@[teB Do]\<rparr>)")
    apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__on_old_grammar_basically)
            apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
            apply(simp add: F_CFG_AUGMENT__input_def)
           apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
         apply(force)
        apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
      apply(simp add: cfg_initial_configurations_def)
      apply(simp add: F_CFG_AUGMENT__input_def)
     apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def)
    apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
    apply(force)
   apply(rename_tac x b nat d w ea nata e wa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
   apply(subgoal_tac "Suc (Suc nata) \<le> Suc nat")
    apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
    prefer 2
    apply(rule cfgSTD.allPreMaxDomSome_prime)
      apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
      apply(force)
     apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
     apply(force)
    apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
    apply(force)
   apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc (Suc nata)) = Some (pair (Some e) c)")
    apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
    prefer 2
    apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
      apply(blast)
     apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
     apply(blast)
    apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
    apply(arith)
   apply(rename_tac x b nat d w ea nata e wa eb wb)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b nat d w ea nata wa eb wb ec)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = wb\<rparr> ec \<lparr>cfg_conf = wa\<rparr>")
    apply(rename_tac x b nat d w ea nata wa eb wb ec)(*strict*)
    apply(force)
   apply(rename_tac x b nat d w ea nata wa eb wb ec)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G' \<lparr>cfg_conf = teB Do # wb @ [teB Do]\<rparr> ec \<lparr>cfg_conf = teB Do # wa @ [teB Do]\<rparr>")
    apply(rename_tac x b nat d w ea nata wa eb wb ec)(*strict*)
    prefer 2
    apply(rule_tac
      n="Suc nata"
      in cfgSTD.position_change_due_to_step_relation)
      apply(rename_tac x b nat d w ea nata wa eb wb ec)(*strict*)
      apply(blast)
     apply(rename_tac x b nat d w ea nata wa eb wb ec)(*strict*)
     apply(blast)
    apply(rename_tac x b nat d w ea nata wa eb wb ec)(*strict*)
    apply(blast)
   apply(rename_tac x b nat d w ea nata wa eb wb ec)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x b nat d w ea nata wa eb wb ec l r)(*strict*)
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
   apply(clarsimp)
   apply(case_tac l)
    apply(rename_tac x b nat d w ea nata wa eb wb ec l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac x b nat d w ea nata wa eb wb ec l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b nat d w ea nata wa eb wb ec r list)(*strict*)
   apply(case_tac r)
    apply(rename_tac x b nat d w ea nata wa eb wb ec r list)(*strict*)
    apply(clarsimp)
   apply(rename_tac x b nat d w ea nata wa eb wb ec r list a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
    apply(rename_tac x b nat d w ea nata wa eb wb ec r list a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x b nat d w ea nata wa eb wb ec r list a lista)(*strict*)
   apply(thin_tac "r=a#lista")
   apply(clarsimp)
   apply(rename_tac x b nat d w ea nata eb ec list w')(*strict*)
   apply(rule conjI)
    apply(rename_tac x b nat d w ea nata eb ec list w')(*strict*)
    apply(clarsimp)
   apply(rename_tac x b nat d w ea nata eb ec list w')(*strict*)
   apply(rule_tac
      x="list"
      in exI)
   apply(rule_tac
      x="w'"
      in exI)
   apply(clarsimp)
  apply(rename_tac x b nat d w ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac x nat d w ea)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(rule cfg_initial_in_nonterms)
   apply(simp add: F_CFG_AUGMENT__input_def)
  apply(rename_tac x b nat d w ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(rule_tac
      x="if nat=0 then None else ea"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x b nat d w ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x b nat d w ea)(*strict*)
    apply(rule_tac
      x="nat"
      in exI)
    apply(simp add: derivation_drop_def derivation_map_def)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(rule conjI)
    apply(rename_tac x b nat d w ea)(*strict*)
    apply(force)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac x b nat d w ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x b nat d w ea)(*strict*)
   apply(simp add: derivation_drop_def derivation_map_def)
  apply(rename_tac x b nat d w ea)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac x nat d w ea)(*strict*)
  apply(rule_tac
      x="nat"
      in exI)
  apply(rule_tac
      x="if nat =0 then None else ea"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in exI)
  apply(simp add: derivation_drop_def derivation_map_def)
  apply(subgoal_tac "\<lparr>cfg_conf = w\<rparr> \<in> cfg_marking_configuration G")
   apply(rename_tac x nat d w ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac x nat d w ea)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(simp only: setAConcat concat_asso)
  apply(simp only: setBConcat concat_asso)
  apply(rule conjI)
   apply(rename_tac x nat d w ea)(*strict*)
   apply(force)
  apply(rename_tac x nat d w ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac x nat d w ea)(*strict*)
   apply(force)
  apply(rename_tac x nat d w ea)(*strict*)
  apply(subgoal_tac "Do \<notin> setB w")
   apply(rename_tac x nat d w ea)(*strict*)
   apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
   apply(force)
  apply(rename_tac x nat d w ea)(*strict*)
  apply(rule not_in_setBI)
  apply(force)
  done

theorem F_CFG_AUGMENT__lang: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> (\<lambda>w. Do # w @ [Do]) ` cfgSTD.marked_language G = cfgSTD.marked_language G'"
  apply(rule order_antisym)
   apply(rule F_CFG_AUGMENT__lang_incl1)
   apply(force)
  apply(rule F_CFG_AUGMENT__lang_incl2)
  apply(force)
  done

lemma F_CFG_AUGMENT__lang_prime: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> (\<lambda>w. Do # w @ [Do]) w \<in> cfgSTD.marked_language G'
  \<Longrightarrow> w \<in> cfgSTD.marked_language G"
  apply(subgoal_tac "(\<lambda>w. Do#w@[Do]) w \<in> ((\<lambda>w. Do#w@[ Do]) ` cfgSTD.marked_language G)")
   prefer 2
   apply(rule_tac
      s="cfgSTD.marked_language G'"
      and t="(\<lambda>w. Do#w@[Do]) ` cfgSTD.marked_language G"
      in ssubst)
    apply(rule F_CFG_AUGMENT__lang)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_CFG_AUGMENT__derivation_of_input_from_effect: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> cfgRM.belongs G' d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> set (cfg_conf c) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> cfgRM.belongs G d"
  apply(simp (no_asm) add: cfgRM.belongs_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(induct_tac i rule: nat_induct)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfg_configurations_def)
   apply(case_tac c)
   apply(rename_tac cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac cfg_conf)(*strict*)
   apply(rule conjI)
    apply(rename_tac cfg_conf)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(force)
   apply(rename_tac cfg_conf)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(force)
  apply(rename_tac i n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rename_tac n)
  apply(case_tac "d(Suc n)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) c1 e2 c2")
   apply(rename_tac n a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 l r)(*strict*)
  apply(simp add: cfg_step_labels_def cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac n e1 e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 l r)(*strict*)
  apply(simp only: setBConcat setAConcat concat_asso)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac n e1 e2 l r)(*strict*)
   prefer 2
   apply(simp add: valid_cfg_def)
  apply(rename_tac n e1 e2 l r)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(clarsimp)
  apply(rename_tac n e1 l r)(*strict*)
  apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
   apply(rename_tac n e1 l r)(*strict*)
   apply(force)
  apply(rename_tac n e1 l r)(*strict*)
  apply(rule F_FRESH_is_fresh)
  apply(simp add: valid_cfg_def)
  done

theorem F_CFG_AUGMENT__preserves_Nonblockingness: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> valid_cfg G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G'"
  apply(rule_tac
      GL="G"
      and R="{(\<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>,\<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>)}\<union>{(\<lparr>cfg_conf=wl\<rparr>,\<lparr>cfg_conf=wr\<rparr>)| wl wr. wr=[teB Do]@wl@[teB Do] \<and> set wl \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) }"
      in cfgRM_cfgRM_ATS_Bisimulation_Configuration_Weak.preserve_Nonblockingness)
        apply(force)
       apply(rule F_CFG_AUGMENT__makes_CFG)
       apply(force)
      apply(simp add: F_CFG_AUGMENT__input_def)
      prefer 5
      apply(force)
     apply(simp add: cfgRM_cfgRM_ATS_Bisimulation_Configuration_Weak.bisimulation_initial_def)
     apply(clarsimp)
     apply(rename_tac i2)(*strict*)
     apply(simp add: cfg_initial_configurations_def)
     apply(simp add: cfg_configurations_def)
     apply(clarsimp)
     apply(rule cfg_initial_in_nonterms)
     apply(force)
    apply(simp add: cfgRM_cfgRM_ATS_Bisimulation_Configuration_Weak.bisimulation_preserves_steps1_def)
    apply(rule conjI)
     apply(clarsimp)
     apply(rename_tac e2 s2')(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac e2 s2' l r)(*strict*)
     apply(case_tac l)
      apply(rename_tac e2 s2' l r)(*strict*)
      prefer 2
      apply(rename_tac e2 s2' l r a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac e2 s2' l r)(*strict*)
     apply(clarsimp)
     apply(rename_tac e2 s2')(*strict*)
     apply(rule_tac
      x="\<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in exI)
     apply(rule conjI)
      apply(rename_tac e2 s2')(*strict*)
      apply(rule cfgRM.der1_is_derivation)
     apply(rename_tac e2 s2')(*strict*)
     apply(rule_tac
      x="0"
      in exI)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac e2 s2')(*strict*)
      apply(rule der1_maximum_of_domain)
     apply(rename_tac e2 s2')(*strict*)
     apply(rule conjI)
      apply(rename_tac e2 s2')(*strict*)
      apply(simp add: get_configuration_def der1_def)
     apply(rename_tac e2 s2')(*strict*)
     apply(case_tac s2')
     apply(rename_tac e2 s2' cfg_confa)(*strict*)
     apply(clarsimp)
     apply(rename_tac e2)(*strict*)
     apply(case_tac e2)
     apply(rename_tac e2 prod_lhsa prod_rhsa)(*strict*)
     apply(clarsimp)
     apply(rename_tac prod_rhs)(*strict*)
     apply(rename_tac w)
     apply(rename_tac w)(*strict*)
     apply(erule impE)
      apply(rename_tac w)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
      apply(erule disjE)
       apply(rename_tac w)(*strict*)
       apply(clarsimp)
      apply(rename_tac w)(*strict*)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = w\<rparr>"
      in ballE)
       apply(rename_tac w)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac w)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
       apply(rename_tac w)(*strict*)
       apply(force)
      apply(rename_tac w)(*strict*)
      apply(rule F_FRESH_is_fresh)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(simp add: two_elements_construct_domain_def)
     apply(clarsimp)
     apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(rename_tac wl e2 s2')(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac wl e2 s2' l r)(*strict*)
    apply(case_tac l)
     apply(rename_tac wl e2 s2' l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac wl e2 s2' l r a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac wl e2 s2' r list)(*strict*)
    apply(case_tac r)
     apply(rename_tac wl e2 s2' r list)(*strict*)
     apply(clarsimp)
    apply(rename_tac wl e2 s2' r list a lista)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
     apply(rename_tac wl e2 s2' r list a lista)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac wl e2 s2' r list a lista)(*strict*)
    apply(thin_tac "r=a#lista")
    apply(clarsimp)
    apply(rename_tac e2 s2' list w')(*strict*)
    apply(rename_tac wl wr)
    apply(rename_tac e2 s2' wl wr)(*strict*)
    apply(case_tac s2')
    apply(rename_tac e2 s2' wl wr cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 wl wr)(*strict*)
    apply(rule_tac
      x="\<lparr>cfg_conf = wl @ prod_rhs e2 @ wr\<rparr>"
      in exI)
    apply(rule_tac
      x="der2 \<lparr>cfg_conf = wl @ teA (prod_lhs e2) # wr\<rparr> e2 \<lparr>cfg_conf = wl @ (prod_rhs e2) @ wr\<rparr>"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "e2 \<in> cfg_productions G")
     apply(rename_tac e2 wl wr)(*strict*)
     prefer 2
     apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
     apply(erule disjE)
      apply(rename_tac e2 wl wr)(*strict*)
      apply(clarsimp)
      apply(rename_tac wl wr)(*strict*)
      apply(simp add: two_elements_construct_domain_def)
      apply(erule disjE)
       apply(rename_tac wl wr)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
        apply(rename_tac wl wr)(*strict*)
        apply(force)
       apply(rename_tac wl wr)(*strict*)
       apply(rule F_FRESH_is_fresh)
       apply(simp add: valid_cfg_def)
      apply(rename_tac wl wr)(*strict*)
      apply(clarsimp)
     apply(rename_tac e2 wl wr)(*strict*)
     apply(clarsimp)
    apply(rename_tac e2 wl wr)(*strict*)
    apply(rule conjI)
     apply(rename_tac e2 wl wr)(*strict*)
     apply(rule cfgRM.der2_is_derivation)
     apply(simp add: cfgRM_step_relation_def)
     apply(rule_tac
      x="wl"
      in exI)
     apply(rule_tac
      x="wr"
      in exI)
     apply(clarsimp)
     apply(simp only: setAConcat concat_asso)
     apply(force)
    apply(rename_tac e2 wl wr)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule conjI)
     apply(rename_tac e2 wl wr)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac e2 wl wr)(*strict*)
    apply(simp add: get_configuration_def der2_def)
    apply(case_tac e2)
    apply(rename_tac e2 wl wr prod_lhsa prod_rhsa)(*strict*)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(rename_tac e2 wl wr prod_lhsa prod_rhsa)(*strict*)
     apply(rule prod_rhs_in_cfg_events)
      apply(rename_tac e2 wl wr prod_lhsa prod_rhs)(*strict*)
      apply(force)
     apply(rename_tac e2 wl wr prod_lhsa prod_rhsa)(*strict*)
     apply(force)
    apply(rename_tac e2 wl wr prod_lhsa prod_rhsa)(*strict*)
    apply(rule prod_rhs_in_nonterms)
     apply(rename_tac e2 wl wr prod_lhsa prod_rhs)(*strict*)
     apply(force)
    apply(rename_tac e2 wl wr prod_lhsa prod_rhsa)(*strict*)
    apply(force)
   apply(subgoal_tac "valid_cfg G'")
    prefer 2
    apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__makes_CFG)
    apply(force)
   apply(simp add: cfgRM_cfgRM_ATS_Bisimulation_Configuration_Weak.bisimulation_preserves_steps2_def)
   apply(rule conjI)
    apply(clarsimp)
    apply(rename_tac e1 s1')(*strict*)
    apply(case_tac s1')
    apply(rename_tac e1 s1' cfg_conf)(*strict*)
    apply(clarsimp)
    apply(rename_tac e1 cfg_conf)(*strict*)
    apply(rename_tac w)
    apply(rename_tac e1 w)(*strict*)
    apply(rule_tac
      x="\<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="der3 \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr> \<lparr>prod_lhs=cfg_initial G',prod_rhs= teB Do # [teA (cfg_initial G)] @ [teB Do]\<rparr> \<lparr>cfg_conf = teB Do # [teA (cfg_initial G)] @ [teB Do]\<rparr> e1 \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>"
      in exI)
    apply(rename_tac e1 w)(*strict*)
    apply(rule conjI)
     apply(rename_tac e1 w)(*strict*)
     apply(rule cfgRM.der3_is_derivation)
       apply(rename_tac e1 w)(*strict*)
       apply(force)
      apply(rename_tac e1 w)(*strict*)
      apply(simp add: cfgRM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac e1 l r)(*strict*)
      apply(rule conjI)
       apply(rename_tac e1 l r)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
       apply(simp add: F_CFG_AUGMENT_def)
      apply(rename_tac e1 l r)(*strict*)
      apply(rule_tac
      x="[]"
      in exI)
      apply(rule_tac
      x="[]"
      in exI)
      apply(clarsimp)
     apply(rename_tac e1 w)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac e1 l r)(*strict*)
     apply(case_tac l)
      apply(rename_tac e1 l r)(*strict*)
      prefer 2
      apply(rename_tac e1 l r a list)(*strict*)
      apply(force)
     apply(rename_tac e1 l r)(*strict*)
     apply(clarsimp)
     apply(rename_tac e1)(*strict*)
     apply(rule conjI)
      apply(rename_tac e1)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(rename_tac e1)(*strict*)
     apply(rule_tac
      x="[teB Do]"
      in exI)
     apply(rule_tac
      x="[teB Do]"
      in exI)
     apply(clarsimp)
    apply(rename_tac e1 w)(*strict*)
    apply(rule_tac
      x="Suc (Suc 0)"
      in exI)
    apply(rule conjI)
     apply(rename_tac e1 w)(*strict*)
     apply(rule der3_maximum_of_domain)
    apply(rename_tac e1 w)(*strict*)
    apply(simp add: get_configuration_def der3_def)
    apply(simp add: cfgRM_step_relation_def)
    apply(erule conjE)
    apply(erule exE)+
    apply(rename_tac e1 w l r)(*strict*)
    apply(erule conjE)+
    apply(case_tac l)
     apply(rename_tac e1 w l r)(*strict*)
     prefer 2
     apply(rename_tac e1 w l r a list)(*strict*)
     apply(force)
    apply(rename_tac e1 w l r)(*strict*)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(rename_tac e1 w l r)(*strict*)
     apply(case_tac e1)
     apply(rename_tac e1 w l r prod_lhsa prod_rhsa)(*strict*)
     apply(rule_tac
      t="w"
      and s="prod_rhs e1"
      in ssubst)
      apply(rename_tac e1 w l r prod_lhsa prod_rhsa)(*strict*)
      apply(force)
     apply(rename_tac e1 w l r prod_lhsa prod_rhsa)(*strict*)
     apply(rule prod_rhs_in_cfg_events)
      apply(rename_tac e1 w l r prod_lhsa prod_rhsa)(*strict*)
      apply(force)
     apply(rename_tac e1 w l r prod_lhsa prod_rhsa)(*strict*)
     apply(force)
    apply(rename_tac e1 w l r)(*strict*)
    apply(case_tac e1)
    apply(rename_tac e1 w l r prod_lhsa prod_rhsa)(*strict*)
    apply(rule prod_rhs_in_nonterms)
     apply(rename_tac e1 w l r prod_lhsa prod_rhsa)(*strict*)
     apply(force)
    apply(rename_tac e1 w l r prod_lhsa prod_rhsa)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(rename_tac wl e1 s1')(*strict*)
   apply(case_tac s1')
   apply(rename_tac wl e1 s1' cfg_conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac wl e1 cfg_conf)(*strict*)
   apply(rename_tac w)
   apply(rename_tac wl e1 w)(*strict*)
   apply(rule_tac
      x="\<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="der2 \<lparr>cfg_conf = teB Do # wl @ [teB Do]\<rparr> e1 \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac wl e1 w)(*strict*)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac e1 l r)(*strict*)
    apply(rule conjI)
     apply(rename_tac e1 l r)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def)
     apply(simp add: F_CFG_AUGMENT_def)
    apply(rename_tac e1 l r)(*strict*)
    apply(rule_tac
      x="[teB Do]@l"
      in exI)
    apply(rule_tac
      x="r@[teB Do]"
      in exI)
    apply(clarsimp)
    apply(simp only: setAConcat concat_asso)
    apply(clarsimp)
   apply(rename_tac wl e1 w)(*strict*)
   apply(rule_tac
      x="Suc 0"
      in exI)
   apply(rule conjI)
    apply(rename_tac wl e1 w)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac wl e1 w)(*strict*)
   apply(simp add: get_configuration_def der2_def)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e1 x l r)(*strict*)
   apply(erule disjE)
    apply(rename_tac e1 x l r)(*strict*)
    apply(force)
   apply(rename_tac e1 x l r)(*strict*)
   apply(erule disjE)
    apply(rename_tac e1 x l r)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e1 x l r)(*strict*)
   apply(rule_tac
      A="set (prod_rhs e1)"
      in set_mp)
    apply(rename_tac e1 x l r)(*strict*)
    apply(case_tac e1)
    apply(rename_tac e1 x l r prod_lhsa prod_rhsa)(*strict*)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(rename_tac e1 x l r prod_lhsa prod_rhsa)(*strict*)
     apply(rule prod_rhs_in_cfg_events)
      apply(rename_tac e1 x l r prod_lhsa prod_rhsa)(*strict*)
      apply(force)
     apply(rename_tac e1 x l r prod_lhsa prod_rhsa)(*strict*)
     apply(force)
    apply(rename_tac e1 x l r prod_lhsa prod_rhsa)(*strict*)
    apply(rule prod_rhs_in_nonterms)
     apply(rename_tac e1 x l r prod_lhsa prod_rhsa)(*strict*)
     apply(force)
    apply(rename_tac e1 x l r prod_lhsa prod_rhsa)(*strict*)
    apply(force)
   apply(rename_tac e1 x l r)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(simp add: cfgRM_cfgRM_ATS_Bisimulation_Configuration_Weak.bisimulation_preserves_marking_condition_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac dh n dha na)(*strict*)
   apply(simp add: cfg_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac dh n dha na i e c)(*strict*)
   apply(rule_tac
      x="na"
      in exI)
   apply(subgoal_tac "\<exists>e c. dha na = Some (pair e c)")
    apply(rename_tac dh n dha na i e c)(*strict*)
    prefer 2
    apply(simp add: maximum_of_domain_def)
    apply(clarsimp)
    apply(rename_tac dh n dha na i e c y ya)(*strict*)
    apply(case_tac ya)
    apply(rename_tac dh n dha na i e c y ya option b)(*strict*)
    apply(force)
   apply(rename_tac dh n dha na i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dha na i e c ea ca)(*strict*)
   apply(simp add: cfg_marking_configuration_def cfg_configurations_def)
   apply(clarsimp)
   apply(rename_tac dh n dha na i e ea ca cb)(*strict*)
   apply(case_tac ca)
   apply(rename_tac dh n dha na i e ea ca cb cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dha na i e ea cb cfg_conf)(*strict*)
   apply(rename_tac w)
   apply(rename_tac dh n dha na i e ea cb w)(*strict*)
   apply(simp add: derivation_append_fit_def der1_def)
   apply(clarsimp)
   apply(rename_tac dh n dha na i e ea cb)(*strict*)
   apply(case_tac "dh n")
    apply(rename_tac dh n dha na i e ea cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dha na i e ea cb a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n dha na i e ea cb a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dha na i e ea cb option)(*strict*)
   apply(subgoal_tac "i=n")
    apply(rename_tac dh n dha na i e ea cb option)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dha na i e ea cb option)(*strict*)
   apply(rule cfgRM.maximum_of_domainUnique)
     apply(rename_tac dh n dha na i e ea cb option)(*strict*)
     apply(force)
    apply(rename_tac dh n dha na i e ea cb option)(*strict*)
    apply(force)
   apply(rename_tac dh n dha na i e ea cb option)(*strict*)
   apply(simp add: maximum_of_domain_def)
   apply(rule cfgRM_no_step_without_nonterms)
      apply(rename_tac dh n dha na i e ea cb option)(*strict*)
      apply(force)
     apply(rename_tac dh n dha na i e ea cb option)(*strict*)
     apply(force)
    apply(rename_tac dh n dha na i e ea cb option)(*strict*)
    apply(force)
   apply(rename_tac dh n dha na i e ea cb option)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac wl dh n dha na)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac wl dh n dha na i e c)(*strict*)
  apply(simp add: cfg_marking_configuration_def cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac wl dh n dha na i e ca)(*strict*)
  apply(rule_tac
      x="na"
      in exI)
  apply(subgoal_tac "\<exists>e c. dha na = Some (pair e c)")
   apply(rename_tac wl dh n dha na i e ca)(*strict*)
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac wl dh n dha na i e ca y ya)(*strict*)
   apply(case_tac ya)
   apply(rename_tac wl dh n dha na i e ca y ya option b)(*strict*)
   apply(force)
  apply(rename_tac wl dh n dha na i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac wl dh n dha na i e ca ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac wl dh n dha na i e ca ea c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac wl dh n dha na i e ca ea cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac wl dh n dha na i e ca ea w)(*strict*)
  apply(simp add: derivation_append_fit_def der1_def)
  apply(clarsimp)
  apply(rename_tac wl dh n dha na i e ca ea)(*strict*)
  apply(case_tac "dh n")
   apply(rename_tac wl dh n dha na i e ca ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac wl dh n dha na i e ca ea a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac wl dh n dha na i e ca ea a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
  apply(subgoal_tac "i=n")
   apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
   prefer 2
   apply(rule cfgRM.maximum_of_domainUnique)
     apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
     apply(force)
    apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
    apply(force)
   apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
   apply(simp add: maximum_of_domain_def)
   apply(rule cfgRM_no_step_without_nonterms)
      apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
      apply(force)
     apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
     apply(force)
    apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
    apply(force)
   apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
   apply(force)
  apply(rename_tac wl dh n dha na i e ca ea option)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dha na e ca ea)(*strict*)
  apply(simp only: setBConcat setAConcat concat_asso)
  apply(clarsimp)
  apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
  apply(clarsimp)
  apply(rename_tac dh n dha na e ca ea x)(*strict*)
  apply(force)
  done

lemma F_CFG_AUGMENT__reachableConf_of_certain_form: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> cfgSTD.derivation_initial G' d
  \<Longrightarrow> d (Suc i) = Some (pair e c)
  \<Longrightarrow> \<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf c = [teB Do] @ w @ [teB Do]"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
   apply(force)
  apply(induct i arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
    apply(rename_tac e c)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac e c)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac e c)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac e c)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac e c)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac e c)(*strict*)
       apply(force)
      apply(rename_tac e c)(*strict*)
      apply(rule cfgSTD.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac e c)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def cfg_initial_configurations_def)
     apply(clarsimp)
     apply(case_tac "d 0")
      apply(rename_tac e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac e c a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac e c a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac e c b)(*strict*)
     apply(simp add: cfg_initial_configurations_def)
    apply(rename_tac e c)(*strict*)
    apply(force)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(simp add: F_CFG_AUGMENT__input_def)
   apply(simp add: two_elements_construct_domain_def valid_cfg_def)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (Suc i) = Some (pair e1 c1) \<and> d (Suc (Suc i)) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation G' c1 e2 c2")
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (Suc i)"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac i e c)(*strict*)
     apply(rule cfgSTD.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac i c e1 e2 c1 w l r)(*strict*)
   apply(force)
  apply(rename_tac i c e1 e2 c1 w l r a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w r list)(*strict*)
  apply(case_tac r)
   apply(rename_tac i c e1 e2 c1 w r list)(*strict*)
   apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 w r list a lista)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
   apply(rename_tac i c e1 e2 c1 w r list a lista)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac i c e1 e2 c1 w r list a lista)(*strict*)
  apply(thin_tac "r=a#lista")
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
  apply(subgoal_tac "e2 \<in> cfg_productions G")
   apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
   apply(simp add: valid_cfg_def F_CFG_AUGMENT__input_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(erule_tac
      x="e2"
      and P="\<lambda>e2. prod_lhs e2 \<in> cfg_nonterminals G \<and> setA (prod_rhs e2) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs e2) \<subseteq> cfg_events G"
      in ballE)
    apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
   apply(clarsimp)
   apply(case_tac x)
    apply(rename_tac i c e1 e2 c1 list w' x a)(*strict*)
    apply(clarsimp)
    apply(rename_tac i c e1 e2 c1 list w' a)(*strict*)
    apply(rule inMap)
    apply(clarsimp)
    apply(rule_tac
      A="setA (prod_rhs e2)"
      in set_mp)
     apply(rename_tac i c e1 e2 c1 list w' a)(*strict*)
     apply(force)
    apply(rename_tac i c e1 e2 c1 list w' a)(*strict*)
    apply(rule set_setA)
    apply(force)
   apply(rename_tac i c e1 e2 c1 list w' x b)(*strict*)
   apply(clarsimp)
   apply(rename_tac i c e1 e2 c1 list w' b)(*strict*)
   apply(subgoal_tac "teB b \<in> teB ` cfg_events G")
    apply(rename_tac i c e1 e2 c1 list w' b)(*strict*)
    apply(force)
   apply(rename_tac i c e1 e2 c1 list w' b)(*strict*)
   apply(rule inMap)
   apply(clarsimp)
   apply(rule_tac
      A="setB (prod_rhs e2)"
      in set_mp)
    apply(rename_tac i c e1 e2 c1 list w' b)(*strict*)
    apply(force)
   apply(rename_tac i c e1 e2 c1 list w' b)(*strict*)
   apply(rule set_setB)
   apply(force)
  apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
  apply(subgoal_tac "prod_lhs e2 \<in> cfg_nonterminals G")
   apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
   apply(subgoal_tac "e2 \<in> cfg_productions G'")
    apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
    apply(simp add: F_CFG_AUGMENT__input_def)
    apply(clarsimp)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac i c e1 c1 list w' x)(*strict*)
    apply(case_tac c1)
    apply(rename_tac i c e1 c1 list w' x cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i c e1 list w' x)(*strict*)
    apply(case_tac c)
    apply(rename_tac i c e1 list w' x cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e1 list w' x)(*strict*)
    apply(simp add: two_elements_construct_domain_def)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac i e1 list w' x)(*strict*)
     apply(force)
    apply(rename_tac i e1 list w' x)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: F_CFG_AUGMENT__input_def valid_cfg_def)
   apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
   apply(rule_tac
      t="cfg_productions G'"
      and s="cfg_step_labels G'"
      in ssubst)
    apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
    apply(simp add: cfg_step_labels_def)
   apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
   apply(rule cfgSTD.belongs_step_labels)
    apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
    apply(rule cfgSTD.derivation_initial_belongs)
     apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
     apply(force)
    apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
    apply(force)
   apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
   apply(force)
  apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
  apply(simp add: two_elements_construct_domain_def)
  apply(erule disjE)
   apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
   apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 list w' x)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__prod_subset: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfg_productions G \<subseteq> cfg_productions G'"
  apply(simp add: F_CFG_AUGMENT_def)
  apply(force)
  done

end

