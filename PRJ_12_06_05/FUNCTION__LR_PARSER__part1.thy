section {*FUNCTION\_\_LR\_PARSER\_\_part1*}
theory
  FUNCTION__LR_PARSER__part1

imports
  PRJ_12_06_05__ENTRY

begin

definition AF_LR_PARSER__rules :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda
  \<Rightarrow> nat
  \<Rightarrow> ((('nonterminal, 'event) DT_cfg_item set, 'event) parser_step_label \<times> ('nonterminal, 'event) cfg_step_label option) set"
  where
    "AF_LR_PARSER__rules G G' M k \<equiv>
  {(\<lparr>rule_lpop = q # q_seq,
      rule_rpop = y,
      rule_lpush = [q, qA],
      rule_rpush = y\<rparr>,
      Some \<lparr>prod_lhs = cfg_item_lhs I,
            prod_rhs = (cfg_item_rhs1 I) @ (cfg_item_rhs2 I)\<rparr>)
      | q q_seq I y qA.
        q \<in> epda_states M
        \<and> I \<in> q
        \<and> \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G
        \<and> cfg_item_rhs1 I = []
        \<and> qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))
        \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I))
        \<and> \<lparr>cfg_item_lhs = cfg_item_lhs I,
            cfg_item_rhs1 = cfg_item_rhs2 I,
            cfg_item_rhs2 = [],
            cfg_item_look_ahead = y\<rparr> \<in> last (q # q_seq)}
  \<union>
  {(\<lparr>rule_lpop = [q],
      rule_rpop = a # y,
      rule_lpush = [q, qA],
      rule_rpush = y\<rparr>,
      None)
      | q a y qA.
      q \<in> epda_states M
      \<and> (\<exists>I \<in> q.
          \<lparr>prod_lhs = cfg_item_lhs I,
            prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> \<in> cfg_productions G
          \<and> [teB a] = take (Suc 0) (cfg_item_rhs2 I)
          \<and> qA \<in> F_EPDA_GOTO M q (teB a)
          \<and> y \<in> cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I)))}"

definition AF_LR_PARSER :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda
  \<Rightarrow> nat
  \<Rightarrow> 'event
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, 'event, ((('nonterminal, 'event) cfg_step_label option) option)) parser"
  where
    "AF_LR_PARSER G G' M k Do \<equiv>
  \<lparr>parser_nonterms =
    epda_states M
    - {epda_initial M,
      last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]),
      F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))},
  parser_events = cfg_events G',
  parser_initial = F_DFA_GOTO M (epda_initial M) (teB Do),
  parser_marking = {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])},
  parser_rules = (\<lambda>(x,y). x) ` AF_LR_PARSER__rules G G' M k,
  parser_marker =
    \<lambda>x.
      if \<exists>! y. (x, y) \<in> AF_LR_PARSER__rules G G' M k
      then Some (THE y. (x, y) \<in> AF_LR_PARSER__rules G G' M k)
      else None,
  parser_bottom = Do\<rparr>"

lemma X6_3_InformationOnRules_UniqueEffect: "
  valid_cfg (G :: ('nonterminal DT_symbol, 'event DT_symbol) cfg)
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> r \<in> parser_rules P
  \<Longrightarrow> \<exists>!y. (r, y) \<in> AF_LR_PARSER__rules G G' M k"
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
  apply(rule HOL.ex_ex1I)
   apply(subgoal_tac "r \<in> (\<lambda>(x, y). x) ` AF_LR_PARSER__rules G G' M k")
    prefer 2
    apply(simp add: AF_LR_PARSER_def)
   apply(subgoal_tac "\<exists>y \<in> AF_LR_PARSER__rules G G' M k. (\<lambda>(x, y). x) y = r")
    prefer 2
    apply(rule inMap_rev)
    apply(clarsimp)
   apply(force)
  apply(rename_tac y ya)(*strict*)
  apply(case_tac y)
   apply(rename_tac y ya)(*strict*)
   apply(subgoal_tac "length (rule_rpop r) > length (rule_rpush r)")
    apply(rename_tac y ya)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER__rules_def)
    apply(clarsimp)
   apply(rename_tac y ya)(*strict*)
   apply(case_tac ya)
    apply(rename_tac y ya)(*strict*)
    apply(force)
   apply(rename_tac y ya a)(*strict*)
   apply(subgoal_tac "length (rule_rpop r) = length (rule_rpush r)")
    apply(rename_tac y ya a)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER__rules_def)
    apply(clarsimp)
   apply(rename_tac y ya a)(*strict*)
   apply(force)
  apply(rename_tac y ya a)(*strict*)
  apply(case_tac ya)
   apply(rename_tac y ya a)(*strict*)
   apply(subgoal_tac "length (rule_rpop r) = length (rule_rpush r)")
    apply(rename_tac y ya a)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER__rules_def)
    apply(clarsimp)
   apply(rename_tac y ya a)(*strict*)
   apply(subgoal_tac "length (rule_rpop r) > length (rule_rpush r)")
    apply(rename_tac y ya a)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER__rules_def)
    apply(clarsimp)
   apply(rename_tac y ya a)(*strict*)
   apply(force)
  apply(rename_tac y ya a aa)(*strict*)
  apply(case_tac a)
  apply(rename_tac y ya a aa prod_lhs prod_rhs)(*strict*)
  apply(case_tac aa)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa)(*strict*)
  apply(subgoal_tac "\<exists>q q_seq I y qA. (r,Some \<lparr>prod_lhs = prod_lhs, prod_rhs = prod_rhs\<rparr>) = (\<lparr>rule_lpop=q#q_seq, rule_rpop=y,rule_lpush=[q,qA], rule_rpush=y\<rparr>,Some \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=(cfg_item_rhs1 I)@(cfg_item_rhs2 I)\<rparr>) \<and> (q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> (cfg_item_rhs1 I=[]) \<and> qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I))) \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) \<and> \<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs2 I,cfg_item_rhs2=[],cfg_item_look_ahead=y\<rparr> \<in> last (q#q_seq))")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER__rules_def)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa)(*strict*)
  apply(subgoal_tac "\<exists>q q_seq I y qA. (r,Some \<lparr>prod_lhs = prod_lhsa, prod_rhs = prod_rhsa\<rparr>) = (\<lparr>rule_lpop=q#q_seq, rule_rpop=y,rule_lpush=[q,qA], rule_rpush=y\<rparr>,Some \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=(cfg_item_rhs1 I)@(cfg_item_rhs2 I)\<rparr>) \<and> (q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> (cfg_item_rhs1 I=[]) \<and> qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I))) \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) \<and> \<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs2 I,cfg_item_rhs2=[],cfg_item_look_ahead=y\<rparr> \<in> last (q#q_seq))")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER__rules_def)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa)(*strict*)
  apply(erule exE)+
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp only: valid_cfg_def)
    apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
      in ballE)
     apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(clarsimp)
     apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac qa q_seqa I Ia yc qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(subgoal_tac "set [teA (cfg_item_lhs I)] \<subseteq> epda_events M")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp only: valid_cfg_def)
    apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
      in ballE)
     apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(clarsimp)
     apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac qa q_seqa I Ia yc qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(subgoal_tac "q_seq=F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(subgoal_tac "{F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)} = F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(force)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(thin_tac "q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(subgoal_tac "[qA]=F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]"
      and s="[F_DFA_GOTO M q (teA (cfg_item_lhs I))]"
      in ssubst)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(subgoal_tac "{F_DFA_GOTO M q (teA (cfg_item_lhs I))} = F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(blast)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(thin_tac "qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
  apply(subgoal_tac "set (cfg_item_rhs2 Ia) \<subseteq> epda_events M")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp only: valid_cfg_def)
    apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs Ia, prod_rhs = cfg_item_rhs2 Ia\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
      in ballE)
     apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(clarsimp)
     apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac qa I Ia yc qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(subgoal_tac "set [teA (cfg_item_lhs Ia)] \<subseteq> epda_events M")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp only: valid_cfg_def)
    apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs Ia, prod_rhs = cfg_item_rhs2 Ia\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
      in ballE)
     apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(clarsimp)
     apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya a aa prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac qa I Ia yc qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(subgoal_tac "q_seqa=F_DFA_GOTO_SEQUENCE M qa (cfg_item_rhs2 Ia)")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(subgoal_tac "{F_DFA_GOTO_SEQUENCE M qa (cfg_item_rhs2 Ia)} = F_EPDA_GOTO_SEQUENCE M qa (cfg_item_rhs2 Ia)")
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(force)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(thin_tac "q_seqa \<in> F_EPDA_GOTO_SEQUENCE M qa (cfg_item_rhs2 Ia)")
  apply(subgoal_tac "[qAa]=F_DFA_GOTO_SEQUENCE M qa [teA (cfg_item_lhs Ia)]")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M qa [teA (cfg_item_lhs Ia)]"
      and s="[F_DFA_GOTO M qa (teA (cfg_item_lhs Ia))]"
      in ssubst)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(subgoal_tac "{F_DFA_GOTO M qa (teA (cfg_item_lhs Ia))} = F_EPDA_GOTO M qa (teA (cfg_item_lhs Ia))")
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(blast)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(thin_tac "qAa \<in> F_EPDA_GOTO M qa (teA (cfg_item_lhs Ia))")
  apply(subgoal_tac "[teA prod_lhs]=[teA prod_lhsa]")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(subgoal_tac "prod_rhs=prod_rhsa")
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(rule_tac
      r="q_seq"
      and P="\<lambda>x. x\<noteq>{}"
      in F_DFA_GOTO_SEQUENCE_injective_prime)
            apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
            apply(blast)
           apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
           apply(blast)
          apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
          apply(rule_tac
      G="G'"
      and F="F"
      and k="k"
      in F_LR_MACHINE_all_Connected)
             apply(force)
            apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
            prefer 3
            apply(force)
           apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
           apply(force)
          apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
          apply(force)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         apply(blast)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(clarsimp)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(clarsimp)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(clarsimp)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(thin_tac "P = AF_LR_PARSER G G' M k Do")
    apply(thin_tac "r \<in> parser_rules P")
    apply(thin_tac "(r, y) \<in> AF_LR_PARSER__rules G G' M k")
    apply(thin_tac "(r, ya) \<in> AF_LR_PARSER__rules G G' M k")
    apply(thin_tac "y = Some a")
    apply(thin_tac "ya = Some aa")
    apply(thin_tac "a = \<lparr>prod_lhs = prod_lhs, prod_rhs = prod_rhs\<rparr>")
    apply(thin_tac "aa = \<lparr>prod_lhs = prod_lhsa, prod_rhs = prod_rhsa\<rparr>")
    apply(thin_tac "qa \<in> epda_states M")
    apply(thin_tac "Ia \<in> qa")
    apply(thin_tac "\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G")
    apply(thin_tac "\<lparr>prod_lhs = cfg_item_lhs Ia, prod_rhs = cfg_item_rhs2 Ia\<rparr> \<in> cfg_productions G")
    apply(thin_tac "cfg_item_rhs1 I = []")
    apply(thin_tac "cfg_item_rhs1 Ia = []")
    apply(thin_tac "\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = yb\<rparr> \<in> last (q # q_seq)")
    apply(thin_tac "\<lparr>cfg_item_lhs = cfg_item_lhs Ia, cfg_item_rhs1 = cfg_item_rhs2 Ia, cfg_item_rhs2 = [], cfg_item_look_ahead = yc\<rparr> \<in> last (qa # q_seqa)")
    apply(thin_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
    apply(thin_tac "set [teA (cfg_item_lhs I)] \<subseteq> epda_events M")
    apply(thin_tac "[qA] = F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]")
    apply(thin_tac "set (cfg_item_rhs2 Ia) \<subseteq> epda_events M")
    apply(thin_tac "set [teA (cfg_item_lhs Ia)] \<subseteq> epda_events M")
    apply(thin_tac "q_seqa = F_DFA_GOTO_SEQUENCE M qa (cfg_item_rhs2 Ia)")
    apply(thin_tac "[qAa] = F_DFA_GOTO_SEQUENCE M qa [teA (cfg_item_lhs Ia)]")
    apply(thin_tac "[teA prod_lhs] = [teA prod_lhsa]")
    apply(thin_tac "(r, Some \<lparr>prod_lhs = prod_lhs, prod_rhs = prod_rhs\<rparr>) = (\<lparr>rule_lpop = q # q_seq, rule_rpop = yb, rule_lpush = [q, qA], rule_rpush = yb\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>)")
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(thin_tac "(r, Some \<lparr>prod_lhs = prod_lhsa, prod_rhs = prod_rhsa\<rparr>) = (\<lparr>rule_lpop = qa # q_seqa, rule_rpop = yc, rule_lpush = [qa, qAa], rule_rpush = yc\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs Ia, prod_rhs = cfg_item_rhs1 Ia @ cfg_item_rhs2 Ia\<rparr>)")
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(rule_tac
      S'="S'"
      and Do="Do"
      and G'="G'"
      and G="G"
      in F_LR_MACHINE_no_empty_states_when_reading_items)
               apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
               apply(force)
              apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
              apply(force)
             apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
             apply(force)
            apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
            apply(force)
           apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
           apply(force)
          apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
          apply(force)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         apply(force)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(rule_tac
      t="epda_delta M"
      and s="snd(F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})"
      in ssubst)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(rule F_LR_MACHINE_all_uniqueEntry)
    apply(force)
   apply(force)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(rule_tac
      M="M"
      and r="[qA]"
      and P="\<lambda>x. x\<noteq>{}"
      in F_DFA_GOTO_SEQUENCE_injective_prime)
           apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
           apply(force)
          apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
          apply(force)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         apply(rule F_LR_MACHINE_all_Connected)
            apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
            prefer 3
            apply(force)
           apply(force)
          apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
          apply(force)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
         apply(force)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   prefer 2
   apply(rule_tac
      t="epda_delta M"
      and s="snd(F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})"
      in ssubst)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(rule F_LR_MACHINE_all_uniqueEntry)
    apply(force)
   apply(force)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(thin_tac "P = AF_LR_PARSER G G' M k Do")
  apply(thin_tac "r \<in> parser_rules P")
  apply(thin_tac "(r, y) \<in> AF_LR_PARSER__rules G G' M k")
  apply(thin_tac "(r, ya) \<in> AF_LR_PARSER__rules G G' M k")
  apply(thin_tac "y = Some a")
  apply(thin_tac "ya = Some aa")
  apply(thin_tac "a = \<lparr>prod_lhs = prod_lhs, prod_rhs = prod_rhs\<rparr>")
  apply(thin_tac "aa = \<lparr>prod_lhs = prod_lhsa, prod_rhs = prod_rhsa\<rparr>")
  apply(thin_tac "(r, Some \<lparr>prod_lhs = prod_lhs, prod_rhs = prod_rhs\<rparr>) = (\<lparr>rule_lpop = q # q_seq, rule_rpop = yb, rule_lpush = [q, qA], rule_rpush = yb\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>)")
  apply(thin_tac "(r, Some \<lparr>prod_lhs = prod_lhsa, prod_rhs = prod_rhsa\<rparr>) = (\<lparr>rule_lpop = qa # q_seqa, rule_rpop = yc, rule_lpush = [qa, qAa], rule_rpush = yc\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs Ia, prod_rhs = cfg_item_rhs1 Ia @ cfg_item_rhs2 Ia\<rparr>)")
  apply(thin_tac "qa \<in> epda_states M")
  apply(thin_tac "Ia \<in> qa")
  apply(thin_tac "\<lparr>prod_lhs = cfg_item_lhs Ia, prod_rhs = cfg_item_rhs2 Ia\<rparr> \<in> cfg_productions G")
  apply(thin_tac "cfg_item_rhs1 Ia = []")
  apply(thin_tac "\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = yb\<rparr> \<in> last (q # q_seq)")
  apply(thin_tac "\<lparr>cfg_item_lhs = cfg_item_lhs Ia, cfg_item_rhs1 = cfg_item_rhs2 Ia, cfg_item_rhs2 = [], cfg_item_look_ahead = yc\<rparr> \<in> last (qa # q_seqa)")
  apply(thin_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
  apply(thin_tac "q_seq = F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(thin_tac "set (cfg_item_rhs2 Ia) \<subseteq> epda_events M")
  apply(thin_tac "set [teA (cfg_item_lhs Ia)] \<subseteq> epda_events M")
  apply(thin_tac "q_seqa = F_DFA_GOTO_SEQUENCE M qa (cfg_item_rhs2 Ia)")
  apply(thin_tac "[qAa] = F_DFA_GOTO_SEQUENCE M qa [teA (cfg_item_lhs Ia)]")
  apply(subgoal_tac "\<exists>J w. setA (cfg_item_rhs2 J) \<subseteq> cfg_nonterminals G' \<and> cfg_item_rhs2 J=teA (cfg_item_lhs I)#w \<and> J \<in> q")
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
   apply(thin_tac "I \<in> q")
   apply(thin_tac "\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G")
   apply(thin_tac "cfg_item_rhs1 I = []")
   apply(erule exE)+
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w)(*strict*)
   apply(erule conjE)+
   apply(rule allI)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
   apply(rule impI)
   apply(rule_tac
      t="[qA]!i"
      and s="qA"
      in ssubst)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(case_tac i)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
     apply(rule nth_0)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i nat)(*strict*)
    apply(thin_tac "[qA] = F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]")
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
   apply(rule_tac
      t="qA"
      and s="F_DFA_GOTO M q (teA (cfg_item_lhs I))"
      in ssubst)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(subgoal_tac "[qA] = [F_DFA_GOTO M q (teA (cfg_item_lhs I))]")
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(rule_tac
      t="[F_DFA_GOTO M q (teA (cfg_item_lhs I))]"
      and s="F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]"
      in subst)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
         apply(force)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
          prefer 3
          apply(force)
         apply(force)
        apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
   apply(thin_tac "set [teA (cfg_item_lhs I)] \<subseteq> epda_events M")
   apply(thin_tac "[qA] = F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]")
   apply(thin_tac "i < length [qA]")
   apply(rule_tac
      t="M"
      and s="F_LR_MACHINE G' F k"
      in ssubst)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO (F_LR_MACHINE G' F k) q (teA (cfg_item_lhs I))"
      and s="F_VALID_ITEM_SET_GOTO G' F k (teA (cfg_item_lhs I)) q"
      in subst)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
         apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
      apply(force)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
     apply(simp add: valid_item_def valid_cfg_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
     apply(rename_tac q I J w)(*strict*)
     apply(clarsimp)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
   apply(subgoal_tac "J\<lparr>cfg_item_rhs1:=cfg_item_rhs1 J@[teA (cfg_item_lhs I)],cfg_item_rhs2:=w\<rparr> \<in> F_VALID_ITEM_SET_GOTO__basis (teA (cfg_item_lhs I)) q")
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(subgoal_tac "J\<lparr>cfg_item_rhs1:=cfg_item_rhs1 J@[teA (cfg_item_lhs I)],cfg_item_rhs2:=w\<rparr> \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis (teA (cfg_item_lhs I)) q)")
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
     apply(simp (no_asm_simp) only: F_VALID_ITEM_SET_GOTO_def)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__basis (teA (cfg_item_lhs I)) q"
      in set_mp)
     apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
       apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
       apply(force)
      apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
      apply(clarsimp)
      apply(rename_tac q I J w x)(*strict*)
      apply(rule F_LR_MACHINE_States_contain_Items)
          apply(rename_tac q I J w x)(*strict*)
          apply(force)
         apply(rename_tac q I J w x)(*strict*)
         apply(force)
        apply(rename_tac q I J w x)(*strict*)
        apply(force)
       apply(rename_tac q I J w x)(*strict*)
       apply(force)
      apply(force)
     apply(force)
    apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
    apply(force)
   apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa J w i)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
   apply(rename_tac q I J w)(*strict*)
   apply(rule_tac
      x="J"
      in bexI)
    apply(rename_tac q I J w)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
   apply(rename_tac q I J w)(*strict*)
   apply(force)
  apply(rename_tac y ya a aa prod_lhs prod_rhs prod_lhsa prod_rhsa q qa q_seq q_seqa I Ia yb yc qA qAa)(*strict*)
  apply(thin_tac "[qA] = F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]")
  apply(simp (no_asm_use))
  apply(rename_tac q I)(*strict*)
  apply(subgoal_tac "\<forall>I \<in> SSq. cfg_item_lhs I \<noteq> SSS' \<longrightarrow> cfg_item_rhs1 I = [] \<longrightarrow> (\<exists>J. setA (cfg_item_rhs2 J) \<subseteq> cfg_nonterminals SSG' \<and> (\<exists>w. cfg_item_rhs2 J = teA (cfg_item_lhs I) # w) \<and> J \<in> SSq)" for SSS' SSG' SSq)
   apply(rename_tac q I)(*strict*)
   prefer 2
   apply(rule rhs1_empty_items_due_to_specific_item)
           apply(rename_tac q I)(*strict*)
           apply(force)
          apply(rename_tac q I)(*strict*)
          apply(force)
         apply(rename_tac q I)(*strict*)
         apply(force)
        apply(rename_tac q I)(*strict*)
        apply(force)
       apply(rename_tac q I)(*strict*)
       apply(force)
      apply(rename_tac q I)(*strict*)
      apply(force)
     apply(rename_tac q I)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac q I)(*strict*)
   apply(force)
  apply(rename_tac q I)(*strict*)
  apply(erule_tac
      x="I"
      and P="\<lambda>I. cfg_item_lhs I \<noteq> F_FRESH (cfg_nonterminals G) \<longrightarrow> cfg_item_rhs1 I = [] \<longrightarrow> (\<exists>J. setA (cfg_item_rhs2 J) \<subseteq> cfg_nonterminals (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) \<and> (\<exists>w. cfg_item_rhs2 J = teA (cfg_item_lhs I) # w) \<and> J \<in> q)"
      in ballE)
   apply(rename_tac q I)(*strict*)
   apply(erule impE)
    apply(rename_tac q I)(*strict*)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      and x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = cfg_item_rhs2 I\<rparr>"
      in ballE)
     apply(rename_tac q I)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
      apply(rename_tac q I)(*strict*)
      apply(force)
     apply(rename_tac q I)(*strict*)
     apply(rule F_FRESH_is_fresh)
     apply(simp add: valid_cfg_def)
    apply(rename_tac q I)(*strict*)
    apply(force)
   apply(rename_tac q I)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac q I)(*strict*)
  apply(erule impE)
   apply(rename_tac q I)(*strict*)
   apply(force)
  apply(rename_tac q I)(*strict*)
  apply(force)
  done

lemma X6_3_InformationOnRules_EffectNotNone: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> r \<in> parser_rules P
  \<Longrightarrow> parser_marker P r \<noteq> None"
  apply(subgoal_tac "\<exists>!y. ((r,y) \<in> (AF_LR_PARSER__rules G G' M k))")
   prefer 2
   apply(rule X6_3_InformationOnRules_UniqueEffect)
          apply(force)+
  apply(simp add: AF_LR_PARSER_def)
  done

lemma X6_3_InformationOnRules_reduce2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> r = \<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>
  \<Longrightarrow> r \<in> parser_rules P
  \<Longrightarrow> parser_marker P r = Some (Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>)
  \<Longrightarrow> rpop = rpush \<and> \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr> \<in> cfg_productions G \<and> (\<exists>q\<delta>. lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ \<and> lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A] \<and> (\<exists>\<delta>. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = XSEQ, cfg_item_rhs2 = [], cfg_item_look_ahead = rpop\<rparr> \<in> valid_item_set G' k (teB Do # \<delta> @ XSEQ) \<and> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))))"
  apply(subgoal_tac "\<exists>!y. (\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, y) \<in> (AF_LR_PARSER__rules G G' M k)")
   prefer 2
   apply(simp add: AF_LR_PARSER_def)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(case_tac "\<exists>!y. (\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, y) \<in> AF_LR_PARSER__rules G (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k) k")
    apply(rename_tac b)(*strict*)
    apply(force)
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(subgoal_tac "(\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<in> (AF_LR_PARSER__rules G G' M k)")
   prefer 2
   apply(simp add: AF_LR_PARSER_def)
   apply(clarsimp)
   apply(rename_tac b y)(*strict*)
   apply(case_tac "\<exists>!y. (\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, y) \<in> AF_LR_PARSER__rules G (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k) k")
    apply(rename_tac b y)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac b y)(*strict*)
   apply(rule_tac y="Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>" in theI_prime2)
    apply(rename_tac b y)(*strict*)
    apply(force)
   apply(rename_tac b y)(*strict*)
   apply(clarsimp)
  apply(subgoal_tac "\<exists>q q_seq I y qA. (\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) = (\<lparr>rule_lpop=q#q_seq, rule_rpop=y,rule_lpush=[q,qA], rule_rpush=y\<rparr>,Some \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=(cfg_item_rhs1 I)@(cfg_item_rhs2 I)\<rparr>) \<and> (q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> (cfg_item_rhs1 I=[]) \<and> qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I))) \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) \<and> \<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs2 I,cfg_item_rhs2=[],cfg_item_look_ahead=y\<rparr> \<in> last (q#q_seq))")
   prefer 2
   apply(thin_tac "\<exists>!y. (\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, y) \<in> AF_LR_PARSER__rules G G' M k")
   apply(simp only: AF_LR_PARSER__rules_def)
   apply(clarsimp)
  apply(erule exE)+
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "\<exists>!y. (\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, y) \<in> AF_LR_PARSER__rules G G' M k")
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "(\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<in> AF_LR_PARSER__rules G G' M k")
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      t="rpop"
      and s="rpush"
      in ssubst)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(rule conjI)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(rule_tac
      t="lpop"
      and s="q#q_seq"
      in ssubst)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(rule_tac
      t="rpush"
      and s="y"
      in ssubst)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(rule_tac
      t="lpush"
      and s="[q, qA]"
      in ssubst)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(rule_tac
      t="A"
      and s="cfg_item_lhs I"
      in ssubst)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(rule_tac
      t="XSEQ"
      and s="cfg_item_rhs1 I @ cfg_item_rhs2 I"
      in ssubst)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(rule_tac
      t="cfg_item_rhs1 I"
      and s="[]"
      in ssubst)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "(\<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>, Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) = (\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>)")
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "r = \<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>")
  apply(thin_tac "r \<in> parser_rules P")
  apply(thin_tac "parser_marker P r = Some(Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>)")
  apply(rule conjI)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(rule_tac
      x="q"
      in exI)
  apply(subgoal_tac "valid_cfg G'")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(subgoal_tac "valid_dfa M")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(subgoal_tac "some_step_from_every_configuration M")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(simp only: valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
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
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(subgoal_tac "set [teA (cfg_item_lhs I)] \<subseteq> epda_events M")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(simp only: valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
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
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
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
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac q q_seq I y qA)(*strict*)
         prefer 3
         apply(force)
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
  apply(rule conjI)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(subgoal_tac "[qA]=F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]"
      and s="[F_DFA_GOTO M q (teA (cfg_item_lhs I))]"
      in ssubst)
    apply(rename_tac q q_seq I y qA)(*strict*)
    apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
        apply(rename_tac q q_seq I y qA)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac q q_seq I y qA)(*strict*)
         prefer 3
         apply(force)
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
   apply(subgoal_tac "{F_DFA_GOTO M q (teA (cfg_item_lhs I))} = F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
    apply(rename_tac q q_seq I y qA)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
        apply(rename_tac q q_seq I y qA)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac q q_seq I y qA)(*strict*)
         prefer 3
         apply(force)
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
   apply(blast)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
  apply(rule conjI)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(thin_tac "[qA] = F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]")
  apply(subgoal_tac "\<exists>w. q=last(F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#w)) \<and> set w \<subseteq> epda_events M")
   apply(rename_tac q q_seq I y qA)(*strict*)
   prefer 2
   apply(rule State_With_Item_from_G_is_reached_via_Dollar_w)
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
        apply(force)
       apply(rename_tac q q_seq I y qA)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac q q_seq I y qA)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(rename_tac q q_seq I y)(*strict*)
   apply(clarsimp)
   apply(rename_tac q I y)(*strict*)
   apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      in ballE)
    apply(rename_tac q I y)(*strict*)
    apply(force)
   apply(rename_tac q I y)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA)(*strict*)
  apply(erule exE)+
  apply(rename_tac q q_seq I y qA w)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(rule conjI)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac q q_seq I y qA w)(*strict*)
  apply(rule_tac
      t="valid_item_set G' k (teB Do # w @ [] @ cfg_item_rhs2 I)"
      and s="(if (teB Do # w @ [] @ cfg_item_rhs2 I)=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w @ [] @ cfg_item_rhs2 I)))"
      in ssubst)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(rename_tac q q_seq I y qA w)(*strict*)
         apply(force)
        apply(rename_tac q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA w)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac q q_seq I y qA w)(*strict*)
    apply(rule_tac
      t="teB Do # w @ [] @ cfg_item_rhs2 I"
      and s="[teB Do] @ w @ [] @ cfg_item_rhs2 I"
      in ssubst)
     apply(rename_tac q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA w)(*strict*)
    apply(simp (no_asm) only: setAConcat concat_asso)
    apply(rule Set.Un_least)
     apply(rename_tac q q_seq I y qA w)(*strict*)
     apply(rule Set.Un_least)
      apply(rename_tac q q_seq I y qA w)(*strict*)
      apply(rule Set.Un_least)
       apply(rename_tac q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA w)(*strict*)
      apply(rule two_elements_construct_domain_setA)
      apply(erule conjE)
      apply(simp add: F_LR_MACHINE_def)
     apply(rename_tac q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA w)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   apply(rule_tac
      t="teB Do # w @ [] @ cfg_item_rhs2 I"
      and s="[teB Do] @ w @ [] @ cfg_item_rhs2 I"
      in ssubst)
    apply(rename_tac q q_seq I y qA w)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   apply(simp (no_asm) only: setBConcat concat_asso)
   apply(rule Set.Un_least)
    apply(rename_tac q q_seq I y qA w)(*strict*)
    apply(rule Set.Un_least)
     apply(rename_tac q q_seq I y qA w)(*strict*)
     apply(rule Set.Un_least)
      apply(rename_tac q q_seq I y qA w)(*strict*)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(rename_tac q q_seq I y qA w)(*strict*)
     apply(rule two_elements_construct_domain_setB)
     apply(erule conjE)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac q q_seq I y qA w)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac q q_seq I y qA w)(*strict*)
  apply(rule_tac
      t="(if teB Do # w @ [] @ cfg_item_rhs2 I = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w @ [] @ cfg_item_rhs2 I)))"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w @ [] @ cfg_item_rhs2 I))"
      in ssubst)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA w)(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w @ [] @ cfg_item_rhs2 I))"
      and s="last (q # q_seq)"
      in ssubst)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac q q_seq I y qA w)(*strict*)
  apply(case_tac q_seq)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "cfg_item_rhs2 I = []")
    apply(rename_tac q q_seq I y qA w)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "length (cfg_item_rhs2 I)=length []")
    apply(rename_tac q q_seq I y qA w)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac q q_seq I y qA w)(*strict*)
         apply(force)
        apply(rename_tac q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA w)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac q q_seq I y qA w)(*strict*)
          prefer 3
          apply(force)
         apply(force)
        apply(rename_tac q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA w)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA w)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA w a list)(*strict*)
  apply(rule_tac
      t="last (q#q_seq)"
      and s="last(q_seq)"
      in ssubst)
   apply(rename_tac q q_seq I y qA w a list)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA w a list)(*strict*)
  apply(rule_tac
      t="q_seq"
      and s="F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)"
      in ssubst)
   apply(rename_tac q q_seq I y qA w a list)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA w a list)(*strict*)
  apply(rule_tac
      t="q"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w))"
      in ssubst)
   apply(rename_tac q q_seq I y qA w a list)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA w a list)(*strict*)
  apply(rule_tac
      t="teB Do # w @ [] @ cfg_item_rhs2 I"
      and s="(teB Do # w) @ cfg_item_rhs2 I"
      in ssubst)
   apply(rename_tac q q_seq I y qA w a list)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA w a list)(*strict*)
  apply(rule sym)
  apply(rule F_DFA_GOTO_SEQUENCE_concat)
         apply(rename_tac q q_seq I y qA w a list)(*strict*)
         apply(force)
        apply(rename_tac q q_seq I y qA w a list)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA w a list)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac q q_seq I y qA w a list)(*strict*)
          prefer 3
          apply(force)
         apply(force)
        apply(rename_tac q q_seq I y qA w a list)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA w a list)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA w a list)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA w a list)(*strict*)
     apply(rule_tac
      t="teB Do # w"
      and s="[teB Do] @ w"
      in ssubst)
      apply(rename_tac q q_seq I y qA w a list)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA w a list)(*strict*)
     apply(erule conjE)
     apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
    apply(rename_tac q q_seq I y qA w a list)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA w a list)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA w a list)(*strict*)
  apply(subgoal_tac "length (cfg_item_rhs2 I)=length q_seq")
   apply(rename_tac q q_seq I y qA w a list)(*strict*)
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac q q_seq I y qA w a list)(*strict*)
        apply(force)
       apply(rename_tac q q_seq I y qA w a list)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA w a list)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac q q_seq I y qA w a list)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac q q_seq I y qA w a list)(*strict*)
       apply(force)
      apply(rename_tac q q_seq I y qA w a list)(*strict*)
      apply(force)
     apply(rename_tac q q_seq I y qA w a list)(*strict*)
     apply(force)
    apply(rename_tac q q_seq I y qA w a list)(*strict*)
    apply(force)
   apply(rename_tac q q_seq I y qA w a list)(*strict*)
   apply(force)
  apply(rename_tac q q_seq I y qA w a list)(*strict*)
  apply(force)
  done

lemma X6_3_InformationOnRules_reduce1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr> \<in> (cfg_productions G)
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = XSEQ, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> \<in> valid_item_set G' k (teB Do # \<delta> @ XSEQ)
  \<Longrightarrow> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))
  \<Longrightarrow> \<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # (F_DFA_GOTO_SEQUENCE M q\<delta> [teA A]), rule_rpush = y\<rparr> \<in> (parser_rules P)"
  apply(subgoal_tac "\<exists>x \<in> (AF_LR_PARSER__rules G G' M k). ((\<lambda>(x,y). x) x) = \<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>")
   apply(simp add: AF_LR_PARSER_def)
   apply(force)
  apply(subgoal_tac "(\<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>,Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<in> (AF_LR_PARSER__rules G G' M k)")
   apply(force)
  apply(simp (no_asm) only: AF_LR_PARSER__rules_def)
  apply(simp (no_asm))
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
  apply(subgoal_tac "valid_dfa M")
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "some_step_from_every_configuration M")
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(subgoal_tac "set (teB Do # \<delta> @ XSEQ) \<subseteq> epda_events M")
   prefer 2
   apply(subgoal_tac "teB Do \<in> epda_events M")
    apply(subgoal_tac "set (\<delta>@XSEQ) \<subseteq> epda_events M")
     apply(force)
    apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(simp add: F_LR_MACHINE_def)
    apply(subgoal_tac "setB ([teB Do]@\<delta>@XSEQ) \<subseteq> cfg_events G' \<and> setA ([teB Do]@\<delta>@XSEQ) \<subseteq> cfg_nonterminals G'")
     prefer 2
     apply(rule_tac
      k="k"
      in valid_item_set_nonempty_only_on_Sigma_Strings)
      apply(force)
     apply(force)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(erule conjE)+
     apply(simp only: setBConcat setAConcat concat_asso)
     apply(blast)
    apply(simp add: F_LR_MACHINE_def)
   apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
  apply(subgoal_tac "teA A \<in> epda_events M")
   prefer 2
   apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
    apply(simp add: F_LR_MACHINE_def)
   apply(subgoal_tac "A \<in> cfg_nonterminals G")
    apply(simp add: F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(simp add: valid_cfg_def)
   apply(erule conjE)+
   apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>"
      and P="\<lambda>x. prod_lhs x \<in> cfg_nonterminals (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) \<and> setA (prod_rhs x) \<subseteq> cfg_nonterminals (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) \<and> setB (prod_rhs x) \<subseteq> cfg_events (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))"
      in ballE)
    apply(clarsimp)
    apply(force)
   apply(force)
  apply(subgoal_tac "q\<delta> \<in> epda_states M")
   prefer 2
   apply(subgoal_tac "(set (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)) \<subseteq> epda_states M)")
    apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in set_mp)
     apply(blast)
    apply(rule_tac
      t="q\<delta>"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in ssubst)
     apply(force)
    apply(rule List.last_in_set)
    apply(subgoal_tac "length (teB Do # \<delta>) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))")
     apply(clarsimp)
    apply(rule_tac
      q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(blast)+
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(force)
    apply(blast)
   apply(rule_tac
      w="(teB Do # \<delta>)"
      and q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main3)
        apply(blast)+
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(blast)
  apply(subgoal_tac "teA A \<in> epda_events M")
   prefer 2
   apply(simp add: valid_cfg_def)
  apply(rule conjI)
   apply(rule impI)
   apply(subgoal_tac "length (F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ) = length XSEQ")
    apply(rule_tac
      x="\<lparr>cfg_item_lhs = A,cfg_item_rhs1 = [],cfg_item_rhs2 = [],cfg_item_look_ahead = y\<rparr>"
      in exI)
    apply(simp (no_asm))
    apply(rule_tac
      x="F_DFA_GOTO M q\<delta> (teA A)"
      in exI)
    apply(rule conjI)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(blast)
        apply(blast)
       apply(force)
      apply(blast)
     apply(force)
    apply(rule conjI)
     apply(force)
    apply(rule conjI)
     apply(force)
    apply(rule conjI)
     apply(rule_tac
      t="q\<delta>"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in ssubst)
      apply(force)
     apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta> @ XSEQ))"
      in ssubst)
      apply(force)
     apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta> @ XSEQ))"
      and s="(if (teB Do # \<delta> @ XSEQ)=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta> @ XSEQ)))"
      in ssubst)
      apply(force)
     apply(rule_tac
      t="(if teB Do # \<delta> @ XSEQ = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta> @ XSEQ)))"
      and s="valid_item_set G' k (teB Do # \<delta> @ XSEQ)"
      in ssubst)
      apply(rule sym)
      apply(rule F_LR_MACHINE_all_SOUND)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(subgoal_tac "set (teB Do # \<delta> @ XSEQ) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
        prefer 2
        apply(simp add: F_LR_MACHINE_def)
       apply(rule two_elements_construct_domain_setA)
       apply(force)
      apply(subgoal_tac "set (teB Do # \<delta> @ XSEQ) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
       prefer 2
       apply(simp add: F_LR_MACHINE_def)
      apply(rule two_elements_construct_domain_setB)
      apply(force)
     apply(force)
    apply(rule conjI)
     apply(force)
    apply(rule conjI)
     apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
         apply(blast)
        apply(blast)
       apply(blast)
      apply(blast)
     apply(force)
    apply(rule_tac
      A="valid_item_set G' k (teB Do#\<delta>)"
      in set_mp)
     prefer 2
     apply(force)
    apply(rule_tac
      t="q\<delta>"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in ssubst)
     apply(force)
    prefer 2
    apply(rule sym)
    apply(rule_tac
      M="M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(blast)
        apply(blast)
       apply(blast)
      apply(force)
     apply(force)
    apply(blast)
   defer
   apply(rule impI)
   apply(rule_tac
      x="\<lparr>cfg_item_lhs = A,cfg_item_rhs1 = [],cfg_item_rhs2 = XSEQ,cfg_item_look_ahead = y\<rparr>"
      in exI)
   apply(simp (no_asm))
   apply(rule_tac
      x="F_DFA_GOTO M q\<delta> (teA A)"
      in exI)
   apply(rule conjI)
    apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
        apply(blast)+
   apply(rule conjI)
    apply(blast)
   apply(rule conjI)
    apply(subgoal_tac "set y \<subseteq> cfg_events G' \<and> (\<exists>p \<in> cfg_productions G'. prod_lhs p = A \<and> prod_rhs p = XSEQ)")
     prefer 2
     apply(rule conjI)
      apply(rule valid_item_set_LookAhead_in_cfg_events)
       apply(force)
      apply(force)
     apply(rule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>"
      in bexI)
      apply(force)
     apply(simp add: F_CFG_AUGMENT_def)
    apply(rule_tac
      t="q\<delta>"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in ssubst)
     apply(force)
    apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      and s="(if (teB Do # \<delta>)=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)))"
      in ssubst)
     apply(force)
    apply(rule_tac
      t="(if teB Do # \<delta> = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)))"
      and s="valid_item_set G' k (teB Do # \<delta>)"
      in ssubst)
     apply(rule sym)
     apply(rule F_LR_MACHINE_all_SOUND)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(subgoal_tac "set (teB Do # \<delta>) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
       prefer 2
       apply(simp add: F_LR_MACHINE_def)
      apply(rule two_elements_construct_domain_setA)
      apply(force)
     apply(subgoal_tac "set (teB Do # \<delta>) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
      prefer 2
      apply(simp add: F_LR_MACHINE_def)
     apply(rule two_elements_construct_domain_setB)
     apply(force)
    apply(subgoal_tac "\<exists>n. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = XSEQ, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G' k n (teB Do # \<delta> @ XSEQ)")
     prefer 2
     apply(simp add: valid_item_set_def)
    apply(erule exE)+
    apply(rename_tac n)(*strict*)
    apply(subgoal_tac "\<exists>\<gamma>. viable_prefix G' \<gamma> \<and> ((teB Do # \<delta> @ XSEQ)=\<gamma>@XSEQ) \<and> \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = [],cfg_item_rhs2 = XSEQ@[],cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G' k n \<gamma>")
     apply(rename_tac n)(*strict*)
     prefer 2
     apply(rule Lemma6__24_3)
     apply(force)
    apply(rename_tac n)(*strict*)
    apply(erule exE)+
    apply(rename_tac n \<gamma>)(*strict*)
    apply(erule conjE)+
    apply(subgoal_tac "\<gamma>=teB Do#\<delta>")
     apply(rename_tac n \<gamma>)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n \<gamma>)(*strict*)
    apply(simp add: valid_item_set_def)
    apply(clarsimp)
    apply(rename_tac n p na)(*strict*)
    apply(rule_tac
      x="n"
      in exI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
        apply(blast)+
   apply(rule conjI)
    apply(rule F_DFA_GOTO_SEQUENCE_in_F_EPDA_GOTO_SEQUENCE_for_complete_DFA)
        apply(blast)+
    apply(force)
   apply(rule_tac
      A="valid_item_set G' k ([teB Do]@\<delta> @ XSEQ)"
      in set_mp)
    prefer 2
    apply(clarsimp)
   apply(rule_tac
      t="q\<delta>"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in ssubst)
    apply(blast)
   apply(thin_tac "\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = XSEQ, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> \<in> valid_item_set G' k (teB Do#\<delta> @ XSEQ)")
   apply(thin_tac "q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))")
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) XSEQ)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) ((teB Do # \<delta>) @ XSEQ))"
      in ssubst)
    apply(rule F_DFA_GOTO_SEQUENCE_concat)
           apply(blast)
          apply(blast)
         apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(subgoal_tac "length (F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ) = length XSEQ")
     apply(force)
    apply(rule sym)
    apply(rule_tac
      q="q\<delta>"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(blast)
        apply(blast)
       apply(blast)
      apply(force)
     apply(force)
    apply(blast)
   apply(rule Set.equalityD1)
   apply(rule_tac
      t="valid_item_set G' k ([teB Do] @ \<delta> @ XSEQ)"
      and s="(if ([teB Do] @ \<delta> @ XSEQ)=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) ([teB Do] @ \<delta> @ XSEQ)))"
      in ssubst)
    apply(rule F_LR_MACHINE_all_SOUND)
          apply(blast)
         apply(force)
        apply(blast)
       apply(blast)
      apply(blast)
     apply(rule two_elements_construct_domain_setA)
     apply(simp add: F_LR_MACHINE_def)
    apply(rule two_elements_construct_domain_setB)
    apply(simp add: F_LR_MACHINE_def)
   apply(clarsimp)
  apply(rule Set.equalityD1)
  apply(rule_tac
      t="valid_item_set G' k (teB Do # \<delta>)"
      and s="(if (teB Do # \<delta>)=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)))"
      in ssubst)
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(blast)
        apply(force)
       apply(blast)
      apply(blast)
     apply(blast)
    apply(rule two_elements_construct_domain_setA)
    apply(simp add: F_LR_MACHINE_def)
   apply(rule two_elements_construct_domain_setB)
   apply(simp add: F_LR_MACHINE_def)
  apply(clarsimp)
  done

lemma AF_LR_PARSER_reduce_rules1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> {r. r \<in> (parser_rules P) \<and> (\<exists>A XSEQ. (parser_marker P) r = Some (Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<and> (\<exists>q\<delta> y. r = \<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>))} = {r. \<exists>lpop rpop lpush rpush A XSEQ. r = \<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr> \<and> (parser_marker P) r = Some (Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<and> rpop = rpush \<and> \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr> \<in> (cfg_productions G) \<and> (\<exists>q\<delta>. lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ \<and> lpush = q\<delta> # (F_DFA_GOTO_SEQUENCE M q\<delta> [teA A]) \<and> (\<exists>\<delta>. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = XSEQ, cfg_item_rhs2 = [], cfg_item_look_ahead = rpop\<rparr> \<in> valid_item_set G' k (teB Do # \<delta> @ XSEQ) \<and> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))))}"
  apply(rule order_antisym)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "x \<in> parser_rules P \<and> (\<exists>A XSEQ. parser_marker P x = Some(Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<and> (\<exists>q\<delta> y. x = \<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>))")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "x \<in> {r \<in> parser_rules P. \<exists>A XSEQ. parser_marker P r = Some(Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<and> (\<exists>q\<delta> y. r = \<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>)}")
   apply(rename_tac x)(*strict*)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac x A XSEQ)(*strict*)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
   apply(subgoal_tac "y = y \<and> \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr> \<in> cfg_productions G \<and> (\<exists>q\<delta>. (rule_lpop x) = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ \<and> (rule_lpush x) = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A] \<and> (\<exists>\<delta>. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = XSEQ, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> \<in> valid_item_set G' k (teB Do # \<delta> @ XSEQ) \<and> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))))")
    apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
    prefer 2
    apply(rule X6_3_InformationOnRules_reduce2)
             apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
             apply(force)
            apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
            apply(force)
           apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
           apply(force)
          apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
          apply(force)
         apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
         apply(force)
        apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
        apply(force)
       apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
       apply(force)
      apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
      apply(force)
     apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
     apply(force)
    apply(rename_tac x A XSEQ q\<delta> y)(*strict*)
    apply(force)
   apply(force)
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>lpop rpop lpush rpush A XSEQ. x = \<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr> \<and> parser_marker P x = Some(Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<and> rpop = rpush \<and> \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr> \<in> cfg_productions G \<and> (\<exists>q\<delta>. lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ \<and> lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A] \<and> (\<exists>\<delta>. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = XSEQ, cfg_item_rhs2 = [], cfg_item_look_ahead = rpop\<rparr> \<in> valid_item_set G' k (teB Do # \<delta> @ XSEQ) \<and> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))))")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(erule exE)+
  apply(rename_tac x lpop rpop lpush rpush A XSEQ)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta>)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "\<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = rpush, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = rpush\<rparr> \<in> parser_rules P")
   apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
   prefer 2
   apply(rule X6_3_InformationOnRules_reduce1)
            apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
            apply(force)
           apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
           apply(force)
          apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
          apply(force)
         apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
         apply(force)
        apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
        apply(force)
       apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
       apply(force)
      apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
      apply(force)
     apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
     apply(force)
    apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
    apply(force)
   apply(rename_tac x lpop rpop lpush rpush A XSEQ q\<delta> \<delta>)(*strict*)
   apply(clarsimp)
  apply(force)
  done

lemma AF_LR_PARSER_reduce_rules2_direction2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> r \<in> parser_rules P
  \<Longrightarrow> parser_marker P r = Some (Some a)
  \<Longrightarrow> \<exists>A XSEQ. (parser_marker P) r = Some (Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<and> (\<exists>q\<delta> y. r = \<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>)"
  apply(subgoal_tac "r \<in> (\<lambda>(x,y). x) ` (AF_LR_PARSER__rules G G' M k)")
   prefer 2
   apply(simp add: AF_LR_PARSER_def)
  apply(subgoal_tac "\<exists>y \<in> AF_LR_PARSER__rules G G' M k. (\<lambda>(x, y). x) y = r")
   prefer 2
   apply(rule inMap_rev)
   apply(force)
  apply(erule bexE)
  apply(rename_tac y)(*strict*)
  apply(subgoal_tac "(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None) r = Some(Some a)")
   apply(rename_tac y)(*strict*)
   prefer 2
   apply(rule_tac
      t="(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None) r"
      and s="parser_marker P r"
      in ssubst)
    apply(rename_tac y)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(thin_tac "parser_marker P r = Some(Some a)")
   apply(rule sym)
   apply(simp add: AF_LR_PARSER_def)
  apply(rename_tac y)(*strict*)
  apply(subgoal_tac "\<exists>!y. (r, y) \<in> AF_LR_PARSER__rules G G' M k")
   apply(rename_tac y)(*strict*)
   prefer 2
   apply(case_tac "\<exists>!y. (r, y) \<in> AF_LR_PARSER__rules G G' M k")
    apply(rename_tac y)(*strict*)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(subgoal_tac "(THE y. (r, y) \<in> AF_LR_PARSER__rules G G' M k, True) = (Some a,True)")
   apply(rename_tac y)(*strict*)
   prefer 2
   apply(case_tac "\<exists>!y. (r, y) \<in> AF_LR_PARSER__rules G G' M k")
    apply(rename_tac y)(*strict*)
    apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y aa b)(*strict*)
  apply(subgoal_tac "b=(THE y. (r, y) \<in> AF_LR_PARSER__rules G G' M k)")
   apply(rename_tac y aa b)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule HOL.the1_equality)
    apply(rename_tac y aa b)(*strict*)
    apply(clarsimp)
   apply(rename_tac y aa b)(*strict*)
   apply(force)
  apply(rename_tac y aa b)(*strict*)
  apply(subgoal_tac "b\<noteq>None")
   apply(rename_tac y aa b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac y aa b)(*strict*)
  apply(subgoal_tac "y \<in> {(\<lparr>rule_lpop=q#q_seq, rule_rpop=y,rule_lpush=[q,qA], rule_rpush=y\<rparr>,Some \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=(cfg_item_rhs1 I)@(cfg_item_rhs2 I)\<rparr>)| q q_seq I y qA. q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> (cfg_item_rhs1 I=[]) \<and> qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I))) \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) \<and> \<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs2 I,cfg_item_rhs2=[],cfg_item_look_ahead=y\<rparr> \<in> last (q#q_seq)}")
   apply(rename_tac y aa b)(*strict*)
   prefer 2
   apply(rule_tac
      A="{(\<lparr>rule_lpop=q#q_seq, rule_rpop=y,rule_lpush=[q,qA], rule_rpush=y\<rparr>,Some \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=(cfg_item_rhs1 I)@(cfg_item_rhs2 I)\<rparr>)| q q_seq I y qA. q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> (cfg_item_rhs1 I=[]) \<and> qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I))) \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) \<and> \<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs2 I,cfg_item_rhs2=[],cfg_item_look_ahead=y\<rparr> \<in> last (q#q_seq)}"
      and B="{(\<lparr>rule_lpop = [q], rule_rpop = a # y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, None) |q a y qA. q \<in> epda_states M \<and> (\<exists>I \<in> q. \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> [teB a] = take (Suc 0) (cfg_item_rhs2 I) \<and> qA \<in> F_EPDA_GOTO M q (teB a) \<and> y \<in> cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I)))}"
      in elementChoice)
    apply(rename_tac y aa b)(*strict*)
    apply(simp add: AF_LR_PARSER__rules_def)
   apply(rename_tac y aa b)(*strict*)
   apply(force)
  apply(rename_tac y aa b)(*strict*)
  apply(subgoal_tac "\<exists>q q_seq I y' qA. y=(\<lparr>rule_lpop = q # q_seq, rule_rpop = y', rule_lpush = [q, qA], rule_rpush = y'\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>) \<and> (q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> cfg_item_rhs1 I = [] \<and> qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I)) \<and> q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) \<and> \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y'\<rparr> \<in> last (q # q_seq))")
   apply(rename_tac y aa b)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac y aa b)(*strict*)
  apply(thin_tac "y \<in> {(\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>) | q q_seq I y qA. q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> cfg_item_rhs1 I = [] \<and> qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I)) \<and> q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) \<and> \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> \<in> last (q # q_seq)}")
  apply(rename_tac y aa b)(*strict*)
  apply(erule exE)+
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      x="cfg_item_lhs I"
      in exI)
  apply(rule_tac
      x="cfg_item_rhs2 I"
      in exI)
  apply(rule conjI)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(rule_tac
      s="(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None) r"
      and t="parser_marker P r"
      in ssubst)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(simp add: AF_LR_PARSER_def)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(rule_tac
      t="(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None) r"
      and s="Some(THE y. (r, y) \<in> AF_LR_PARSER__rules G G' M k)"
      in ssubst)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(clarsimp)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(rule_tac
      t="(THE y. (r, y) \<in> AF_LR_PARSER__rules G G' M k)"
      and s="b"
      in ssubst)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(force)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(subgoal_tac "(r, b) \<in> AF_LR_PARSER__rules G G' M k")
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(subgoal_tac "(r, Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>) \<in> AF_LR_PARSER__rules G G' M k")
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(clarsimp)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(rule_tac
      x="q"
      in exI)
  apply(rule_tac
      x="y'"
      in exI)
  apply(subgoal_tac "valid_cfg G'")
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(subgoal_tac "valid_dfa M")
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
     apply(blast)
    apply(blast)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(blast)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(subgoal_tac "some_step_from_every_configuration M")
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(force)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
      prefer 3
      apply(force)
     apply(force)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(force)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(force)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(simp only: valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
      in ballE)
     apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
      apply(force)
     apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
     apply(force)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(force)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac q q_seq I y' qA bb y)(*strict*)
    apply(force)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(subgoal_tac "set [teA (cfg_item_lhs I)] \<subseteq> epda_events M")
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(simp only: valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
      in ballE)
     apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
      apply(force)
     apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
     apply(force)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(force)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac q q_seq I y' qA bb y)(*strict*)
    apply(force)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) = q_seq")
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule F_DFA_GOTO_SEQUENCE_F_EPDA_GOTO_SEQUENCE_elem)
        apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
        apply(blast)
       apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
       apply(blast)
      apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
      apply(blast)
     apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
     apply(blast)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(blast)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(force)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)] = [qA]")
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule F_DFA_GOTO_SEQUENCE_F_EPDA_GOTO_SEQUENCE_elem)
        apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
        apply(blast)
       apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
       apply(blast)
      apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
      apply(blast)
     apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
     apply(blast)
    apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
    apply(force)
   apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
   apply(simp add: F_EPDA_GOTO_SEQUENCE_def)
  apply(rename_tac y aa b q q_seq I y' qA)(*strict*)
  apply(force)
  done

lemma AF_LR_PARSER_reduce_rules2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> {r. r \<in> (parser_rules P) \<and> (\<exists>A XSEQ. (parser_marker P) r = Some (Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<and> (\<exists>q\<delta> y. r = \<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>))} = {r. r \<in> (parser_rules P) \<and> (\<exists>a. (parser_marker P) r = Some (Some a))}"
  apply(rule order_antisym)
   apply(clarsimp)
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>A XSEQ. (parser_marker P) x = Some(Some \<lparr>prod_lhs=A,prod_rhs=XSEQ\<rparr>) \<and> (\<exists>q\<delta> y. x=\<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>)")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(subgoal_tac "x \<in> parser_rules P \<and>(\<exists>a. parser_marker P x = Some(Some a))")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(erule conjE)
   apply(erule exE)
   apply(rename_tac x a)(*strict*)
   apply(rule AF_LR_PARSER_reduce_rules2_direction2)
           apply(rename_tac x a)(*strict*)
           apply(blast)+
  done

corollary AF_LR_PARSER_reduce_rules: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> {r. r \<in> (parser_rules P) \<and> (\<exists>a. (parser_marker P) r = Some (Some a))} = {r. \<exists>lpop rpop lpush rpush A XSEQ. r = \<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr> \<and> (parser_marker P) r = Some (Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<and> rpop = rpush \<and> \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr> \<in> (cfg_productions G) \<and> (\<exists>q\<delta>. lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ \<and> lpush = q\<delta> # (F_DFA_GOTO_SEQUENCE M q\<delta> [teA A]) \<and> (\<exists>\<delta>. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = XSEQ, cfg_item_rhs2 = [], cfg_item_look_ahead = rpop\<rparr> \<in> valid_item_set G' k (teB Do # \<delta> @ XSEQ) \<and> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))))}"
  apply(rule_tac
      t="{r. r \<in> (parser_rules P) \<and> (\<exists>a. (parser_marker P) r = Some(Some a))}"
      and s="{r. r \<in> (parser_rules P) \<and> (\<exists>A XSEQ. (parser_marker P) r = Some(Some \<lparr>prod_lhs=A,prod_rhs=XSEQ\<rparr>) \<and> (\<exists>q\<delta> y. r=\<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>))}"
      in subst)
   apply(rule AF_LR_PARSER_reduce_rules2)
         apply(blast)
        apply(blast)
       apply(blast)
      apply(blast)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(rule AF_LR_PARSER_reduce_rules1)
        apply(blast)
       apply(blast)
      apply(blast)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(blast)
  done

lemma X6_3_InformationOnRules_shift1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = (teB a) # \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (teB Do # \<delta>)
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = \<alpha> @ (teB a) # \<beta>\<rparr> \<in> cfg_productions G
  \<Longrightarrow> y \<in> (cfgSTD_first G' (k - 1) (\<beta> @ (liftB z)))
  \<Longrightarrow> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))
  \<Longrightarrow> \<lparr>rule_lpop = [q\<delta>], rule_rpop = a # y, rule_lpush = [q\<delta>, F_DFA_GOTO M q\<delta> (teB a)], rule_rpush = y\<rparr> \<in> (parser_rules P)"
  apply(subgoal_tac "\<exists>x \<in> (AF_LR_PARSER__rules G G' M k). ((\<lambda>(x,y). x) x) = \<lparr>rule_lpop=[q\<delta>],rule_rpop=a#y,rule_lpush=[q\<delta>,F_DFA_GOTO M q\<delta> (teB a)], rule_rpush=y\<rparr>")
   apply(simp add: AF_LR_PARSER_def)
   apply(force)
  apply(subgoal_tac "(\<lparr>rule_lpop = [q\<delta>], rule_rpop = a # y, rule_lpush = [q\<delta>, F_DFA_GOTO M q\<delta> (teB a)], rule_rpush = y\<rparr>,None) \<in> (AF_LR_PARSER__rules G G' M k)")
   apply(force)
  apply(simp (no_asm) only: AF_LR_PARSER__rules_def)
  apply(simp (no_asm))
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
  apply(subgoal_tac "valid_dfa M")
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(subgoal_tac "some_step_from_every_configuration M")
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(blast)
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
  apply(subgoal_tac "set (teB Do # \<delta>) \<subseteq> epda_events M")
   prefer 2
   apply(subgoal_tac "teB Do \<in> epda_events M")
    apply(subgoal_tac "set \<delta> \<subseteq> epda_events M")
     apply(force)
    apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(simp add: F_LR_MACHINE_def)
    apply(subgoal_tac "setB ([teB Do]@\<delta>) \<subseteq> cfg_events G' \<and> setA ([teB Do]@\<delta>) \<subseteq> cfg_nonterminals G'")
     prefer 2
     apply(rule_tac
      k="k"
      in valid_item_set_nonempty_only_on_Sigma_Strings)
      apply(force)
     apply(force)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(erule conjE)+
     apply(simp only: setBConcat setAConcat concat_asso)
     apply(blast)
    apply(simp add: F_LR_MACHINE_def)
   apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
  apply(subgoal_tac "valid_item G' k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teB a # \<beta>, cfg_item_look_ahead = z\<rparr>")
   prefer 2
   apply(rule Fact6_12__2)
    apply(force)
   apply(force)
  apply(subgoal_tac "teA A \<in> epda_events M")
   prefer 2
   apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
    apply(simp add: F_LR_MACHINE_def)
   apply(subgoal_tac "A \<in> cfg_nonterminals G'")
    apply(simp add: two_elements_construct_domain_def)
   apply(simp add: valid_cfg_def)
   apply(erule conjE)+
   apply(simp add: valid_item_def)
   apply(clarsimp)
  apply(subgoal_tac "q\<delta> \<in> epda_states M")
   prefer 2
   apply(subgoal_tac "(set (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)) \<subseteq> epda_states M)")
    apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in set_mp)
     apply(blast)
    apply(rule_tac
      t="q\<delta>"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in ssubst)
     apply(force)
    apply(rule List.last_in_set)
    apply(subgoal_tac "length (teB Do # \<delta>) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))")
     apply(clarsimp)
    apply(rule_tac
      q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(blast)+
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(force)
    apply(blast)
   apply(rule_tac
      q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main3)
        apply(blast)+
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(blast)
   apply(blast)
  apply(subgoal_tac "teA A \<in> epda_events M")
   prefer 2
   apply(simp add: valid_cfg_def)
  apply(subgoal_tac "teB a \<in> epda_events M")
   prefer 2
   apply(simp add: valid_item_def)
   apply(clarsimp)
   apply(rename_tac p)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="p"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) \<and> setB (prod_rhs p) \<subseteq> cfg_events (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))"
      in ballE)
    apply(rename_tac p)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
    apply(rule_tac
      A="set [teB a]"
      in set_mp)
     apply(rename_tac p)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac p)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      A="setB (\<alpha> @ teB a # \<beta>)"
      in set_mp)
       apply(rename_tac p)(*strict*)
       apply(clarsimp)
      apply(rename_tac p)(*strict*)
      apply(rule elemInsetB)
     apply(rename_tac p)(*strict*)
     apply(force)
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(force)
  apply(rule_tac
      x="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teB a # \<beta>, cfg_item_look_ahead = z\<rparr>"
      in bexI)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="q\<delta>"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
      and s="(if (teB Do # \<delta>)=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)))"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="(if teB Do # \<delta> = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)))"
      and s="valid_item_set G' k (teB Do # \<delta>)"
      in ssubst)
   apply(rule sym)
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(blast)
        apply(force)
       apply(blast)
      apply(blast)
     apply(blast)
    apply(rule two_elements_construct_domain_setA)
    apply(simp add: F_LR_MACHINE_def)
   apply(rule two_elements_construct_domain_setB)
   apply(simp add: F_LR_MACHINE_def)
  apply(blast)
  done

lemma X6_3_InformationOnRules_shift2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> r = \<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr>
  \<Longrightarrow> r \<in> parser_rules P
  \<Longrightarrow> parser_marker P r = Some None
  \<Longrightarrow> \<exists>q\<delta> y \<beta> z A \<alpha> a \<delta>. y \<in> (cfgSTD_first G' (k - 1) (\<beta> @ (liftB z))) \<and> \<lparr>prod_lhs = A, prod_rhs = \<alpha> @ (teB a) # \<beta>\<rparr> \<in> cfg_productions G \<and> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)) \<and> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = (teB a) # \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (teB Do # \<delta>) \<and> lpop = [q\<delta>] \<and> rpop = a # y \<and> lpush = [q\<delta>, F_DFA_GOTO M q\<delta> (teB a)] \<and> rpush = y"
  apply(subgoal_tac "\<exists>x \<in> (AF_LR_PARSER__rules G G' M k). ((\<lambda>(x,y). x) x) = r")
   prefer 2
   apply(simp add: AF_LR_PARSER_def)
   apply(force)
  apply(erule bexE)+
  apply(rename_tac x)(*strict*)
  apply(case_tac x)
  apply(rename_tac x a b)(*strict*)
  apply(subgoal_tac "b=None")
   apply(rename_tac x a b)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>!y. ((r,y) \<in> (AF_LR_PARSER__rules G G' M k))")
    apply(rename_tac x a b)(*strict*)
    prefer 2
    apply(rule X6_3_InformationOnRules_UniqueEffect)
           apply(rename_tac x a b)(*strict*)
           apply(force)
          apply(force)
         apply(rename_tac x a b)(*strict*)
         apply(force)
        apply(rename_tac x a b)(*strict*)
        apply(force)
       apply(rename_tac x a b)(*strict*)
       apply(force)
      apply(rename_tac x a b)(*strict*)
      apply(force)
     apply(rename_tac x a b)(*strict*)
     apply(force)
    apply(rename_tac x a b)(*strict*)
    apply(force)
   apply(rename_tac x a b)(*strict*)
   apply(subgoal_tac "(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None) r = Some None")
    apply(rename_tac x a b)(*strict*)
    prefer 2
    apply(rule_tac
      t="(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None) r"
      and s="parser_marker P r"
      in ssubst)
     apply(rename_tac x a b)(*strict*)
     apply(simp add: AF_LR_PARSER_def)
    apply(rename_tac x a b)(*strict*)
    apply(force)
   apply(rename_tac x a b)(*strict*)
   apply(subgoal_tac "(THE y. (r, y) \<in> AF_LR_PARSER__rules G G' M k) = None")
    apply(rename_tac x a b)(*strict*)
    apply(rule_tac
      t="None"
      and s="(THE y. (r, y) \<in> AF_LR_PARSER__rules G G' M k)"
      in ssubst)
     apply(rename_tac x a b)(*strict*)
     apply(force)
    apply(rename_tac x a b)(*strict*)
    apply(rule sym)
    apply(rule HOL.the1_equality)
     apply(rename_tac x a b)(*strict*)
     apply(force)
    apply(rename_tac x a b)(*strict*)
    apply(force)
   apply(rename_tac x a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac x a b)(*strict*)
  apply(subgoal_tac "\<exists>q a y qA. r=\<lparr>rule_lpop=[q],rule_rpop=a#y,rule_lpush=[q,qA],rule_rpush=y\<rparr> \<and> (q \<in> epda_states M) \<and> (\<exists>I \<in> q. \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> [teB a] = take (Suc 0) (cfg_item_rhs2 I) \<and> qA \<in> (F_EPDA_GOTO M q (teB a)) \<and> y \<in> (cfgSTD_first G' (k - 1) ((drop (Suc 0) (cfg_item_rhs2 I))@(liftB (cfg_item_look_ahead I)))))")
   apply(rename_tac x a b)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER__rules_def)
  apply(rename_tac x a b)(*strict*)
  apply(erule exE)+
  apply(rename_tac x a b q aa y qA)(*strict*)
  apply(erule conjE)+
  apply(erule bexE)+
  apply(rename_tac x a b q aa y qA I)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      x="q"
      in exI)
  apply(rule_tac
      x="y"
      in exI)
  apply(rule_tac
      x="drop (Suc 0) (cfg_item_rhs2 I)"
      in exI)
  apply(rule_tac
      x="cfg_item_look_ahead I"
      in exI)
  apply(rule_tac
      x="cfg_item_lhs I"
      in exI)
  apply(rule_tac
      x="cfg_item_rhs1 I"
      in exI)
  apply(rule_tac
      x="aa"
      in exI)
  apply(subgoal_tac "valid_cfg G'")
   apply(rename_tac x a b q aa y qA I)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
  apply(rename_tac x a b q aa y qA I)(*strict*)
  apply(subgoal_tac "valid_dfa M")
   apply(rename_tac x a b q aa y qA I)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(rename_tac x a b q aa y qA I)(*strict*)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(rename_tac x a b q aa y qA I)(*strict*)
  apply(subgoal_tac "some_step_from_every_configuration M")
   apply(rename_tac x a b q aa y qA I)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(rename_tac x a b q aa y qA I)(*strict*)
     apply(blast)
    apply(force)
   apply(force)
  apply(rename_tac x a b q aa y qA I)(*strict*)
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   apply(rename_tac x a b q aa y qA I)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      apply(rename_tac x a b q aa y qA I)(*strict*)
      prefer 3
      apply(force)
     apply(force)
    apply(rename_tac x a b q aa y qA I)(*strict*)
    apply(force)
   apply(rename_tac x a b q aa y qA I)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I)(*strict*)
  apply(subgoal_tac "\<exists>w. q=last(F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#w)) \<and> (set w \<subseteq> epda_events M)")
   apply(rename_tac x a b q aa y qA I)(*strict*)
   prefer 2
   apply(rule State_With_Item_from_G_is_reached_via_Dollar_w)
              apply(rename_tac x a b q aa y qA I)(*strict*)
              apply(force)
             apply(force)
            apply(rename_tac x a b q aa y qA I)(*strict*)
            apply(force)
           apply(rename_tac x a b q aa y qA I)(*strict*)
           apply(force)
          apply(rename_tac x a b q aa y qA I)(*strict*)
          apply(force)
         apply(rename_tac x a b q aa y qA I)(*strict*)
         apply(force)
        apply(rename_tac x a b q aa y qA I)(*strict*)
        apply(force)
       apply(rename_tac x a b q aa y qA I)(*strict*)
       apply(force)
      apply(rename_tac x a b q aa y qA I)(*strict*)
      apply(force)
     apply(rename_tac x a b q aa y qA I)(*strict*)
     apply(force)
    apply(rename_tac x a b q aa y qA I)(*strict*)
    apply(force)
   apply(rename_tac x a b q aa y qA I)(*strict*)
   apply(simp only: valid_cfg_def)
   apply(erule conjE)+
   apply(erule_tac
      P="\<lambda>p. valid_cfg_step_label G p"
      and x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>"
      in ballE)
    apply(rename_tac x a b q aa y qA I)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a b q aa y qA I)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I)(*strict*)
  apply(erule exE)+
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "valid_item_set G' k (teB Do # w)=(if (teB Do # w)=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w)))")
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(rename_tac x a b q aa y qA I w)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac x a b q aa y qA I w)(*strict*)
       apply(force)
      apply(rename_tac x a b q aa y qA I w)(*strict*)
      apply(force)
     apply(rename_tac x a b q aa y qA I w)(*strict*)
     apply(force)
    apply(rename_tac x a b q aa y qA I w)(*strict*)
    apply(simp (no_asm_simp))
    apply(rule two_elements_construct_domain_setA)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(simp (no_asm_simp))
   apply(rule conjI)
    apply(rename_tac x a b q aa y qA I w)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(subgoal_tac "teB aa# drop (Suc 0) (cfg_item_rhs2 I) = cfg_item_rhs2 I")
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   prefer 2
   apply(rule_tac
      t="teB aa# drop (Suc 0) (cfg_item_rhs2 I)"
      and s="[teB aa] @ drop (Suc 0) (cfg_item_rhs2 I)"
      in ssubst)
    apply(rename_tac x a b q aa y qA I w)(*strict*)
    apply(rule ConsApp)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(rule_tac
      s="cfg_item_rhs2 I"
      and t="[teB aa] @ drop (Suc 0) (cfg_item_rhs2 I)"
      in ssubst)
    apply(rename_tac x a b q aa y qA I w)(*strict*)
    apply(rule_tac
      t="[teB aa]"
      and s="take (Suc 0) (cfg_item_rhs2 I)"
      in ssubst)
     apply(rename_tac x a b q aa y qA I w)(*strict*)
     apply(force)
    apply(rename_tac x a b q aa y qA I w)(*strict*)
    apply(rule List.append_take_drop_id)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(rule conjI)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(rule conjI)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(rule conjI)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(rule conjI)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(rule_tac
      s="I"
      and t="\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs1 I, cfg_item_rhs2 = teB aa # drop (Suc 0) (cfg_item_rhs2 I), cfg_item_look_ahead = cfg_item_look_ahead I\<rparr>"
      in ssubst)
    apply(rename_tac x a b q aa y qA I w)(*strict*)
    apply(force)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(rule conjI)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(rule conjI)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(rule conjI)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO M q (teB aa)"
      and s="qA"
      in subst)
    apply(rename_tac x a b q aa y qA I w)(*strict*)
    apply(rule F_DFA_GOTO_F_EPDA_GOTO_elem)
         apply(rename_tac x a b q aa y qA I w)(*strict*)
         apply(force)
        apply(rename_tac x a b q aa y qA I w)(*strict*)
        apply(force)
       apply(rename_tac x a b q aa y qA I w)(*strict*)
       apply(force)
      apply(rename_tac x a b q aa y qA I w)(*strict*)
      apply(force)
     apply(rename_tac x a b q aa y qA I w)(*strict*)
     apply(rule_tac
      A="set (cfg_item_rhs2 I)"
      in set_mp)
      apply(rename_tac x a b q aa y qA I w)(*strict*)
      apply(rule_tac
      G="G'"
      in F_LR_MACHINE_item_in_state_rhs2_in_cfg_events)
          apply(rename_tac x a b q aa y qA I w)(*strict*)
          apply(force)
         apply(rename_tac x a b q aa y qA I w)(*strict*)
         apply(force)
        apply(rename_tac x a b q aa y qA I w)(*strict*)
        apply(force)
       apply(rename_tac x a b q aa y qA I w)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac x a b q aa y qA I w)(*strict*)
     apply(rule_tac
      w'="drop (Suc 0) (cfg_item_rhs2 I)"
      in head_in_set)
     apply(force)
    apply(rename_tac x a b q aa y qA I w)(*strict*)
    apply(force)
   apply(rename_tac x a b q aa y qA I w)(*strict*)
   apply(force)
  apply(rename_tac x a b q aa y qA I w)(*strict*)
  apply(force)
  done

corollary AF_LR_PARSER_shift_rules: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> {r. r \<in> (parser_rules P) \<and> (parser_marker P) r = Some None} = {r. \<exists>lpop rpop lpush rpush. r = \<lparr>rule_lpop = lpop, rule_rpop = rpop, rule_lpush = lpush, rule_rpush = rpush\<rparr> \<and> (\<exists>q\<delta> y \<beta> z A \<alpha> a \<delta>. y \<in> (cfgSTD_first G' (k - 1) (\<beta> @ (liftB z))) \<and> \<lparr>prod_lhs = A, prod_rhs = \<alpha> @ (teB a) # \<beta>\<rparr> \<in> cfg_productions G \<and> q\<delta> = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)) \<and> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = (teB a) # \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (teB Do # \<delta>) \<and> lpop = [q\<delta>] \<and> rpop = a # y \<and> lpush = [q\<delta>, F_DFA_GOTO M q\<delta> (teB a)] \<and> rpush = y)}"
  apply(rule order_antisym)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
   apply(rename_tac x rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
   apply(rename_tac lpop rpop lpush rpush)
   apply(rename_tac x lpop rpop lpush rpush)(*strict*)
   apply(subgoal_tac "\<exists>q\<delta> y \<beta> z A \<alpha> a \<delta>. y \<in> (cfgSTD_first G' (k- 1) (\<beta>@(liftB z))) \<and> \<lparr>prod_lhs=A,prod_rhs=\<alpha>@(teB a)#\<beta>\<rparr> \<in> cfg_productions G \<and> q\<delta>=last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#\<delta>)) \<and> \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>,cfg_item_rhs2 = (teB a)#\<beta>,cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (teB Do#\<delta>) \<and> lpop=[q\<delta>] \<and> rpop=a#y \<and> lpush=[q\<delta>,F_DFA_GOTO M q\<delta> (teB a)] \<and> rpush=y")
    apply(rename_tac x lpop rpop lpush rpush)(*strict*)
    prefer 2
    apply(rule X6_3_InformationOnRules_shift2)
             apply(rename_tac x lpop rpop lpush rpush)(*strict*)
             apply(blast)
            apply(rename_tac x lpop rpop lpush rpush)(*strict*)
            apply(blast)
           apply(rename_tac x lpop rpop lpush rpush)(*strict*)
           apply(blast)
          apply(rename_tac x lpop rpop lpush rpush)(*strict*)
          apply(blast)
         apply(rename_tac x lpop rpop lpush rpush)(*strict*)
         apply(blast)
        apply(force)
       apply(rename_tac x lpop rpop lpush rpush)(*strict*)
       apply(blast)
      apply(rename_tac x lpop rpop lpush rpush)(*strict*)
      apply(blast)
     apply(rename_tac x lpop rpop lpush rpush)(*strict*)
     apply(blast)
    apply(rename_tac x lpop rpop lpush rpush)(*strict*)
    apply(blast)
   apply(rename_tac x lpop rpop lpush rpush)(*strict*)
   apply(force)
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(case_tac x)
  apply(rename_tac x rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
  apply(rename_tac lpop rpop lpush rpush)
  apply(rename_tac x lpop rpop lpush rpush)(*strict*)
  apply(subgoal_tac "\<exists>q\<delta> y \<beta> z A \<alpha> a \<delta>. y \<in> (cfgSTD_first G' (k- 1) (\<beta>@(liftB z))) \<and> \<lparr>prod_lhs=A,prod_rhs=\<alpha>@(teB a)#\<beta>\<rparr> \<in> cfg_productions G \<and> q\<delta>=last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#\<delta>)) \<and> \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>,cfg_item_rhs2 = (teB a)#\<beta>,cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (teB Do#\<delta>) \<and> lpop=[q\<delta>] \<and> rpop=a#y \<and> lpush=[q\<delta>,F_DFA_GOTO M q\<delta> (teB a)] \<and> rpush=y")
   apply(rename_tac x lpop rpop lpush rpush)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac x lpop rpop lpush rpush)(*strict*)
  apply(erule exE)+
  apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "\<lparr>rule_lpop=[q\<delta>],rule_rpop=a#y,rule_lpush=[q\<delta>,F_DFA_GOTO M q\<delta> (teB a)], rule_rpush=y\<rparr> \<in> (parser_rules P)")
   apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
   prefer 2
   apply(rule X6_3_InformationOnRules_shift1)
             apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
             apply(blast)
            apply(force)
           apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
           apply(blast)
          apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
          apply(blast)
         apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
         apply(blast)
        apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
        apply(blast)
       apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
       apply(blast)
      apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
      apply(blast)
     apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
     apply(blast)
    apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
    apply(blast)
   apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
   apply(blast)
  apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(subgoal_tac "parser_marker P x = Some None")
   apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>!y. ((x,y) \<in> (AF_LR_PARSER__rules G G' M k))")
    apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
    prefer 2
    apply(rule X6_3_InformationOnRules_UniqueEffect)
           apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
           apply(blast)
          apply(force)
         apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
         apply(blast)
        apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
        apply(blast)
       apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
       apply(blast)
      apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
      apply(blast)
     apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
     apply(blast)
    apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
    apply(blast)
   apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
   apply(subgoal_tac "(x, None) \<in> AF_LR_PARSER__rules G G' M k")
    apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
    apply(rule_tac
      t="parser_marker P"
      and s="(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None)"
      in ssubst)
     apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
     apply(simp add: AF_LR_PARSER_def)
     apply(force)
    apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
    apply(subgoal_tac "(THE y. (x, y) \<in> AF_LR_PARSER__rules G G' M k) = None")
     apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
     apply(force)
    apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
    apply(rule HOL.the1_equality)
     apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
     apply(force)
    apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
    apply(force)
   apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
   apply(simp add: AF_LR_PARSER__rules_def)
   apply(force)
  apply(rename_tac x lpop rpop lpush rpush q\<delta> y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(force)
  done

lemma EveryStateFrom_F_LR_MACHINE_in_AF_LR_PARSER_except_two: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> q = last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)
  \<Longrightarrow> q \<noteq> {}
  \<Longrightarrow> w \<notin> {[], [teB Do, teA (cfg_initial G), teB Do]}
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> q \<in> parser_nonterms P"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "q\<noteq>F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))")
   prefer 2
   apply(subgoal_tac "F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))={}")
    apply(force)
   apply(rule ReadInitialIsEmpty)
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
  apply(subgoal_tac "\<forall>e \<in> epda_delta M. edge_trg e \<noteq> epda_initial M")
   prefer 2
   apply(rule ballI)
   apply(rename_tac e)(*strict*)
   apply(case_tac e)
   apply(rename_tac e edge_src edge_event edge_pop edge_push edge_trga)(*strict*)
   apply(rule F_LR_MACHINE_target_not_initial)
          apply(rename_tac e edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
          apply(force)
         apply(rename_tac e edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
         apply(force)
        apply(rename_tac e edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
        apply(force)
       apply(rename_tac e edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
       apply(force)
      apply(rename_tac e edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
      apply(force)
     apply(rename_tac e edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
     apply(force)
    apply(rename_tac e edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
    apply(force)
   apply(force)
  apply(rule_tac
      t="parser_nonterms P"
      and s="(epda_states M)-{epda_initial M,last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G),teB Do]),F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))}"
      in ssubst)
   apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(subgoal_tac "q \<in> epda_states M")
   prefer 2
   apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
    prefer 2
    apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(force)
    apply(force)
   apply(case_tac w)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      t="q"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(rule_tac
      t="q"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="valid_item_set G' k w"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(rule_tac
      t="valid_item_set G' k w"
      and s="(if w=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      in ssubst)
     apply(rename_tac a list)(*strict*)
     apply(rule_tac
      G="G'"
      in F_LR_MACHINE_all_SOUND)
           apply(rename_tac a list)(*strict*)
           apply(force)
          apply(force)
         apply(rename_tac a list)(*strict*)
         apply(force)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(rule two_elements_construct_domain_setA)
      apply(simp add: F_LR_MACHINE_def)
     apply(rename_tac a list)(*strict*)
     apply(rule two_elements_construct_domain_setB)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      t="epda_states M"
      and s="{valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(rule LRM_contains_theEqClasses)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="a#list"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac a list)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac a list)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(subgoal_tac "length w=length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
   prefer 2
   apply(rule_tac
      w="w"
      and q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(force)
   apply(force)
  apply(subgoal_tac "q\<noteq>epda_initial M")
   prefer 2
   apply(case_tac w)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      t="q"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(rule lengthGT)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(subgoal_tac "(\<forall>i<(length w). F_DFA_GOTO M (((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) w))!i) (w!i) = ((F_DFA_GOTO_SEQUENCE M (epda_initial M) w)!i))")
    apply(rename_tac a list)(*strict*)
    prefer 2
    apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main2)
         apply(rename_tac a list)(*strict*)
         apply(force)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(case_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w) = epda_initial M")
    apply(rename_tac a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(erule_tac
      x="length w - Suc 0"
      in allE)
   apply(erule impE)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(subgoal_tac "F_DFA_GOTO M ((epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w) ! (length w - Suc 0)) (w ! (length w - Suc 0)) \<noteq> F_DFA_GOTO_SEQUENCE M (epda_initial M) w ! (length w - Suc 0)")
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) w ! (length w - Suc 0)"
      and s="epda_initial M"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(rule_tac
      P="\<lambda>x. F_DFA_GOTO_SEQUENCE M (epda_initial M) w ! (length w - Suc 0) = x"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(rule sym)
    apply(rule_tac
      t="Suc 0"
      and s="1"
      in ssubst)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(rule_tac
      t="length w"
      and s="length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(rule last_conv_nth)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO M ((epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w) ! (length w - Suc 0)) (w ! (length w - Suc 0))"
      and s="F_VALID_ITEM_SET_GOTO G' F k (w ! (length w - Suc 0)) ((epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w) ! (length w - Suc 0))"
      in subst)
    apply(rename_tac a list)(*strict*)
    apply(rule_tac
      t="M"
      and s="F_LR_MACHINE G' F k"
      in ssubst)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
         apply(rename_tac a list)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(rule_tac
      A="set w"
      in set_mp)
      apply(rename_tac a list)(*strict*)
      apply(simp add: F_LR_MACHINE_def)
     apply(rename_tac a list)(*strict*)
     apply(rule last_nth_in)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(rule_tac
      A="set ((epda_initial (F_LR_MACHINE G' F k) # F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G' F k) (epda_initial (F_LR_MACHINE G' F k)) w))"
      in set_mp)
     apply(rename_tac a list)(*strict*)
     apply(subgoal_tac "set (F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G' F k) (epda_initial (F_LR_MACHINE G' F k)) w) \<subseteq> epda_states (F_LR_MACHINE G' F k)")
      apply(rename_tac a list)(*strict*)
      apply(subgoal_tac "epda_initial (F_LR_MACHINE G' F k) \<in> epda_states(F_LR_MACHINE G' F k)")
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def F_LR_MACHINE_def)
     apply(rename_tac a list)(*strict*)
     apply(rule_tac
      w="w"
      and q="(epda_initial (F_LR_MACHINE G' F k))"
      in F_DFA_GOTO_SEQUENCESound_main3)
          apply(rename_tac a list)(*strict*)
          apply(force)
         apply(rename_tac a list)(*strict*)
         apply(force)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def F_LR_MACHINE_def)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(rule nth_mem)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      t="epda_initial M"
      and s="F_VALID_ITEM_SET_INITIAL G' F k"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac a list)(*strict*)
   apply(rule not_sym)
   apply(rule F_VALID_ITEM_SET_GOTO_does_not_reach_F_LR_MACHINE_initial)
         apply(rename_tac a list)(*strict*)
         apply(force)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule_tac
      s="epda_initial M"
      and t="F_VALID_ITEM_SET_INITIAL G' F k"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac a list)(*strict*)
   apply(subgoal_tac "(epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w) ! (length w - Suc 0) \<in> epda_states M")
    apply(rename_tac a list)(*strict*)
    prefer 2
    apply(rule inSet_from_head_and_rest_nth)
     apply(rename_tac a list)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def F_LR_MACHINE_def)
    apply(rename_tac a list)(*strict*)
    apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in set_mp)
     apply(rename_tac a list)(*strict*)
     apply(rule_tac
      w="w"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main3)
          apply(rename_tac a list)(*strict*)
          apply(force)
         apply(rename_tac a list)(*strict*)
         apply(force)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def F_LR_MACHINE_def)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(subgoal_tac "\<exists>w'. (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w) ! (length w - Suc 0)=valid_item_set G' k w' \<and> set w' \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(rename_tac a list)(*strict*)
    prefer 2
    apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
     apply(rename_tac a list)(*strict*)
     prefer 2
     apply(rule LRM_contains_theEqClasses)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(erule exE)+
   apply(rename_tac a list w')(*strict*)
   apply(rule ballI)
   apply(rename_tac a list w' I)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac a list w' I)(*strict*)
    apply(force)
   apply(rename_tac a list w' I)(*strict*)
   apply(force)
  apply(subgoal_tac "q\<noteq>last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
   prefer 2
   apply(case_tac "q = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
    prefer 2
    apply(force)
   apply(case_tac "length w")
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "w=[teB Do, teA (cfg_initial G), teB Do]")
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac nat)(*strict*)
         apply(force)
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "length [teB Do, teA (cfg_initial G), teB Do] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac nat)(*strict*)
         apply(force)
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac nat)(*strict*)
     apply(rule set_take_head2)
      apply(rename_tac nat)(*strict*)
      apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
     apply(rename_tac nat)(*strict*)
     apply(rule set_take_head2)
      apply(rename_tac nat)(*strict*)
      apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
     apply(rename_tac nat)(*strict*)
     apply(rule set_take_head2)
      apply(rename_tac nat)(*strict*)
      apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule sym)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      q="epda_initial M"
      and M="F_LR_MACHINE G' F k"
      in F_DFA_GOTO_SEQUENCE_injective_rev)
               apply(rename_tac nat)(*strict*)
               apply(force)
              apply(rename_tac nat)(*strict*)
              apply(force)
             apply(rename_tac nat)(*strict*)
             apply(force)
            apply(rename_tac nat)(*strict*)
            apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
           apply(rename_tac nat)(*strict*)
           apply(rule set_take_head2)
            apply(rename_tac nat)(*strict*)
            apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
           apply(rename_tac nat)(*strict*)
           apply(rule set_take_head2)
            apply(rename_tac nat)(*strict*)
            apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
           apply(rename_tac nat)(*strict*)
           apply(rule set_take_head2)
            apply(rename_tac nat)(*strict*)
            apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
           apply(rename_tac nat)(*strict*)
           apply(force)
          apply(rename_tac nat)(*strict*)
          apply(force)
         apply(rename_tac nat)(*strict*)
         apply(force)
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(rule_tac
      t="(F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)"
      and s="M"
      in ssubst)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="q"
      in ssubst)
      apply(rename_tac nat)(*strict*)
      apply(rule_tac
      t="q"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(rule sym)
      apply(rule lengthGT)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule_tac
      t="(F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)"
      and s="M"
      in ssubst)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(rule allI)+
   apply(rename_tac nat q' e1 e2)(*strict*)
   apply(rule impI)
   apply(rule_tac
      q'="q'"
      in uniqueEntryEdgeForReadingDollarInitialDollar)
                apply(rename_tac nat q' e1 e2)(*strict*)
                apply(force)
               apply(rename_tac nat q' e1 e2)(*strict*)
               apply(force)
              apply(rename_tac nat q' e1 e2)(*strict*)
              apply(force)
             apply(rename_tac nat q' e1 e2)(*strict*)
             apply(force)
            apply(rename_tac nat q' e1 e2)(*strict*)
            apply(force)
           apply(rename_tac nat q' e1 e2)(*strict*)
           apply(force)
          apply(rename_tac nat q' e1 e2)(*strict*)
          apply(force)
         apply(rename_tac nat q' e1 e2)(*strict*)
         apply(force)
        apply(rename_tac nat q' e1 e2)(*strict*)
        apply(force)
       apply(rename_tac nat q' e1 e2)(*strict*)
       apply(force)
      apply(rename_tac nat q' e1 e2)(*strict*)
      apply(force)
     apply(rename_tac nat q' e1 e2)(*strict*)
     apply(force)
    apply(rename_tac nat q' e1 e2)(*strict*)
    apply(force)
   apply(force)
  apply(force)
  done

lemma AF_LR_PARSER_in_parser_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> every_state_in_some_accessible_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> cfg_item_lhs I \<in> cfg_nonterminals G
  \<Longrightarrow> q \<in> parser_nonterms P"
  apply(rule_tac
      t="parser_nonterms P"
      and s="(epda_states M)- {epda_initial M, last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G),teB Do]), F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))}"
      in ssubst)
   apply(simp add: AF_LR_PARSER_def)
  apply(subgoal_tac "q\<noteq>epda_initial M")
   apply(subgoal_tac "q\<noteq>last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
    apply(subgoal_tac "q\<noteq>F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))")
     apply(force)
    apply(thin_tac "q \<noteq> epda_initial M")
    apply(thin_tac "q \<noteq> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
    apply(case_tac "q = F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))")
     apply(subgoal_tac "q={}")
      apply(force)
     apply(rule ReadInitialIsEmpty)
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
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])"
      in ssubst)
    apply(subgoal_tac "length [teB Do, teA (cfg_initial G), teB Do] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
     prefer 2
     apply(rule_tac
      w="[teB Do, teA (cfg_initial G), teB Do]"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
     apply(force)
    apply(force)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])"
      and s="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do,teA (cfg_initial G), teB Do],cfg_item_rhs2=[],cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
    apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_3)
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
   apply(subgoal_tac "I\<notin>{\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2 = [], cfg_item_look_ahead = []\<rparr>}")
    prefer 2
    apply(clarsimp)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(force)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(force)
  apply(rule_tac
      s="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [])))"
      and t="epda_initial M"
      in ssubst)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) []"
      and s="[]"
      in ssubst)
    apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
     prefer 2
     apply(rule_tac
      w="[]"
      and q="(epda_initial (F_LR_MACHINE G' F k))"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
   prefer 2
   apply(rule_tac
      w="[]"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
   apply(force)
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [])"
      and s="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[],cfg_item_rhs2=[teB Do,teA (cfg_initial G), teB Do],cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
   apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_0)
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
  apply(subgoal_tac "I\<notin>{\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}")
   prefer 2
   apply(clarsimp)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    apply(force)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(force)
  done

lemma AF_LR_PARSER_valid_parser_finite_parser_events: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> finite (parser_events P)"
  apply(simp add: AF_LR_PARSER_def valid_cfg_def F_CFG_AUGMENT_def)
  done

lemma AF_LR_PARSER_valid_parser_finite_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> finite (parser_nonterms P)"
  apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  done

lemma AF_LR_PARSER_valid_parser_parser_initial_in_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> parser_initial P \<in> parser_nonterms P"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="parser_initial P"
      and s="F_DFA_GOTO M (epda_initial M) (teB Do)"
      in ssubst)
   apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule_tac
      w="[teB Do]"
      in EveryStateFrom_F_LR_MACHINE_in_AF_LR_PARSER_except_two)
               apply(force)+
     apply(rule sym)
     apply(rule F_DFA_GOTO_SEQUENCE_length_last)
            apply(force)+
        apply(rule valid_epda_initial_in_states)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
       apply(force)+
     apply(rule F_LR_MACHINE_Do_in_cfg_events)
          apply(force)+
    apply(subgoal_tac "\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do],cfg_item_rhs2=[teA (cfg_initial G), teB Do],cfg_item_look_ahead=[]\<rparr> \<in> F_DFA_GOTO M (epda_initial M) (teB Do)")
     prefer 2
     apply(rule_tac
      t="F_DFA_GOTO M (epda_initial M) (teB Do)"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in subst)
      apply(rule F_DFA_GOTO_SEQUENCE_length_last)
             apply(force)+
         apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
         apply(rule valid_epda_initial_in_states)
         apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
        apply(force)+
      apply(rule F_LR_MACHINE_Do_in_cfg_events)
           apply(force)+
     apply(rule_tac
      A="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      in set_mp)
      apply(force)
     apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      and s="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do],cfg_item_rhs2=[teA (cfg_initial G), teB Do],cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
      apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_1)
                apply(force)+
  apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
  done

lemma AF_LR_PARSER_valid_parser_parser_marking_in_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> parser_marking P \<subseteq> parser_nonterms P"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="parser_marking P"
      and s="{last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])}"
      in ssubst)
   apply(simp add: AF_LR_PARSER_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<in> parser_nonterms P")
   apply(force)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="last (epda_initial M #F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in subst)
   apply(rule F_DFA_GOTO_SEQUENCE_length_last2)
            apply(force)+
        apply(rule valid_epda_initial_in_states)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
       apply(force)+
   apply(rule F_LR_MACHINE_DoS_in_cfg_events)
        apply(force)+
  apply(rule_tac
      w="[teB Do,teA (cfg_initial G)]"
      in EveryStateFrom_F_LR_MACHINE_in_AF_LR_PARSER_except_two)
               apply(force)+
    apply(subgoal_tac "\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do,teA (cfg_initial G)],cfg_item_rhs2=[teB Do],cfg_item_look_ahead=[]\<rparr> \<in> last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
     apply(force)
    apply(rule_tac
      A="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      in set_mp)
     apply(force)
    apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      and s="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do,teA (cfg_initial G)],cfg_item_rhs2=[teB Do],cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
     apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_2)
               apply(force)+
  apply(rule F_LR_MACHINE_DoS_in_cfg_events)
       apply(force)+
  done

lemma AF_LR_PARSER_valid_parser_rules_are_parserrules: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> (e, v) \<in> AF_LR_PARSER__rules G G' M k
  \<Longrightarrow> valid_parser_step_label P e"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>maxl. \<forall>q \<in> (epda_states M). \<forall>I \<in> q. length (cfg_item_rhs1 I @ cfg_item_rhs2 I)\<le>maxl")
   prefer 2
   apply(subgoal_tac "\<exists>maxl. \<forall>I \<in> {I. \<exists>q. I \<in> q \<and> q \<in> (epda_states M)}. (\<lambda>I. length (cfg_item_rhs1 I @ cfg_item_rhs2 I)) I \<le>maxl")
    prefer 2
    apply(rule_tac
      f="(\<lambda>I. length (cfg_item_rhs1 I @ cfg_item_rhs2 I))"
      in finite_has_max)
    apply(rule_tac
      t="{I. \<exists>q. I \<in> q \<and> q \<in> epda_states M}"
      and s="\<Union>{(\<lambda>x. x)S|S. S \<in> epda_states M}"
      in ssubst)
     apply(force)
    apply(rule finite_big_union)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rule ballI)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      G="G'"
      in F_LR_MACHINE_has_finite_states)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(erule exE)
   apply(rename_tac maxl)(*strict*)
   apply(rule_tac
      x="maxl"
      in exI)
   apply(force)
  apply(erule exE)
  apply(rename_tac maxl)(*strict*)
  apply(unfold valid_parser_step_label_def)
  apply(rename_tac maxl)(*strict*)
  apply(subgoal_tac " (\<exists>q q_seq I y qA. (e,v)=(\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>) \<and> q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> cfg_item_rhs1 I = [] \<and> qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I)) \<and> q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) \<and> \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> \<in> last (q # q_seq)) \<or> (\<exists>q a y qA. (e,v)=(\<lparr>rule_lpop = [q], rule_rpop = a # y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, None) \<and> q \<in> epda_states M \<and> (\<exists>I \<in> q. \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> [teB a] = take (Suc 0) (cfg_item_rhs2 I) \<and> qA \<in> F_EPDA_GOTO M q (teB a) \<and> y \<in> cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))))")
   apply(rename_tac maxl)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER__rules_def)
  apply(rename_tac maxl)(*strict*)
  apply(erule disjE)
   apply(rename_tac maxl)(*strict*)
   apply(erule exE)+
   apply(rename_tac maxl q q_seq I y qA)(*strict*)
   apply(erule conjE)+
   apply(subgoal_tac "\<exists>w. q=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(rename_tac maxl q q_seq I y qA)(*strict*)
    prefer 2
    apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
     apply(rename_tac maxl q q_seq I y qA)(*strict*)
     prefer 2
     apply(rule "LRM_contains_theEqClasses")
       apply(rename_tac maxl q q_seq I y qA)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA)(*strict*)
   apply(erule exE)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "valid_item G' k I")
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(rule_tac
      q="q"
      in F_LR_MACHINE_States_contain_Items)
        apply(rename_tac maxl q q_seq I y qA w)(*strict*)
        apply(force,force,force,force,force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      and q="q"
      in F_LR_MACHINE_item_in_state_rhs2_in_cfg_events)
        apply(rename_tac maxl q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "teA (cfg_item_lhs I) \<in> epda_events M")
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      in F_LR_MACHINE_item_in_state_lhs_in_cfg_events)
       apply(rename_tac maxl q q_seq I y qA w)(*strict*)
       apply(force)
      apply(force)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "q_seq=F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(subgoal_tac "{F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)} = F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     prefer 2
     apply(rule F_DFA_GOTO_SEQUENCE_to_F_EPDA_GOTO_SEQUENCE)
         apply(rename_tac maxl q q_seq I y qA w)(*strict*)
         apply(force,force,force,force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(thin_tac "q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
   apply(subgoal_tac "[qA]=F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]")
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]"
      and s="[F_DFA_GOTO M q (teA (cfg_item_lhs I))]"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(rename_tac maxl q q_seq I y qA w)(*strict*)
         apply(force,force,force,force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(subgoal_tac "{F_DFA_GOTO M q (teA (cfg_item_lhs I))} = F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     prefer 2
     apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
         apply(rename_tac maxl q q_seq I y qA w)(*strict*)
         apply(force,force,force,force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(blast)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(thin_tac "qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
   apply(erule_tac
      x="q"
      in ballE)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(erule_tac
      x="I"
      in ballE)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "valid_item G' k \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr>")
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(case_tac q_seq)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(rule Fact6_12__2)
      apply(rename_tac maxl q q_seq I y qA w)(*strict*)
      apply(force,force)
    apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
    apply(subgoal_tac "(last q_seq) \<in> epda_states M")
     apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
     prefer 2
     apply(rule_tac
      A="set q_seq"
      in set_mp)
      apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
      apply(rule_tac
      q="q"
      in F_DFA_GOTO_SEQUENCESound_main3)
           apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
           apply(force,force,force,force,force)
      apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
    apply(subgoal_tac "\<exists>w. (last q_seq)=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
     apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
     prefer 2
     apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
      apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
      prefer 2
      apply(rule LRM_contains_theEqClasses)
        apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
        apply(force,force,force)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
    apply(erule exE)
    apply(rename_tac maxl q q_seq I y qA w a list wa)(*strict*)
    apply(rule Fact6_12__2)
     apply(rename_tac maxl q q_seq I y qA w a list wa)(*strict*)
     apply(force,force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(rule_tac
      t="parser_events P"
      and s="cfg_events G'"
      in ssubst)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(simp add: AF_LR_PARSER_def F_CFG_AUGMENT_def)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "length (cfg_item_rhs2 I)=length q_seq")
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac maxl q q_seq I y qA w)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(rule conjI)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      t="rule_rpop e"
      and s="y"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      x="k"
      in exI)
    apply(rule_tac
      t="y"
      and s="cfg_item_look_ahead (\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr>)"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      t="parser_bottom P"
      and s="Do"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(simp add: AF_LR_PARSER_def)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      t="cfg_events G' - {Do}"
      and s="cfg_events G"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(rule F_CFG_AUGMENT__cfg_events)
        apply(rename_tac maxl q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      q="last (q # q_seq)"
      in DollarTailStays_notS_prime)
             apply(rename_tac maxl q q_seq I y qA w)(*strict*)
             apply(force)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w)(*strict*)
      apply(case_tac "q_seq")
       apply(rename_tac maxl q q_seq I y qA w)(*strict*)
       apply(rule_tac
      t="last (q#q_seq)"
      and s="q"
      in ssubst)
        apply(rename_tac maxl q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
      apply(rule_tac
      t="last (q#q_seq)"
      and s="last(q_seq)"
      in ssubst)
       apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
      apply(rule DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
            apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w a list)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      t="cfg_item_lhs \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> "
      and s="cfg_item_lhs I"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      A="cfg_nonterminals G"
      in distinct_by_set_membership)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(rule CFGprod_lhs_in_nonterms)
       apply(rename_tac maxl q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(rule conjI)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      t="rule_rpush e"
      and s="y"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      I="\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr>"
      in Item_la_in_CFG)
      apply(rename_tac maxl q q_seq I y qA w)(*strict*)
      apply(force,force,force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(subgoal_tac "valid_item_set G' k w \<in> parser_nonterms P")
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    prefer 2
    apply(rule AF_LR_PARSER_in_parser_nonterms)
                 apply(rename_tac maxl q q_seq I y qA w)(*strict*)
                 apply(force,force,force,force,force,force,force,force,force,force,force)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule prod_lhs_in_nonterms2)
      apply(rename_tac maxl q q_seq I y qA w)(*strict*)
      apply(force,force,force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(rule conjI)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule_tac
      t="rule_lpop e"
      and s="q # q_seq"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule set_subset_by_nth_elem)
    apply(rule allI)
    apply(rename_tac maxl q q_seq I y qA w i)(*strict*)
    apply(rule impI)
    apply(case_tac i)
     apply(rename_tac maxl q q_seq I y qA w i)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(subgoal_tac "length (cfg_item_rhs2 I) = length (F_DFA_GOTO_SEQUENCE M (valid_item_set G' k w) (cfg_item_rhs2 I))")
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     prefer 2
     apply(rule_tac
      q="(valid_item_set G' k w)"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     prefer 2
     apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(simp only: valid_cfg_def)
      apply(erule conjE)+
      apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. valid_cfg_step_label G p"
      in ballE)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(clarsimp)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(clarsimp)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in subset_trans)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
      apply(clarsimp)
      apply(rename_tac maxl I y qA w nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(subgoal_tac "length (take i (cfg_item_rhs2 I)) = length (F_DFA_GOTO_SEQUENCE M (valid_item_set G' k w) (take i (cfg_item_rhs2 I)))")
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     prefer 2
     apply(rule_tac
      q="(valid_item_set G' k w)"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(rule_tac
      B="set (cfg_item_rhs2 I)"
      in subset_trans)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(rule List.set_take_subset)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(rule_tac
      t="(q#q_seq) ! i"
      and s="(F_DFA_GOTO_SEQUENCE M (valid_item_set G' k w) (cfg_item_rhs2 I)) ! nat"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (valid_item_set G' k w) (cfg_item_rhs2 I) ! nat"
      and s="last (F_DFA_GOTO_SEQUENCE M (valid_item_set G' k w) (take (Suc nat) (cfg_item_rhs2 I)))"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE)
          apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(simp add: F_LR_MACHINE_def)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule Item_rhs2_in_CFG)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(rule_tac
      G="G"
      and I="I \<lparr>cfg_item_rhs1 := cfg_item_rhs1 I @ take (Suc nat) (cfg_item_rhs2 I), cfg_item_rhs2 := drop (Suc nat) (cfg_item_rhs2 I)\<rparr>"
      in AF_LR_PARSER_in_parser_nonterms)
                 apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
                 apply(force)
                apply(force)
               apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
               apply(force)
              apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
              apply(force)
             apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
             apply(force)
            apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(rule_tac
      ?q0.0="(valid_item_set G' k w)"
      and w="(take (Suc nat) (cfg_item_rhs2 I))"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
            apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(rule_tac
      B="set (cfg_item_rhs2 I)"
      in subset_trans)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(rule List.set_take_subset)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule_tac
      n="Suc nat"
      and I="I"
      and q="(valid_item_set G' k w)"
      in F_LR_MACHINE_shifted_item_in_next_states)
                  apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
                  apply(force)
                 apply(force)
                apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
                apply(force)
               apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
               apply(force)
              apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
              apply(force)
             apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
             apply(force)
            apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(simp add: valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      in ballE)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w)(*strict*)
   apply(rule conjI)
    apply(rename_tac maxl q q_seq I y qA w)(*strict*)
    apply(rule set_subset_by_nth_elem)
    apply(rule allI)
    apply(rename_tac maxl q q_seq I y qA w i)(*strict*)
    apply(rule impI)
    apply(case_tac i)
     apply(rename_tac maxl q q_seq I y qA w i)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(subgoal_tac "length [teA (cfg_item_lhs I)] = length (F_DFA_GOTO_SEQUENCE M (valid_item_set G' k w) [teA (cfg_item_lhs I)])")
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     prefer 2
     apply(rule_tac
      q="valid_item_set G' k w"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(case_tac nat)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     prefer 2
     apply(rename_tac maxl q q_seq I y qA w i nat nata)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(rule_tac
      t="rule_lpush e ! i"
      and s="qA"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule_tac
      t="rule_lpush e ! i"
      and s="[q,qA] ! i"
      in ssubst)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule_tac
      t="i"
      and s="Suc 0"
      in ssubst)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule second_of_two)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(rule_tac
      t="qA"
      and s="F_DFA_GOTO M q (teA (cfg_item_lhs I))"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(rule_tac
      x="qA"
      and y="F_DFA_GOTO M q (teA (cfg_item_lhs I))"
      in Cons_inj)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(rule_tac
      t="[F_DFA_GOTO M q (teA (cfg_item_lhs I))]"
      and s="F_DFA_GOTO_SEQUENCE M q [teA (cfg_item_lhs I)]"
      in subst)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
            apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(subgoal_tac "\<exists>n. I \<in> valid_item_set_n G' k n w")
     apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
     prefer 2
     apply(rule valid_item_set_n_subset_valid_item_set_rev)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat)(*strict*)
    apply(erule exE)+
    apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
    apply(subgoal_tac "\<exists>p \<in> (cfg_productions G'). \<exists>A \<alpha> \<beta>. p=\<lparr>prod_lhs=A,prod_rhs=\<alpha>@[teA (cfg_item_lhs I)]@\<beta>\<rparr> \<and> (\<exists>y v. setA v={} \<and> (\<exists>m<n. \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>,cfg_item_rhs2 = [teA (cfg_item_lhs I)]@\<beta>,cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G' k m w \<and> (\<exists>d e. cfgRM.derivation G' d \<and> maximum_of_domain d (n-m- 1) \<and> d 0 = Some (pair None \<lparr>cfg_conf=\<beta>\<rparr>) \<and> d (n-m- 1) = Some (pair e \<lparr>cfg_conf=v\<rparr>)) \<and> take k ((filterB v)@y) = (cfg_item_look_ahead I)))")
     apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
     prefer 2
     apply(rule_tac
      w="cfg_item_rhs2 I"
      in Lemma6_19)
       apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
      apply(case_tac n)
       apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
       apply(subgoal_tac "False")
        apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
       apply(subgoal_tac "I \<in> {I. \<exists>p \<in> cfg_productions G'. \<exists>w'. prod_lhs p=cfg_initial G' \<and> cfg_item_lhs I=cfg_initial G' \<and> (cfg_item_rhs1 I=w) \<and> cfg_item_rhs2 I = w' \<and> cfg_item_look_ahead I = [] \<and> (prod_rhs p=(w@w'))}")
        apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
        prefer 2
        apply(rule_tac
      t="{I. \<exists>p \<in> cfg_productions G'. \<exists>w'. prod_lhs p = cfg_initial G' \<and> cfg_item_lhs I = cfg_initial G' \<and> cfg_item_rhs1 I = w \<and> cfg_item_rhs2 I = w' \<and> cfg_item_look_ahead I = [] \<and> prod_rhs p = w @ w'}"
      and s="valid_item_set_n G' k 0 w"
      in ssubst)
         apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
         apply(rule sym)
         apply(rule Fact6_20)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
       apply(subgoal_tac "\<exists>p \<in> cfg_productions G'. \<exists>w'. prod_lhs p = cfg_initial G' \<and> cfg_item_lhs I = cfg_initial G' \<and> cfg_item_rhs1 I = w \<and> cfg_item_rhs2 I = w' \<and> cfg_item_look_ahead I = [] \<and> prod_rhs p = w @ w'")
        apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
       apply(erule bexE)+
       apply(rename_tac maxl q q_seq I y qA w i nat n p)(*strict*)
       apply(erule exE)+
       apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
       apply(erule conjE)+
       apply(subgoal_tac "cfg_item_lhs I \<in> cfg_nonterminals G")
        apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
        prefer 2
        apply(rule CFGprod_lhs_in_nonterms)
          apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
       apply(subgoal_tac "cfg_initial G' \<notin> cfg_nonterminals G")
        apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
        prefer 2
        apply(rule F_CFG_AUGMENT__initial_not_in_nonterms)
           apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p w')(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n nata)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
     apply(rule_tac
      t="\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = [], cfg_item_rhs2 = cfg_item_rhs2 I, cfg_item_look_ahead = cfg_item_look_ahead I\<rparr>"
      and s="I"
      in ssubst)
      apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
    apply(rule_tac
      t="q"
      and s="valid_item_set G' k w"
      in ssubst)
     apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n)(*strict*)
    apply(erule bexE)
    apply(rename_tac maxl q q_seq I y qA w i nat n p)(*strict*)
    apply(erule exE)+
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta>)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(erule conjE)+
    apply(case_tac "A \<in> cfg_nonterminals G")
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(rule_tac
      G="G"
      and I="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>@[teA (cfg_item_lhs I)], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = ya\<rparr>"
      in AF_LR_PARSER_in_parser_nonterms)
                  apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
                  apply(force)
                 apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
                 apply(force)
                apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
                apply(force)
               apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
               apply(force)
              apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
              apply(force)
             apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
             apply(force)
            apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(rule_tac
      t="F_LR_MACHINE
             (F_CFG_AUGMENT G
               (F_FRESH (cfg_nonterminals G))
               (F_FRESH (cfg_events G))) F
             k"
      and s="M"
      in ssubst)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(rule_tac
      ?q0.0="q"
      in DFA_F_DFA_GOTO_in_states)
            apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(subgoal_tac "cfg_item_lhs I \<in> cfg_nonterminals G'")
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       prefer 2
       apply(rule Item_lhs_in_CFG)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(rule_tac
      t="F_DFA_GOTO M (valid_item_set G' k w) (teA (cfg_item_lhs I))"
      and s="valid_item_set G' k (w@[teA (cfg_item_lhs I)])"
      in ssubst)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(rule_tac
      t="F_DFA_GOTO M (valid_item_set G' k w) (teA (cfg_item_lhs I))"
      and s="F_VALID_ITEM_SET_GOTO G' F k (teA (cfg_item_lhs I)) (valid_item_set G' k w)"
      in ssubst)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(rule sym)
        apply(rule_tac
      t="M"
      and s="F_LR_MACHINE G' F k"
      in ssubst)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
             apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
             apply(force)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(simp add: two_elements_construct_domain_def)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(rule sym)
       apply(rule Lemma6__26)
          apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
          apply(force)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(rule two_elements_construct_domain_setA)
        apply(rule set_concat_subset)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(simp add: two_elements_construct_domain_def)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(rule two_elements_construct_domain_setB)
       apply(rule set_concat_subset)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(simp add: two_elements_construct_domain_def)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(rule valid_item_set_n_subset_valid_item_set)
      apply(rule Lemma6__24_2)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(subgoal_tac "A=S'")
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     prefer 2
     apply(subgoal_tac "A \<in> cfg_nonterminals G'")
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(erule conjE)+
     apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = \<alpha> @ [teA (cfg_item_lhs I)] @ \<beta>\<rparr>"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      in ballE)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(subgoal_tac "p=\<lparr>prod_lhs=S',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>")
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     prefer 2
     apply(simp add: valid_cfg_def)
     apply(erule conjE)+
     apply(erule_tac
      x="p"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      in ballE)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(clarsimp)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(simp add: F_CFG_AUGMENT_def)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(subgoal_tac "\<alpha>=[teB Do] \<and> \<beta>=[teB Do] \<and> cfg_item_lhs I=cfg_initial G")
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     prefer 2
     apply(rule match3)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(erule conjE)+
    apply(subgoal_tac "w=[teB Do] \<and> ya=[]")
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     prefer 2
     apply(rule_tac
      G="G"
      and G'="G'"
      and Do="Do"
      and S'="S'"
      and k="k"
      in DollarReadItem_OnlyIn_Specific_Valid)
           apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(rule valid_item_set_n_subset_valid_item_set)
   apply(rule_tac
    t="\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = ya\<rparr>"
    and s="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = [teA (cfg_item_lhs I)] @ \<beta>, cfg_item_look_ahead = ya\<rparr>"
    in ssubst)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(force)
  apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO M (valid_item_set G' k w) (teA (cfg_item_lhs I))"
    and s="valid_item_set G' k [teB Do,teA (cfg_initial G)]"
    in ssubst)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(rule_tac
    t="F_DFA_GOTO M (valid_item_set G' k w) (teA (cfg_item_lhs I))"
    and s="F_VALID_ITEM_SET_GOTO G' F k (teA (cfg_item_lhs I)) (valid_item_set G' k w)"
    in ssubst)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(rule sym)
    apply(rule_tac
    t="M"
    and s="F_LR_MACHINE G' F k"
    in ssubst)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(rule sym)
   apply(rule_tac
    t="[teB Do, teA (cfg_initial G)]"
    and s="[teB Do]@[teA (cfg_item_lhs I)]"
    in ssubst)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(rule_tac
    t="w"
    and s="[teB Do]"
    in ssubst)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(rule Lemma6__26)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(rule set_concat_subset)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(rule set_concat_subset)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(force)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
  apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
  apply(rule_tac
    t="valid_item_set G' k [teB Do, teA (cfg_initial G)]"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
    in ssubst)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
          apply(force)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(force)
  apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
  apply(subgoal_tac "length [teB Do, teA (cfg_initial G)] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   prefer 2
   apply(rule_tac
    M="M"
    and q="epda_initial M"
    in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(force)
  apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
  apply(rule_tac
    t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
    and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
    in ssubst)
   apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
   apply(force)
  apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
  apply(rule_tac
    w="[teB Do, teA (cfg_initial G)]"
    and G'="G'"
    and G="G"
    and Do="Do"
    and S'="S'"
    in EveryStateFrom_F_LR_MACHINE_in_AF_LR_PARSER_except_two)
               apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
               apply(force)
              apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
              apply(force)
             apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
             apply(force)
            apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(subgoal_tac "{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do,teA (cfg_initial G)],cfg_item_rhs2=[teB Do],cfg_item_look_ahead=[]\<rparr>} \<subseteq> last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(rule_tac
    t="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do,teA (cfg_initial G)],cfg_item_rhs2=[teB Do],cfg_item_look_ahead=[]\<rparr>}"
    and s="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])))-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
    in subst)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_2)
               apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
               apply(force)
              apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
              apply(force)
             apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
             apply(force)
            apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
            apply(force)
           apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
           apply(force)
          apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
          apply(force)
         apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
         apply(force)
        apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
        apply(force)
       apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
       apply(force)
      apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
      apply(force)
     apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
     apply(force)
    apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac maxl q q_seq I y qA w i nat n p A \<alpha> \<beta> ya va m d ea)(*strict*)
  apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def)
  apply(rename_tac maxl q q_seq I y qA w)(*strict*)
  apply(rule conjI)
  apply(rename_tac maxl q q_seq I y qA w)(*strict*)
  apply(force)
  apply(rename_tac maxl q q_seq I y qA w)(*strict*)
  apply(rule conjI)
  apply(rename_tac maxl q q_seq I y qA w)(*strict*)
  apply(force)
  apply(rename_tac maxl q q_seq I y qA w)(*strict*)
  apply(rule conjI)
  apply(rename_tac maxl q q_seq I y qA w)(*strict*)
  apply(rule_tac
    x="[]"
    in exI)
  apply(force)
  apply(rename_tac maxl q q_seq I y qA w)(*strict*)
  apply(rule impI)
  apply(erule exE)+
  apply(rename_tac maxl q q_seq I y qA w x)(*strict*)
  apply(rule_tac
    x="x"
    in exI)
  apply(clarsimp)
  apply(rename_tac maxl)(*strict*)
  apply(erule exE)+
  apply(rename_tac maxl q a y qA)(*strict*)
  apply(erule conjE)+
  apply(erule bexE)+
  apply(rename_tac maxl q a y qA I)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "\<exists>w. q=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
  apply(rename_tac maxl q a y qA I)(*strict*)
  prefer 2
  apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
  apply(rename_tac maxl q a y qA I)(*strict*)
  prefer 2
  apply(rule LRM_contains_theEqClasses)
    apply(rename_tac maxl q a y qA I)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac maxl q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I)(*strict*)
  apply(erule exE)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "valid_item G' k I")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    q="q"
    in F_LR_MACHINE_States_contain_Items)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    G="G'"
    and q="q"
    in F_LR_MACHINE_item_in_state_rhs2_in_cfg_events)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "teA (cfg_item_lhs I) \<in> epda_events M")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    G="G'"
    in F_LR_MACHINE_item_in_state_lhs_in_cfg_events)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "[qA]=F_DFA_GOTO_SEQUENCE M q [teB a]")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M q [teB a]"
    and s="[F_DFA_GOTO M q (teB a)]"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
      apply(rename_tac maxl q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    A="set (cfg_item_rhs2 I)"
    in set_mp)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(clarsimp)
  apply(rename_tac maxl a y qA I w)(*strict*)
  apply(rule head_in_set2)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "{F_DFA_GOTO M q (teB a)} = F_EPDA_GOTO M q (teB a)")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
      apply(rename_tac maxl q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    A="set (cfg_item_rhs2 I)"
    in set_mp)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(clarsimp)
  apply(rename_tac maxl a y qA I w)(*strict*)
  apply(rule head_in_set2)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule listEqI1)
  apply(blast)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(thin_tac "qA \<in> F_EPDA_GOTO M q (teB a)")
  apply(erule_tac
    x="q"
    in ballE)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(erule_tac
    x="I"
    in ballE)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "a \<in> parser_events P")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    t="parser_events P"
    and s="cfg_events G'"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: AF_LR_PARSER_def)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    A="setB (cfg_item_rhs2 I)"
    in set_mp)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule two_elements_construct_domain_setB)
  apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_def F_CFG_AUGMENT_def)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    A="setB (take (Suc 0) (cfg_item_rhs2 I))"
    in set_mp)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule setBTakeIndexSubset2)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="(take (Suc 0) (cfg_item_rhs2 I))"
    and s="teB a#[]"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(clarsimp)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(thin_tac "[teB a] = take (Suc 0) (cfg_item_rhs2 I)")
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "a \<in> cfg_events G")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    A="setB [teB a]"
    in set_mp)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="[teB a]"
    and s="(take (Suc 0) (cfg_item_rhs2 I))"
    in ssubst)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="setB (cfg_item_rhs2 I)"
    in subset_trans)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule setBTakeIndexSubset2)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="setB (cfg_item_rhs1 I @ cfg_item_rhs2 I)"
    in subset_trans)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(simp (no_asm) only: setBConcat concat_asso)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule prod_rhs_in_cfg_events)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule setB_triv)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "q \<in> parser_nonterms P")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule AF_LR_PARSER_in_parser_nonterms)
              apply(rename_tac maxl q a y qA I w)(*strict*)
              apply(force)
             apply(rename_tac maxl q a y qA I w)(*strict*)
             apply(force)
            apply(rename_tac maxl q a y qA I w)(*strict*)
            apply(force)
           apply(rename_tac maxl q a y qA I w)(*strict*)
           apply(force)
          apply(rename_tac maxl q a y qA I w)(*strict*)
          apply(force)
         apply(rename_tac maxl q a y qA I w)(*strict*)
         apply(force)
        apply(rename_tac maxl q a y qA I w)(*strict*)
        apply(force)
       apply(rename_tac maxl q a y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(erule conjE)+
  apply(erule_tac
    x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>"
    and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
    in ballE)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "qA \<in> parser_nonterms P")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(subgoal_tac "teB a \<in> epda_events M")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    A="set (cfg_item_rhs2 I)"
    in set_mp)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule Item_rhs2_in_CFG)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    w'="drop (Suc 0) (cfg_item_rhs2 I)"
    in head_in_set)
  apply(rule_tac
    t="teB a # drop (Suc 0) (cfg_item_rhs2 I)"
    and s="take (Suc 0) (cfg_item_rhs2 I) @ drop (Suc 0) (cfg_item_rhs2 I)"
    in ssubst)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule_tac
    t="take (Suc 0) (cfg_item_rhs2 I)"
    and s="[teB a]"
    in ssubst)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(thin_tac "[teB a] = take (Suc 0) (cfg_item_rhs2 I)")
   apply(simp (no_asm_simp))
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "[qA] = [F_DFA_GOTO M q (teB a)]")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    t="[F_DFA_GOTO M q (teB a)]"
    and s="F_DFA_GOTO_SEQUENCE M q [(teB a)]"
    in ssubst)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule sym)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(rename_tac maxl q a y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="qA"
    and s="F_DFA_GOTO M q (teB a)"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    I="\<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs1 I @ [teB a],cfg_item_rhs2=drop (Suc 0) (cfg_item_rhs2 I),cfg_item_look_ahead=cfg_item_look_ahead I\<rparr>"
    in AF_LR_PARSER_in_parser_nonterms)
              apply(rename_tac maxl q a y qA I w)(*strict*)
              apply(force,force,force,force,force,force,force,force,force)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule_tac
    X="teB a"
    and ?q0.0="q"
    in DFA_F_DFA_GOTO_in_states)
        apply(rename_tac maxl q a y qA I w)(*strict*)
        apply(force,force,force,force,force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(rule_tac
    t="cfg_item_lhs \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs1 I @ [teB a], cfg_item_rhs2 = drop (Suc 0) (cfg_item_rhs2 I), cfg_item_look_ahead = cfg_item_look_ahead I\<rparr>"
    and s="cfg_item_lhs I"
    in ssubst)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule CFGprod_lhs_in_nonterms)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="q"
    and s="valid_item_set G' k w"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO M (valid_item_set G' k w) (teB a)"
    and s="F_VALID_ITEM_SET_GOTO G' F k (teB a) (valid_item_set G' k w)"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule sym)
  apply(rule_tac
    t="M"
    and s="F_LR_MACHINE G' F k"
    in ssubst)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
       apply(rename_tac maxl q a y qA I w)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(simp add: two_elements_construct_domain_def F_LR_MACHINE_def)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="F_VALID_ITEM_SET_GOTO G' F k (teB a) (valid_item_set G' k w)"
    and s="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis (teB a) (valid_item_set G' k w))"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO_def)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    A="F_VALID_ITEM_SET_GOTO__basis (teB a) (valid_item_set G' k w)"
    in set_mp)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
   apply(rule subsetI)
   apply(rename_tac maxl q a y qA I w x)(*strict*)
   apply(subgoal_tac "valid_item G' k x")
    apply(rename_tac maxl q a y qA I w x)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w x)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac maxl q a y qA I w x)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w x)(*strict*)
   apply(force)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "\<exists>I1 \<in> (valid_item_set G' k w). F_VALID_ITEM_SET_GOTO__passes (teB a) I1 \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs1 I @ [teB a], cfg_item_rhs2 = drop (Suc 0) (cfg_item_rhs2 I), cfg_item_look_ahead = cfg_item_look_ahead I\<rparr>")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    x="I"
    in bexI)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "cfg_item_rhs2 I = teB a # drop (Suc 0) (cfg_item_rhs2 I)")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="teB a # drop (Suc 0) (cfg_item_rhs2 I)"
    and s="[teB a] @ drop (Suc 0) (cfg_item_rhs2 I)"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(thin_tac "[teB a] = take (Suc 0) (cfg_item_rhs2 I)")
  apply(simp (no_asm_simp))
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="[teB a]"
    and s="take (Suc 0) (cfg_item_rhs2 I)"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "set y \<subseteq> parser_events P")
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule conjI)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "y \<in> (kPrefix (k - 1)) ` append_language (cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I))) {cfg_item_look_ahead I}")
   apply(rename_tac maxl q a y qA I w)(*strict*)
   prefer 2
   apply(rule_tac
    t="(kPrefix (k - 1)) ` append_language (cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I))) {cfg_item_look_ahead I}"
    and s="cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))"
    in ssubst)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(rule cfgSTD_first_pull_out_terimal_tail_string)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(subgoal_tac "setA (drop (Suc 0) (cfg_item_rhs2 I)) \<subseteq> cfg_nonterminals G")
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(subgoal_tac "setB (drop (Suc 0) (cfg_item_rhs2 I)) \<subseteq> cfg_events G")
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(subgoal_tac "y \<in> (kPrefix (k - 1)) ` append_language (cfgSTD_first G (k - 1) (drop (Suc 0) (cfg_item_rhs2 I))) {cfg_item_look_ahead I}")
     apply(rename_tac maxl q a y qA I w)(*strict*)
     prefer 2
     apply(rule_tac
    t="cfgSTD_first G (k - 1) (drop (Suc 0) (cfg_item_rhs2 I))"
    and s="cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I))"
    in ssubst)
      apply(rename_tac maxl q a y qA I w)(*strict*)
      apply(rule cfgSTD_first_F_CFG_AUGMENT__no_change_on_old_input)
            apply(rename_tac maxl q a y qA I w)(*strict*)
            apply(force)
           apply(rename_tac maxl q a y qA I w)(*strict*)
           apply(force)
          apply(rename_tac maxl q a y qA I w)(*strict*)
          apply(force)
         apply(rename_tac maxl q a y qA I w)(*strict*)
         apply(force)
        apply(rename_tac maxl q a y qA I w)(*strict*)
        apply(force)
       apply(rename_tac maxl q a y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(thin_tac "y \<in> cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))")
    apply(thin_tac "y \<in> kPrefix (k - 1) ` append_language(cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I))) {cfg_item_look_ahead I}")
    apply(subgoal_tac "\<exists>x \<in> append_language(cfgSTD_first G (k - 1) (drop (Suc 0) (cfg_item_rhs2 I))) {cfg_item_look_ahead I}. (kPrefix (k - 1)) x = y")
     apply(rename_tac maxl q a y qA I w)(*strict*)
     prefer 2
     apply(rule inMap_rev)
     apply(force)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(thin_tac "y \<in> kPrefix (k - 1) ` append_language(cfgSTD_first G (k - 1) (drop (Suc 0) (cfg_item_rhs2 I))) {cfg_item_look_ahead I}")
    apply(erule bexE)+
    apply(rename_tac maxl q a y qA I w x)(*strict*)
    apply(simp (no_asm_use) only: append_language_def)
    apply(subgoal_tac "\<exists>a \<in> cfgSTD_first G (k - 1) (drop (Suc 0) (cfg_item_rhs2 I)). x = a @ (cfg_item_look_ahead I)")
     apply(rename_tac maxl q a y qA I w x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac maxl q a y qA I w x)(*strict*)
    apply(thin_tac "x \<in> {w. \<exists>a \<in> cfgSTD_first G (k - 1) (drop (Suc 0) (cfg_item_rhs2 I)). \<exists>b \<in> {cfg_item_look_ahead I}. w = a @ b}")
    apply(erule bexE)+
    apply(rename_tac maxl q a y qA I w x aa)(*strict*)
    apply(case_tac k)
     apply(rename_tac maxl q a y qA I w x aa)(*strict*)
     apply(subgoal_tac "y=[]")
      apply(rename_tac maxl q a y qA I w x aa)(*strict*)
      prefer 2
      apply(simp add: kPrefix_def)
     apply(rename_tac maxl q a y qA I w x aa)(*strict*)
     apply(rule_tac
    x="Suc 0"
    in exI)
     apply(rule_tac
    t="rule_rpop e"
    and s="[a]"
    in ssubst)
      apply(rename_tac maxl q a y qA I w x aa)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa)(*strict*)
     apply(rule inMap)
     apply(rule_tac
    x="a#[parser_bottom P]"
    in bexI)
      apply(rename_tac maxl q a y qA I w x aa)(*strict*)
      apply(simp add: kPrefix_def)
     apply(rename_tac maxl q a y qA I w x aa)(*strict*)
     apply(subgoal_tac "a \<in> parser_events P - {parser_bottom P}")
      apply(rename_tac maxl q a y qA I w x aa)(*strict*)
      apply(clarsimp)
     apply(rename_tac maxl q a y qA I w x aa)(*strict*)
     apply(rule_tac
    t="parser_events P - {parser_bottom P}"
    and s="cfg_events G"
    in ssubst)
      apply(rename_tac maxl q a y qA I w x aa)(*strict*)
      apply(rule_tac
    t="parser_events P"
    and s="cfg_events G'"
    in ssubst)
       apply(rename_tac maxl q a y qA I w x aa)(*strict*)
       apply(simp add: AF_LR_PARSER_def)
      apply(rename_tac maxl q a y qA I w x aa)(*strict*)
      apply(rule_tac
    t="parser_bottom P"
    and s="Do"
    in ssubst)
       apply(rename_tac maxl q a y qA I w x aa)(*strict*)
       apply(simp add: AF_LR_PARSER_def)
      apply(rename_tac maxl q a y qA I w x aa)(*strict*)
      apply(rule F_CFG_AUGMENT__cfg_events)
         apply(rename_tac maxl q a y qA I w x aa)(*strict*)
         apply(force)
        apply(rename_tac maxl q a y qA I w x aa)(*strict*)
        apply(force)
       apply(rename_tac maxl q a y qA I w x aa)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
    apply(erule conjE)+
    apply(rule_tac
    t="rule_rpop e"
    and s="a#y"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
    apply(rule_tac
    t="y"
    and s="kPrefix (k - 1)x"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
    apply(rule_tac
    t="x"
    and s="aa@(cfg_item_look_ahead I)"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
    apply(subgoal_tac "(cfg_item_look_ahead I) \<in> ((kPrefix k) ` {w@[Do]|w. set w \<subseteq> (cfg_events G)})")
     apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
     prefer 2
     apply(rule_tac
    q="q"
    in DollarTailStays_notS_prime)
              apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
              apply(force)
             apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
             apply(force)
            apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
            apply(force)
           apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
           apply(force)
          apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
          apply(force)
         apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
         apply(force)
        apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
     apply(rule_tac
    A="cfg_nonterminals G"
    in distinct_by_set_membership)
      apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
      apply(rule CFGprod_lhs_in_nonterms)
        apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
        apply(force)
       apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
     apply(rule F_FRESH_is_fresh)
     apply(simp add: valid_cfg_def)
    apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
    apply(rule_tac
    x="length (a # kPrefix (k - 1) (aa @ cfg_item_look_ahead I))"
    in exI)
    apply(rule inMap)
    apply(subgoal_tac "\<exists>x \<in> {w @ [Do] |w. set w \<subseteq> cfg_events G}. (kPrefix k) x = cfg_item_look_ahead I")
     apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
     prefer 2
     apply(rule inMap_rev)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat)(*strict*)
    apply(erule bexE)
    apply(rename_tac maxl q a y qA I w x aa nat xa)(*strict*)
    apply(thin_tac "cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G}")
    apply(subgoal_tac "\<exists>w. xa=w @ [Do] \<and> set w \<subseteq> cfg_events G")
     apply(rename_tac maxl q a y qA I w x aa nat xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat xa)(*strict*)
    apply(thin_tac "xa \<in> {w @ [Do] |w. set w \<subseteq> cfg_events G}")
    apply(erule exE)+
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(erule conjE)+
    apply(rule_tac
    t="cfg_item_look_ahead I"
    and s="kPrefix k xa"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(rule_tac
    t="xa"
    and s="wa@[Do]"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(rule_tac
    t="parser_bottom P"
    and s="Do"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(simp add: AF_LR_PARSER_def)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(rule_tac
    t="parser_events P"
    and s="cfg_events G'"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(simp add: AF_LR_PARSER_def)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(rule_tac
    t="cfg_events G' - {Do}"
    and s="cfg_events G"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule F_CFG_AUGMENT__cfg_events)
        apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
        apply(force)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(case_tac "k\<ge>(Suc (length wa))")
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule_tac
    t="kPrefix k (wa@[Do])"
    and s="wa@[Do]"
    in ssubst)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(simp (no_asm_use) only: kPrefix_def)
      apply(rule List.take_all)
      apply(rule_tac
    t="length (wa@[Do])"
    and s="Suc (length wa)"
    in ssubst)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(rule Suc_length)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(case_tac "k - 1 \<ge> length(aa @ wa @ [Do])")
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(rule_tac
    t="kPrefix (k - 1) (aa @ wa @ [Do])"
    and s="aa @ wa @ [Do]"
    in ssubst)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(simp (no_asm_use) only: kPrefix_def)
       apply(rule List.take_all)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(rule_tac
    x="a # aa @ wa @ [Do]"
    in bexI)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(simp (no_asm_use) only: kPrefix_def)
       apply(rule take_all)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(subgoal_tac "set ([a]@aa@wa) \<subseteq> cfg_events G")
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(rule set_concat_subset)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(rule set_concat_subset)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(rule cfgSTD_firstk_in_cfg_events)
         apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
         apply(force)
        apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule_tac
    x="a # (kPrefix (k - 1) (aa @ wa @ [Do])) @ [Do]"
    in bexI)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(simp (no_asm_use) only: kPrefix_def)
      apply(rule_tac
    t="(a # take (k - 1) (aa @ wa @ [Do]) @ [Do])"
    and s="(a # take (k - 1) (aa @ wa @ [Do])) @ [Do]"
    in ssubst)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(rule sym)
      apply(rule takePrecise)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(simp (no_asm_use))
     apply(rule conjI)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule_tac
    t="kPrefix (k - Suc 0) (aa @ wa @ [Do])"
    and s="kPrefix (k - Suc 0) (aa @ wa)"
    in ssubst)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(simp (no_asm_use) only: kPrefix_def)
      apply(rule_tac
    t="(aa @ wa @ [Do])"
    and s="((aa @ wa) @ [Do])"
    in ssubst)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(rule take_append2)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule_tac
    B="set (aa@wa)"
    in subset_trans)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(simp (no_asm_use) only: kPrefix_def)
      apply(rule List.set_take_subset)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule set_concat_subset)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(rule cfgSTD_firstk_in_cfg_events)
         apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
         apply(force)
        apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
        prefer 3
        apply(force)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(rule_tac
    x="(a # kPrefix (k - 1) (aa @ kPrefix k (wa @ [Do]))) @ [Do]"
    in bexI)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule sym)
     apply(simp (no_asm_use) only: kPrefix_def)
     apply(rule takePrecise)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(simp (no_asm_use))
    apply(rule conjI)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(rule_tac
    t="kPrefix k (wa@[Do])"
    and s="kPrefix k wa"
    in ssubst)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(simp add: kPrefix_def)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(simp (no_asm_simp) only: kPrefix_def)
    apply(rule_tac
    B="set (aa @ take (Suc nat) wa)"
    in subset_trans)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule List.set_take_subset)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(rule set_concat_subset)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule cfgSTD_firstk_in_cfg_events)
        apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
        apply(force)
       apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
      apply(force)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(force)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(rule_tac
    B="set wa"
    in subset_trans)
     apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
     apply(rule List.set_take_subset)
    apply(rename_tac maxl q a y qA I w x aa nat xa wa)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   prefer 2
   apply(rule_tac
    B="setA (cfg_item_rhs2 I)"
    in subset_trans)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(rule setADropIndexSubset2)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule_tac
    B="setA (cfg_item_rhs1 I @ cfg_item_rhs2 I)"
    in subset_trans)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(simp (no_asm) only: setAConcat concat_asso)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule prod_rhs_in_nonterms)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="setB (cfg_item_rhs2 I)"
    in subset_trans)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule setBDropIndexSubset2)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="setB (cfg_item_rhs1 I @ cfg_item_rhs2 I)"
    in subset_trans)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(simp (no_asm) only: setBConcat concat_asso)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule prod_rhs_in_cfg_events)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule conjI,force)
  apply(rule conjI,force)
  apply(rule conjI)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="rule_lpush e"
    and s="[q, qA]"
    in ssubst)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule set_take_head2)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule set_take_head2)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(thin_tac "[qA] = F_DFA_GOTO_SEQUENCE M q [teB a]")
  apply(rule conjI,force)
  apply(rule conjI,force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule conjI)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(rule_tac
    t="rule_rpush e"
    and s="y"
    in ssubst)
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(subgoal_tac "x@[parser_bottom P]=a#y")
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(thin_tac "x @ [parser_bottom P] = rule_rpop e")
  apply(case_tac y)
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(subgoal_tac "a\<noteq>parser_bottom P")
   apply(rename_tac maxl q a y qA I w x)(*strict*)
   apply(clarsimp)
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(rule_tac
    A="cfg_events G"
    in distinct_by_set_membership)
   apply(rename_tac maxl q a y qA I w x)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(rule_tac
    t="parser_bottom P"
    and s="Do"
    in ssubst)
   apply(rename_tac maxl q a y qA I w x)(*strict*)
   apply(simp add: AF_LR_PARSER_def)
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(rule_tac
    t="Do"
    and s="F_FRESH (cfg_events G)"
    in ssubst)
   apply(rename_tac maxl q a y qA I w x)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w x)(*strict*)
  apply(rule F_FRESH_is_fresh)
  apply(simp add: valid_cfg_def)
  apply(rename_tac maxl q a y qA I w x aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. y = w' @ [x']")
  apply(rename_tac maxl q a y qA I w x aa list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac maxl q a y qA I w x aa list)(*strict*)
  apply(thin_tac "y=aa#list")
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="parser_events P"
    and s="cfg_events G'"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: AF_LR_PARSER_def)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule cfgSTD_firstk_in_cfg_events)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  prefer 3
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(rule Set.Un_least)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="setA (cfg_item_rhs2 I)"
    in subset_trans)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule setADropIndexSubset2)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="setA (cfg_item_rhs1 I @ cfg_item_rhs2 I)"
    in subset_trans)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(simp (no_asm) only: setAConcat concat_asso)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="cfg_nonterminals G"
    in subset_trans)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(rule prod_rhs_in_nonterms)
    apply(rename_tac maxl q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="setA (liftB (cfg_item_look_ahead I))"
    and s="{}"
    in ssubst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule setA_liftB)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp (no_asm) only: setBConcat concat_asso)
  apply(rule Set.Un_least)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="setB (cfg_item_rhs2 I)"
    in subset_trans)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule setBDropIndexSubset2)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="setB (cfg_item_rhs1 I @ cfg_item_rhs2 I)"
    in subset_trans)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp (no_asm) only: setBConcat concat_asso)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    B="cfg_events G"
    in subset_trans)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule prod_rhs_in_cfg_events)
   apply(rename_tac maxl q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(force)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule_tac
    t="setB (liftB (cfg_item_look_ahead I))"
    and s="set (cfg_item_look_ahead I)"
    in subst)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(rule set_setB_liftB)
  apply(rename_tac maxl q a y qA I w)(*strict*)
  apply(simp add: valid_item_def)
  done

lemma AF_LR_PARSER_valid_parser_finite_parser_rules: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> finite (parser_rules P)"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "finite (AF_LR_PARSER__rules G G' M k)")
   apply(simp add: AF_LR_PARSER_def)
  apply(subgoal_tac "\<exists>maxl. \<forall>q \<in> (epda_states M). \<forall>I \<in> q. length (cfg_item_rhs1 I @ cfg_item_rhs2 I)\<le>maxl")
   prefer 2
   apply(subgoal_tac "\<exists>maxl. \<forall>I \<in> {I. \<exists>q. I \<in> q \<and> q \<in> (epda_states M)}. (\<lambda>I. length (cfg_item_rhs1 I @ cfg_item_rhs2 I)) I \<le>maxl")
    prefer 2
    apply(rule_tac
      f="(\<lambda>I. length (cfg_item_rhs1 I @ cfg_item_rhs2 I))"
      in finite_has_max)
    apply(rule_tac
      t="{I. \<exists>q. I \<in> q \<and> q \<in> epda_states M}"
      and s="\<Union>{(\<lambda>x. x)S|S. S \<in> epda_states M}"
      in ssubst)
     apply(force)
    apply(rule finite_big_union)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rule ballI)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      G="G'"
      in F_LR_MACHINE_has_finite_states)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(erule exE)
   apply(rename_tac maxl)(*strict*)
   apply(rule_tac
      x="maxl"
      in exI)
   apply(force)
  apply(erule exE)
  apply(rename_tac maxl)(*strict*)
  apply(rule_tac
      B = "{r. length (rule_lpop r)\<le>Suc maxl \<and> length (rule_rpop r)\<le>Suc k \<and> length (rule_lpush r)\<le>Suc(Suc maxl) \<and> length (rule_rpush r)\<le>Suc k \<and> valid_parser_step_label P r} \<times>(WrapInSome (cfg_productions G))"
      in Finite_Set.finite_subset)
   apply(rename_tac maxl)(*strict*)
   apply(rule subsetI)
   apply(rename_tac maxl x)(*strict*)
   apply(case_tac x)
   apply(rename_tac maxl x a b)(*strict*)
   apply(subgoal_tac "valid_parser_step_label P a")
    apply(rename_tac maxl x a b)(*strict*)
    prefer 2
    apply(rule AF_LR_PARSER_valid_parser_rules_are_parserrules)
              apply(rename_tac maxl x a b)(*strict*)
              apply(force)
             apply(rename_tac maxl x a b)(*strict*)
             apply(force)
            apply(rename_tac maxl x a b)(*strict*)
            apply(force)
           apply(rename_tac maxl x a b)(*strict*)
           apply(force)
          apply(rename_tac maxl x a b)(*strict*)
          apply(force)
         apply(rename_tac maxl x a b)(*strict*)
         apply(force)
        apply(rename_tac maxl x a b)(*strict*)
        apply(force)
       apply(rename_tac maxl x a b)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac maxl x a b)(*strict*)
   apply(subgoal_tac " (\<exists>q q_seq I y qA. x=(\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>) \<and> q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> cfg_item_rhs1 I = [] \<and> qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I)) \<and> q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) \<and> \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> \<in> last (q # q_seq)) \<or> (\<exists>q a y qA. x=(\<lparr>rule_lpop = [q], rule_rpop = a # y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, None) \<and> q \<in> epda_states M \<and> (\<exists>I \<in> q. \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> [teB a] = take (Suc 0) (cfg_item_rhs2 I) \<and> qA \<in> F_EPDA_GOTO M q (teB a) \<and> y \<in> cfgSTD_first G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))))")
    apply(rename_tac maxl x a b)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER__rules_def)
   apply(rename_tac maxl x a b)(*strict*)
   apply(erule disjE)
    apply(rename_tac maxl x a b)(*strict*)
    apply(erule exE)+
    apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
    apply(erule conjE)+
    apply(erule_tac
      x="q"
      in ballE)
     apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
    apply(erule_tac
      x="I"
      in ballE)
     apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
    apply(subgoal_tac "\<exists>w. q=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
     apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
     prefer 2
     apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
      apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
      prefer 2
      apply(rule "LRM_contains_theEqClasses")
        apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
     apply(force)
    apply(rename_tac maxl x a b q q_seq I y qA)(*strict*)
    apply(erule exE)
    apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
    apply(subgoal_tac "valid_item G' k \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr>")
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     prefer 2
     apply(case_tac q_seq)
      apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
      apply(rule Fact6_12__2)
       apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
     apply(subgoal_tac "(last q_seq) \<in> epda_states M")
      apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
      prefer 2
      apply(rule_tac
      A="set q_seq"
      in set_mp)
       apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
       apply(rule_tac
      w="(cfg_item_rhs2 I)"
      and q="q"
      in F_EPDA_GOTO_SEQUENCESound_main3)
           apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
           apply(force)
          apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
          apply(force)
         apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
         apply(force)
        apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
        apply(subgoal_tac "setA (cfg_item_rhs2 I) \<subseteq> cfg_nonterminals G")
         apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
         apply(subgoal_tac "setB (cfg_item_rhs2 I) \<subseteq> cfg_events G")
          apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
          apply(simp (no_asm_simp) add: F_LR_MACHINE_def)
          apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
           apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
           apply(rule_tac
      B="cfg_events G"
      in subset_trans)
            apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
            apply(force)
           apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
           apply(simp add: F_CFG_AUGMENT_def)
           apply(force)
          apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
          apply(simp add: F_CFG_AUGMENT_def)
          apply(force)
         apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
         apply(rule prod_rhs_in_cfg_events)
          apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
          apply(force)
         apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
         apply(force)
        apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
        apply(rule prod_rhs_in_nonterms)
         apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
         apply(force)
        apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
        apply(force)
       apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
     apply(subgoal_tac "\<exists>w. (last q_seq)=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
      apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
      prefer 2
      apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
       apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
       prefer 2
       apply(rule LRM_contains_theEqClasses)
         apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q q_seq I y qA w aa list)(*strict*)
     apply(erule exE)
     apply(rename_tac maxl x a b q q_seq I y qA w aa list wa)(*strict*)
     apply(rule Fact6_12__2)
      apply(rename_tac maxl x a b q q_seq I y qA w aa list wa)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q q_seq I y qA w aa list wa)(*strict*)
     apply(force)
    apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
    apply(subgoal_tac "valid_item G' k I")
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     prefer 2
     apply(rule_tac
      q="q"
      in F_LR_MACHINE_States_contain_Items)
         apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
         apply(force)
        apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
    apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     prefer 2
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
      apply(simp add: F_LR_MACHINE_def)
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     apply(rule_tac
      I="I"
      in Item_rhs2_in_CFG)
       apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
    apply(subgoal_tac "q_seq=F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     prefer 2
     apply(rule_tac
      q="q"
      in F_DFA_GOTO_SEQUENCE_F_EPDA_GOTO_SEQUENCE_elem)
          apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
          apply(force)
         apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
         apply(force)
        apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
    apply(subgoal_tac "length q_seq \<le> maxl")
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     prefer 2
     apply(rule_tac
      t="length q_seq"
      and s="length (cfg_item_rhs2 I)"
      in subst)
      apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
      apply(rule_tac
      q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
           apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
           apply(force)
          apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
          apply(force)
         apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
         apply(force)
        apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
        apply(force)
       apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     apply(force)
    apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
    apply(subgoal_tac "length y \<le> Suc k")
     apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
     apply(simp add: WrapInSome_def)
     apply(clarsimp)
    apply(rename_tac maxl x a b q q_seq I y qA w)(*strict*)
    apply(simp add: valid_item_def)
   apply(rename_tac maxl x a b)(*strict*)
   apply(erule exE)+
   apply(rename_tac maxl x a b q aa y qA)(*strict*)
   apply(erule conjE)+
   apply(erule bexE)+
   apply(rename_tac maxl x a b q aa y qA I)(*strict*)
   apply(erule conjE)+
   apply(subgoal_tac "\<exists>w. q=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(rename_tac maxl x a b q aa y qA I)(*strict*)
    prefer 2
    apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
     apply(rename_tac maxl x a b q aa y qA I)(*strict*)
     prefer 2
     apply(rule LRM_contains_theEqClasses)
       apply(rename_tac maxl x a b q aa y qA I)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac maxl x a b q aa y qA I)(*strict*)
     apply(force)
    apply(rename_tac maxl x a b q aa y qA I)(*strict*)
    apply(force)
   apply(rename_tac maxl x a b q aa y qA I)(*strict*)
   apply(erule exE)
   apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
   apply(subgoal_tac "valid_item G' k I")
    apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
    prefer 2
    apply(rule_tac
      q="q"
      in F_LR_MACHINE_States_contain_Items)
        apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
        apply(force)
       apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
   apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
    apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      and q="q"
      in F_LR_MACHINE_item_in_state_rhs2_in_cfg_events)
        apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
        apply(force)
       apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
   apply(subgoal_tac "teA (cfg_item_lhs I) \<in> epda_events M")
    apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      in F_LR_MACHINE_item_in_state_lhs_in_cfg_events)
       apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rename_tac maxl x a b q aa y qA I w)(*strict*)
   apply(rename_tac maxl x x1 x2 q a y qA I w)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(subgoal_tac "[qA]=F_DFA_GOTO_SEQUENCE M q [teB a]")
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    prefer 2
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q [teB a]"
      and s="[F_DFA_GOTO M q (teB a)]"
      in ssubst)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
         apply(force)
        apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
        apply(force)
       apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(rule_tac
      A="set (cfg_item_rhs2 I)"
      in set_mp)
      apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(clarsimp)
     apply(rename_tac maxl aa y qA I w)(*strict*)
     apply(rule head_in_set2)
     apply(force)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(subgoal_tac "{F_DFA_GOTO M q (teB a)} = F_EPDA_GOTO M q (teB a)")
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     prefer 2
     apply(rule F_DFA_GOTO_to_F_EPDA_GOTO)
         apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
         apply(force)
        apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
        apply(force)
       apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(rule_tac
      A="set (cfg_item_rhs2 I)"
      in set_mp)
      apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(clarsimp)
     apply(rename_tac maxl aa y qA I w)(*strict*)
     apply(rule head_in_set2)
     apply(force)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(rule listEqI1)
    apply(blast)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(thin_tac "qA \<in> F_EPDA_GOTO M q (teB a)")
   apply(erule_tac
      x="q"
      in ballE)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(erule_tac
      x="I"
      in ballE)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(subgoal_tac "\<lparr>rule_lpop = [q], rule_rpop = a # y, rule_lpush = [q, qA], rule_rpush = y\<rparr> \<in> {r. length (rule_lpop r) \<le> Suc maxl \<and> length (rule_rpop r) \<le> Suc k \<and> length (rule_lpush r) \<le> Suc (Suc maxl) \<and> length (rule_rpush r) \<le> Suc k \<and> valid_parser_step_label P r}")
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(simp add: WrapInSome_def)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(rule CollectI)
   apply(subgoal_tac "length y\<le>k- Suc 0")
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    prefer 2
    apply(rule cfgSTD_firstk_shorter_than_k)
    apply(force)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(rule conjI)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(rule conjI)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(simp (no_asm_simp))
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(rule conjI)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(rule_tac
      t="rule_lpush \<lparr>rule_lpop = [q], rule_rpop = a # y, rule_lpush = [q, qA], rule_rpush = y\<rparr>"
      and s="[q,qA]"
      in ssubst)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(rule_tac
      t="length [q,qA]"
      and s="Suc(Suc 0)"
      in ssubst)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(rule length2)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(rule conjI)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(rule_tac
      t="rule_rpush \<lparr>rule_lpop = [q], rule_rpop = a # y, rule_lpush = [q, qA], rule_rpush = y\<rparr>"
      and s="y"
      in ssubst)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(rule AF_LR_PARSER_valid_parser_rules_are_parserrules)
             apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
             apply(force)
            apply(force)
           apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
           apply(force)
          apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
          apply(force)
         apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
         apply(force)
        apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
        apply(force)
       apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
       apply(force)
      apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
      apply(force)
     apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
     apply(force)
    apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
    apply(force)
   apply(rename_tac maxl x x1 x2 q a y qA I w)(*strict*)
   apply(force)
  apply(rename_tac maxl)(*strict*)
  apply(rule finite_cartesian_product)
   apply(rename_tac maxl)(*strict*)
   apply(rule_tac
      t="{r. length (rule_lpop r) \<le> Suc maxl \<and> length (rule_rpop r) \<le> Suc k \<and> length (rule_lpush r) \<le> Suc (Suc maxl) \<and> length (rule_rpush r) \<le> Suc k \<and> valid_parser_step_label P r}"
      and s="(\<lambda>(a,b,c,d). \<lparr>rule_lpop=a,rule_rpop=b,rule_lpush=c,rule_rpush=d\<rparr> ) ` {(lpop,rpop,lpush,rpush)| lpop rpop lpush rpush. length lpop \<le> Suc maxl \<and> length rpop \<le> Suc k \<and> length lpush \<le> Suc (Suc maxl) \<and> length rpush \<le> Suc k \<and> valid_parser_step_label P \<lparr>rule_lpop=lpop,rule_rpop=rpop,rule_lpush=lpush,rule_rpush=rpush\<rparr>}"
      in ssubst)
    apply(rename_tac maxl)(*strict*)
    apply(clarsimp)
    apply(rule order_antisym)
     apply(rename_tac maxl)(*strict*)
     apply(clarsimp)
     apply(rename_tac maxl x)(*strict*)
     apply(case_tac x)
     apply(rename_tac maxl x rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
     apply(rename_tac a b c d)
     apply(rename_tac maxl x a b c d)(*strict*)
     apply(rule_tac
      y="(a,b,c,d)"
      in inMap2)
      apply(rename_tac maxl x a b c d)(*strict*)
      apply(clarsimp)
     apply(rename_tac maxl x a b c d)(*strict*)
     apply(clarsimp)
    apply(rename_tac maxl)(*strict*)
    apply(clarsimp)
   apply(rename_tac maxl)(*strict*)
   apply(rule finite_imageI)
   apply(unfold valid_parser_step_label_def)
   apply(rule_tac
      B="{(lpop, rpop, lpush, rpush) |lpop rpop lpush rpush. length lpop \<le> Suc maxl \<and> length rpop \<le> Suc k \<and> length lpush \<le> Suc (Suc maxl) \<and> length rpush \<le> Suc k \<and> set rpop \<subseteq> parser_events P \<and> set rpush \<subseteq> parser_events P \<and> set lpop \<subseteq> parser_nonterms P \<and> set lpush \<subseteq> parser_nonterms P}"
      in finite_subset)
    apply(rename_tac maxl)(*strict*)
    apply(rule subsetI)
    apply(rename_tac maxl x)(*strict*)
    apply(simp (no_asm_use))
    apply(erule exE)+
    apply(rename_tac maxl x lpop rpop lpush rpush)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa)(*strict*)
    apply(rule_tac
      x="lpop"
      in exI)
    apply(rule_tac
      x="rpop"
      in exI)
    apply(rule_tac
      x="lpush"
      in exI)
    apply(rule_tac
      x="rpush"
      in exI)
    apply(rule conjI,force)
    apply(rule conjI,force)
    apply(rule conjI,force)
    apply(rule conjI,force)
    apply(rule conjI,force)
    apply(rule conjI)
     apply(rename_tac maxl x lpop rpop lpush rpush ka xa)(*strict*)
     prefer 2
     apply(rule conjI,force)
     apply(rule conjI,force)
     apply(force)
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa)(*strict*)
    apply(subgoal_tac "\<exists>y \<in> {w @ [parser_bottom P] |w. set w \<subseteq> parser_events P - {parser_bottom P}}. (kPrefix ka) y=rpop")
     apply(rename_tac maxl x lpop rpop lpush rpush ka xa)(*strict*)
     prefer 2
     apply(rule inMap_rev)
     apply(force)
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa)(*strict*)
    apply(erule bexE)+
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa y)(*strict*)
    apply(rule_tac
      t="rpop"
      and s="kPrefix ka y"
      in ssubst)
     apply(rename_tac maxl x lpop rpop lpush rpush ka xa y)(*strict*)
     apply(force)
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa y)(*strict*)
    apply(rule_tac
      B="set y"
      in subset_trans)
     apply(rename_tac maxl x lpop rpop lpush rpush ka xa y)(*strict*)
     apply(simp (no_asm_use) only: kPrefix_def)
     apply(rule List.set_take_subset)
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa y)(*strict*)
    apply(subgoal_tac "\<exists>w. y=w @ [parser_bottom P] \<and> set w \<subseteq> parser_events P - {parser_bottom P}")
     apply(rename_tac maxl x lpop rpop lpush rpush ka xa y)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa y)(*strict*)
    apply(erule exE)+
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa y w)(*strict*)
    apply(rule_tac
      t="y"
      and s="w @ [parser_bottom P]"
      in ssubst)
     apply(rename_tac maxl x lpop rpop lpush rpush ka xa y w)(*strict*)
     apply(force)
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa y w)(*strict*)
    apply(rule set_concat_subset)
     apply(rename_tac maxl x lpop rpop lpush rpush ka xa y w)(*strict*)
     apply(erule conjE)+
     apply(blast)
    apply(rename_tac maxl x lpop rpop lpush rpush ka xa y w)(*strict*)
    apply(simp add: AF_LR_PARSER_def F_CFG_AUGMENT_def)
   apply(rename_tac maxl)(*strict*)
   apply(rule_tac
      B="{(lpop, rpop, lpush, rpush) |lpop rpop lpush rpush. length lpop \<le> Suc (Suc (maxl+k)) \<and> length rpop \<le> Suc (Suc (maxl+k)) \<and> length lpush \<le> Suc (Suc (maxl+k)) \<and> length rpush \<le> Suc (Suc (maxl+k)) \<and> set rpop \<subseteq> parser_events P \<and> set rpush \<subseteq> parser_events P \<and> set lpop \<subseteq> parser_nonterms P \<and> set lpush \<subseteq> parser_nonterms P}"
      in finite_subset)
    apply(rename_tac maxl)(*strict*)
    apply(force)
   apply(rename_tac maxl)(*strict*)
   apply(subgoal_tac "finite {a. (length a\<le> Suc(Suc(maxl+k))) \<and> (set a) \<subseteq> parser_nonterms P}")
    apply(rename_tac maxl)(*strict*)
    prefer 2
    apply(rule_tac
      s="{w. w \<in> kleene_star (parser_nonterms P) \<and> length w\<le>Suc(Suc(maxl+k))}"
      and P="\<lambda>x. finite x"
      in ssubst)
     apply(rename_tac maxl)(*strict*)
     apply(clarsimp)
     apply(simp add: kleene_star_def)
     apply(rule order_antisym)
      apply(rename_tac maxl)(*strict*)
      apply(force)
     apply(rename_tac maxl)(*strict*)
     apply(force)
    apply(rename_tac maxl)(*strict*)
    apply(rule wordsUpToLengthFinite)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def AF_LR_PARSER_def)
   apply(rename_tac maxl)(*strict*)
   apply(subgoal_tac "finite {a. (length a\<le> Suc(Suc(maxl+k))) \<and> (set a) \<subseteq> parser_events P}")
    apply(rename_tac maxl)(*strict*)
    prefer 2
    apply(rule_tac
      s="{w. w \<in> kleene_star (parser_events P) \<and> length w\<le>Suc(Suc(maxl+k))}"
      and P="\<lambda>x. finite x"
      in ssubst)
     apply(rename_tac maxl)(*strict*)
     apply(clarsimp)
     apply(simp add: kleene_star_def)
     apply(rule order_antisym)
      apply(rename_tac maxl)(*strict*)
      apply(force)
     apply(rename_tac maxl)(*strict*)
     apply(force)
    apply(rename_tac maxl)(*strict*)
    apply(rule wordsUpToLengthFinite)
    apply(simp add: valid_cfg_def valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def AF_LR_PARSER_def)
   apply(rename_tac maxl)(*strict*)
   apply(rule_tac
      P="\<lambda>x. finite x"
      and s=" {a. (length a\<le> Suc(Suc(maxl+k))) \<and> (set a) \<subseteq> parser_nonterms P} \<times>{a. (length a\<le> Suc(Suc(maxl+k))) \<and> (set a) \<subseteq> parser_events P} \<times>{a. (length a\<le> Suc(Suc(maxl+k))) \<and> (set a) \<subseteq> parser_nonterms P} \<times>{a. (length a\<le> Suc(Suc(maxl+k))) \<and> (set a) \<subseteq> parser_events P}"
      in ssubst)
    apply(rename_tac maxl)(*strict*)
    apply(force)
   apply(rename_tac maxl)(*strict*)
   apply(rule finite_cartesian_product)
    apply(rename_tac maxl)(*strict*)
    apply(force)
   apply(rename_tac maxl)(*strict*)
   apply(rule finite_cartesian_product)
    apply(rename_tac maxl)(*strict*)
    apply(force)
   apply(rename_tac maxl)(*strict*)
   apply(rule finite_cartesian_product)
    apply(rename_tac maxl)(*strict*)
    apply(force)
   apply(rename_tac maxl)(*strict*)
   apply(force)
  apply(rename_tac maxl)(*strict*)
  apply(simp add: WrapInSome_def valid_cfg_def)
  done

corollary AF_LR_PARSER_valid_parser: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> valid_parser P"
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
  apply(unfold valid_parser_def)
  apply(rule conjI)
   apply(rule AF_LR_PARSER_valid_parser_finite_parser_events)
         apply(force)+
  apply(rule conjI)
   apply(rule AF_LR_PARSER_valid_parser_finite_nonterms)
          apply(force)+
  apply(rule conjI)
   apply(rule AF_LR_PARSER_valid_parser_parser_initial_in_nonterms)
            apply(force)+
  apply(rule conjI)
   apply(rule AF_LR_PARSER_valid_parser_parser_marking_in_nonterms)
            apply(force)+
  apply(rule conjI)
   apply(rule AF_LR_PARSER_valid_parser_finite_parser_rules)
            apply(force)+
  apply(rule conjI)
   apply(rule ballI)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>y. ((x,y) \<in> (AF_LR_PARSER__rules G G' M k))")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(subgoal_tac "\<exists>!y. ((x,y) \<in> (AF_LR_PARSER__rules G G' M k))")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule X6_3_InformationOnRules_UniqueEffect)
           apply(rename_tac x)(*strict*)
           apply(force)+
   apply(rename_tac x)(*strict*)
   apply(erule exE)+
   apply(rename_tac x y)(*strict*)
   apply(rule AF_LR_PARSER_valid_parser_rules_are_parserrules)
             apply(rename_tac x y)(*strict*)
             apply(force)+
  apply(simp add: F_CFG_AUGMENT_def AF_LR_PARSER_def)
  done

lemma AF_LR_PARSER_NonNone_effect_only_for_rules: "
  P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> valid_parser P
  \<Longrightarrow> parser_marker P r = Some x
  \<Longrightarrow> r \<in> parser_rules P"
  apply(case_tac "\<exists>!y. ((r,y) \<in> (AF_LR_PARSER__rules G G' M k))")
   apply(simp add: AF_LR_PARSER_def)
   apply(rule inMap)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(rule_tac
      x="(r,y)"
      in bexI)
    apply(rename_tac y)(*strict*)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(simp add: AF_LR_PARSER_def)
  done

lemma AF_LR_PARSER_nonterms_not_empty: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> P = AF_LR_PARSER G G' M k Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q \<in> parser_nonterms P
  \<Longrightarrow> q \<noteq> {}"
  apply(subgoal_tac "F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G)) = {}")
   prefer 2
   apply(rule_tac
      q="F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))"
      in ReadInitialIsEmpty)
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
  apply(simp (no_asm_use) only: AF_LR_PARSER_def)
  apply(force)
  done

definition AF_LR_PARSER_input :: "
  ('nonterminal DT_symbol, 'event DT_symbol) cfg
  \<Rightarrow> ('nonterminal DT_symbol, 'event DT_symbol) DT_first_function
  \<Rightarrow> 'event DT_symbol
  \<Rightarrow> 'nonterminal DT_symbol
  \<Rightarrow> ('nonterminal DT_symbol, 'event DT_symbol) cfg
  \<Rightarrow> (('nonterminal DT_symbol, 'event DT_symbol) DT_cfg_item set,
      ('nonterminal DT_symbol, 'event DT_symbol) DT_two_elements,
      nat) epda
  \<Rightarrow> (('nonterminal DT_symbol, 'event DT_symbol) DT_cfg_item set,
      'event DT_symbol,
      (('nonterminal DT_symbol, 'event DT_symbol) cfg_step_label option option)) parser
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "AF_LR_PARSER_input G F Do S' G' M P k \<equiv>
  valid_cfg G
  \<and> cfgSTD_first_compatible F k
  \<and> Do = F_FRESH (cfg_events G)
  \<and> S' = F_FRESH (cfg_nonterminals G)
  \<and> G' = F_CFG_AUGMENT G S' Do
  \<and> M = F_LR_MACHINE G' F k
  \<and> P = AF_LR_PARSER G G' M k Do"

lemma AF_LR_PARSER__rules_reduce_elem: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> parser_marker P r'_v = Some (Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>)
  \<Longrightarrow> r'_v \<in> parser_rules P
  \<Longrightarrow> \<exists>q q_seq I y qA. (r'_v, parser_marker P r'_v) = (\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, Some (Some \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>)) \<and> q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> cfg_item_rhs1 I = [] \<and> qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I)) \<and> q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) \<and> \<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs2 I, cfg_item_rhs2 = [], cfg_item_look_ahead = y\<rparr> \<in> last (q # q_seq)"
  apply(subgoal_tac "(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None) r'_v = Some(Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>)")
   prefer 2
   apply(rule_tac
      t="(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None)"
      and s="parser_marker P"
      in ssubst)
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(force)
  apply(subgoal_tac "\<exists>!y. (r'_v, y) \<in> AF_LR_PARSER__rules G G' M k")
   prefer 2
   apply(case_tac "\<exists>!y. (r'_v, y) \<in> AF_LR_PARSER__rules G G' M k")
    apply(force)
   apply(force)
  apply(subgoal_tac "(THE y. (r'_v, y) \<in> AF_LR_PARSER__rules G G' M k) = Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>")
   prefer 2
   apply(clarsimp)
  apply(subgoal_tac "(r'_v,Some \<lparr>prod_lhs = A, prod_rhs = XSEQ\<rparr>) \<in> AF_LR_PARSER__rules G G' M k")
   prefer 2
   apply(rule_tac
      P="\<lambda>y. (r'_v, y) \<in> AF_LR_PARSER__rules G G' M k"
      in THE_eq_prop)
    apply(force)
   apply(force)
  apply(simp add: AF_LR_PARSER__rules_def)
  done

lemma AF_LR_PARSER__rules_shift_elem: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> parser_marker P r'_v = Some None
  \<Longrightarrow> r'_v \<in> parser_rules P
  \<Longrightarrow> \<exists>q a y qA. (r'_v, parser_marker P r'_v) = (\<lparr>rule_lpop = [q], rule_rpop = a # y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, Some None) \<and> (q \<in> epda_states M) \<and> (\<exists>I \<in> q. \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> [teB a] = take (Suc 0) (cfg_item_rhs2 I) \<and> qA \<in> (F_EPDA_GOTO M q (teB a)) \<and> y \<in> (cfgSTD_first G' (k- 1) ((drop (Suc 0) (cfg_item_rhs2 I)) @ (liftB (cfg_item_look_ahead I)))))"
  apply(subgoal_tac "(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None) r'_v = Some None")
   prefer 2
   apply(rule_tac
      t="(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None)"
      and s="parser_marker P"
      in ssubst)
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(force)
  apply(subgoal_tac "\<exists>!y. (r'_v, y) \<in> AF_LR_PARSER__rules G G' M k")
   prefer 2
   apply(rule X6_3_InformationOnRules_UniqueEffect)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(simp add: AF_LR_PARSER_input_def)
         apply(force)
        apply(force)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "(THE y. (r'_v, y) \<in> AF_LR_PARSER__rules G G' M k) = None")
   prefer 2
   apply(clarsimp)
  apply(subgoal_tac "(r'_v,None) \<in> AF_LR_PARSER__rules G G' M k")
   prefer 2
   apply(rule_tac
      P="\<lambda>y. (r'_v, y) \<in> AF_LR_PARSER__rules G G' M k"
      in THE_eq_prop)
    apply(force)
   apply(force)
  apply(simp add: AF_LR_PARSER__rules_def)
  done

end
