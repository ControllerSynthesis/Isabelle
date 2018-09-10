section {*T05\_05\_LR\_PARSER*}
theory
  T05_05_LR_PARSER

imports
  T05_04_LR_MACHINE
  T05_01_EPDA_GOTO

begin

definition item_core :: "
  ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label"
  where
    "item_core I \<equiv>
  \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>"

definition F_LR_PARSER__rules :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda
  \<Rightarrow> ((('nonterminal, 'event) DT_cfg_item set, 'event) parser_step_label \<times> ('nonterminal, 'event) cfg_step_label option) set"
  where
    "F_LR_PARSER__rules G G' M \<equiv>
  {(\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr>,
    Some (item_core I))
    | q q_seq I y qA.
    q \<in> epda_states M
    \<and> I \<in> q
    \<and> item_core I \<in> cfg_productions G
    \<and> cfg_item_rhs1 I = []
    \<and> y = cfg_item_look_ahead I
    \<and> qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))
    \<and> q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)}
  \<union>
  {(\<lparr>rule_lpop = [q], rule_rpop = [a], rule_lpush = [q, qA], rule_rpush = []\<rparr>, None)
    | q a qA I.
    q \<in> epda_states M
    \<and> I \<in> q
    \<and> item_core I \<in> cfg_productions G
    \<and> [teB a] = take (Suc 0) (cfg_item_rhs2 I)
    \<and> qA \<in> F_EPDA_GOTO M q (teB a)}"

definition F_LR_PARSER :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda
  \<Rightarrow> 'event
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, 'event, ((('nonterminal, 'event) cfg_step_label option) option)) parser"
  where
    "F_LR_PARSER G G' M e_F \<equiv>
  \<lparr>parser_nonterms =
    epda_states M
    - {epda_initial M,
        last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB e_F, teA (cfg_initial G), teB e_F]),
        F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))},
  parser_events = cfg_events G',
  parser_initial = F_DFA_GOTO M (epda_initial M) (teB e_F),
  parser_marking = {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB e_F, teA (cfg_initial G)])},
  parser_rules = (\<lambda>(x, y). x) ` F_LR_PARSER__rules G G' M,
  parser_marker =
    \<lambda>x.
        if \<exists>! y. (x, y) \<in> F_LR_PARSER__rules G G' M
        then Some (THE y. (x, y) \<in> F_LR_PARSER__rules G G' M)
        else None,
  parser_bottom = e_F\<rparr>"

definition F_LRk_PARSER__rules :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda
  \<Rightarrow> nat
  \<Rightarrow> ((('nonterminal, 'event) DT_cfg_item set, 'event) parser_step_label \<times> ('nonterminal, 'event) cfg_step_label option) set"
  where
    "F_LRk_PARSER__rules G F G' M k \<equiv>
  {(\<lparr>rule_lpop = q # q_seq, rule_rpop = y, rule_lpush = [q, qA], rule_rpush = y\<rparr>,
    Some (item_core I))
    | q q_seq I y qA.
    q \<in> epda_states M
    \<and> I \<in> q
    \<and> item_core I \<in> cfg_productions G
    \<and> cfg_item_rhs1 I = []
    \<and> y = cfg_item_look_ahead I
    \<and> qA \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))
    \<and> q_seq \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)}
  \<union>
  {(\<lparr>rule_lpop = [q], rule_rpop = a # y, rule_lpush = [q, qA], rule_rpush = y\<rparr>, None)
    | q a y qA I.
    q \<in> epda_states M
    \<and> I \<in> q
    \<and> item_core I \<in> cfg_productions G
    \<and> [teB a] = take (Suc 0) (cfg_item_rhs2 I)
    \<and> qA \<in> F_EPDA_GOTO M q (teB a)
    \<and> y \<in> F G' (k - 1) (drop (Suc 0) (cfg_item_rhs2 I) @ liftB (cfg_item_look_ahead I))}"

definition F_LRk_PARSER :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda
  \<Rightarrow> nat
  \<Rightarrow> 'event
  \<Rightarrow> (('nonterminal, 'event) DT_cfg_item set, 'event, ((('nonterminal, 'event) cfg_step_label option) option)) parser"
  where
    "F_LRk_PARSER G F G' M k e_F \<equiv>
  \<lparr>parser_nonterms =
    epda_states M
    - {epda_initial M,
        last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB e_F, teA (cfg_initial G), teB e_F]),
        F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))},
  parser_events = cfg_events G',
  parser_initial = F_DFA_GOTO M (epda_initial M) (teB e_F),
  parser_marking = {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB e_F, teA (cfg_initial G)])},
  parser_rules = (\<lambda>(x, y). x) ` F_LRk_PARSER__rules G F G' M k,
  parser_marker =
    \<lambda>x.
        if \<exists>! y. (x, y) \<in> F_LRk_PARSER__rules G F G' M k
        then Some (THE y. (x, y) \<in> F_LRk_PARSER__rules G F G' M k)
        else None,
  parser_bottom = e_F\<rparr>"

end
