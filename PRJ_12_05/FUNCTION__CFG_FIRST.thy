section {*FUNCTION\_\_CFG\_FIRST*}
theory
  FUNCTION__CFG_FIRST

imports
  PRJ_12_05__ENTRY

begin

type_synonym ('nonterminal, 'event) F_CFG_FIRST__table_domain = "('nonterminal, 'event) DT_two_elements list \<Rightarrow> 'event option set"

definition maps_to_cfg_events :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "maps_to_cfg_events G f \<equiv>
  \<forall>x. option_to_setMap (f x) \<subseteq> cfg_events G"

definition maps_only_from_table_domain :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "maps_only_from_table_domain G f \<equiv>
  \<forall>x. f x \<noteq> {} \<longrightarrow> x \<in> F_CFG_FIRST__table_domain G"

definition F_CFG_FIRST__table__fp_valid_input :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_valid_input G f \<equiv>
  valid_cfg G
  \<and> cfg_has_production G
  \<and> cfg_every_nonterminal_on_some_left_hand_side G
  \<and> maps_to_cfg_events G f
  \<and> maps_only_from_table_domain G f"

primrec F_CFG_FIRST__table_recursive :: "
  nat
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain"
  where
    "F_CFG_FIRST__table_recursive 0 G f = f"
  | "F_CFG_FIRST__table_recursive (Suc n) G f = F_CFG_FIRST__table_recursive n G (F_CFG_FIRST__table__fp_one G f)"

definition F_CFG_FIRST__table__fp_invariant_02 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_02 G f w \<equiv>
  f w \<subseteq> cfgSTD_first_symbol_of_derivable_effect G w"

definition F_CFG_FIRST__table__fp_invariant_01 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_01 G f w \<equiv>
  None \<in> f w \<longrightarrow> (\<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = []\<rparr>})"

definition F_CFG_FIRST__table__fp_invariant_03 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_03 G f \<equiv>
  f [] \<subseteq> {None}"

definition F_CFG_FIRST__table__fp_invariant_04 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_04 G f \<equiv>
  F_CFG_FIRST__table__fp_one G f [] = {None}"

definition F_CFG_FIRST__table__fp_invariant_05 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_05 G f \<equiv>
  \<forall>x l. teB x # l \<in> F_CFG_FIRST__table_domain G \<longrightarrow> F_CFG_FIRST__table__fp_one G f (teB x # l) = {Some x}"

definition F_CFG_FIRST__table__fp_invariant_06 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_06 G f \<equiv>
   (\<forall>x l. f (teB x # l) \<subseteq> {Some x})"

definition F_CFG_FIRST__table__fp_invariant_07 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_07 G f \<equiv>
  \<forall>x A. 
    x \<in> f [teA A]
    \<longrightarrow> (\<exists>v. 
          \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G
          \<and> x \<in> f v)"

definition F_CFG_FIRST__table__fp_invariant_08 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_08 G f \<equiv>
  \<forall>A v x. 
    \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G
    \<and> x \<in> f v
    \<longrightarrow> x \<in> F_CFG_FIRST__table__fp_one G f [teA A]"

definition F_CFG_FIRST__table__fp_invariant_09 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_09 G f \<equiv>
  \<forall>B u A w x. 
    \<lparr>prod_lhs = B, prod_rhs = u @ teA A # w\<rparr> \<in> cfg_productions G
    \<and> Some x \<in> f [teA A]
    \<longrightarrow> Some x \<in> F_CFG_FIRST__table__fp_one G f (teA A # w)"

definition F_CFG_FIRST__table__fp_invariant_10 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_10 G f \<equiv>
  \<forall>B u A w. 
    \<lparr>prod_lhs = B, prod_rhs = u @ teA A # w\<rparr> \<in> cfg_productions G
    \<and> None \<in> f [teA A]
    \<and> None \<in> f w
    \<longrightarrow> None \<in> F_CFG_FIRST__table__fp_one G f (teA A # w)"

definition F_CFG_FIRST__table__fp_invariant_11 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_11 G f \<equiv>
  \<forall>A x w. 
    None \<in> f [teA A]
    \<and> x \<in> f w
    \<and> teA A # w \<in> F_CFG_FIRST__table_domain G
    \<longrightarrow> x \<in> F_CFG_FIRST__table__fp_one G f (teA A # w)"

definition F_CFG_FIRST__table__fp_invariant_12 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_12 G f \<equiv>
  \<forall>A x w. 
    [teA A] \<in> F_CFG_FIRST__table_domain G 
    \<longrightarrow> None \<notin> f [teA A] 
    \<longrightarrow> Some x \<in> f (teA A # w) 
    \<longrightarrow> Some x \<in> f [teA A]"

definition F_CFG_FIRST__table__fp_invariant_13 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_13 G f \<equiv>
  \<forall>w A x. 
    [teA A] \<in> F_CFG_FIRST__table_domain G 
    \<longrightarrow> Some x \<in> f (teA A # w) 
    \<longrightarrow> Some x \<notin> f w 
    \<longrightarrow> Some x \<in> f [teA A]"

definition F_CFG_FIRST__table__fp_invariant_14 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_14 G f \<equiv>
  \<forall>A. 
    \<lparr>prod_lhs = A, prod_rhs = []\<rparr> \<in> cfg_productions G 
    \<longrightarrow> None \<in> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table__fp_one G f) [teA A]"

definition F_CFG_FIRST__table__fp_invariant_15 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_15 G f \<equiv>
  \<forall>A w. 
    \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<in> cfg_productions G
    \<and> None \<in> f w 
    \<longrightarrow> None \<in> F_CFG_FIRST__table__fp_one G f [teA A]"

definition F_CFG_FIRST__table__fp_invariant_16 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_16 G f \<equiv>
  \<forall>w \<in> F_CFG_FIRST__table_domain G. 
    setB w = {}
    \<and> w \<noteq> []
    \<and> (\<forall>i < length w. None \<in> f [w ! i])
    \<longrightarrow> None \<in> F_CFG_FIRST__table_recursive (length w) G f w"

definition F_CFG_FIRST__table__fp_invariant_17 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariant_17 G f \<equiv>
  \<forall>w \<in> F_CFG_FIRST__table_domain G. 
    None \<in> f w
    \<longrightarrow> 
      setB w = {}
      \<and> (\<forall>i < length w. None \<in> f [w ! i])"

definition F_CFG_FIRST__table__fp_invariants :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) F_CFG_FIRST__table_domain
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__table__fp_invariants G f \<equiv>
  (\<forall>w. F_CFG_FIRST__table__fp_invariant_02 G f w
      \<and> F_CFG_FIRST__table__fp_invariant_01 G f w)
  \<and> F_CFG_FIRST__table__fp_invariant_03 G f
  \<and> F_CFG_FIRST__table__fp_invariant_04 G f
  \<and> F_CFG_FIRST__table__fp_invariant_05 G f
  \<and> F_CFG_FIRST__table__fp_invariant_06 G f
  \<and> F_CFG_FIRST__table__fp_invariant_07 G f
  \<and> F_CFG_FIRST__table__fp_invariant_08 G f
  \<and> F_CFG_FIRST__table__fp_invariant_09 G f
  \<and> F_CFG_FIRST__table__fp_invariant_10 G f
  \<and> F_CFG_FIRST__table__fp_invariant_11 G f
  \<and> F_CFG_FIRST__table__fp_invariant_12 G f
  \<and> F_CFG_FIRST__table__fp_invariant_13 G f
  \<and> F_CFG_FIRST__table__fp_invariant_14 G f
  \<and> F_CFG_FIRST__table__fp_invariant_15 G f
  \<and> F_CFG_FIRST__table__fp_invariant_16 G f
  \<and> F_CFG_FIRST__table__fp_invariant_17 G f
  \<and> F_CFG_FIRST__table__fp_valid_input G f"

lemma inSigma: "
  maps_to_cfg_events G f
  \<Longrightarrow> Some x \<in> f w
  \<Longrightarrow> x \<in> cfg_events G"
  apply(simp add: maps_to_cfg_events_def)
  apply(erule_tac
      x = "w"
      in allE)
  apply(simp add: option_to_setMap_def)
  apply(auto)
  done

lemma table_domain__Cons_rhs: "
  \<lparr>prod_lhs = y, prod_rhs = w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> w \<in> F_CFG_FIRST__table_domain G"
  apply(simp add: F_CFG_FIRST__table_domain_def)
  apply(rule disjI2)
  apply(rule_tac
      x = "\<lparr>prod_lhs = y, prod_rhs = w\<rparr>"
      in exI)
  apply(auto)
  apply(rule suffixes_intro2)
  done

lemma emptyIntable_domain: "
  cfg_has_production G
  \<Longrightarrow> [] \<in> F_CFG_FIRST__table_domain G"
  apply(simp add: F_CFG_FIRST__table_domain_def)
  apply(simp add: cfg_has_production_def)
  apply(subgoal_tac "\<exists>e. e \<in> cfg_productions G")
   defer
   apply(rule emptySetE)
   apply(auto)
  apply(rename_tac e x)(*strict*)
  apply(erule_tac
      x = "e"
      in allE)
  apply(auto)
  apply(subgoal_tac "[] \<in> suffixes (prod_rhs e)")
   apply(rename_tac e x)(*strict*)
   apply(blast)
  apply(rename_tac e x)(*strict*)
  apply(rule suffixes_intro2_prime)
  done

lemma table_domain__Cons_lhs: "
  \<lparr>prod_lhs = y, prod_rhs = w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> [teA y] \<in> F_CFG_FIRST__table_domain G"
  apply(simp add: F_CFG_FIRST__table_domain_def)
  apply(auto)
  done

lemma table_domainDecomp: "
  a # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> w \<in> F_CFG_FIRST__table_domain G"
  apply(simp add: F_CFG_FIRST__table_domain_def)
  apply(auto)
   apply(rename_tac e)(*strict*)
   apply(erule_tac
      x = "e"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "[] \<in> suffixes (prod_rhs e)")
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(rule suffixes_intro2_prime)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x = "e"
      in allE)
  apply(clarsimp)
  apply(rule suffixes_contra1)
   apply(rename_tac e)(*strict*)
   apply(blast)+
  done

lemma table_domainDecomp2: "
  w1 @ a # w2 \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> a # w2 \<in> F_CFG_FIRST__table_domain G"
  apply(subgoal_tac "w1 @ a # w2 \<in> F_CFG_FIRST__table_domain G \<longrightarrow> a # w2 \<in> F_CFG_FIRST__table_domain G")
   apply(blast)
  apply(thin_tac "w1 @ a # w2 \<in> F_CFG_FIRST__table_domain G")
  apply(induct_tac w1)
   apply(clarsimp)
  apply(rename_tac aa list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "list @ a # w2 \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac aa list)(*strict*)
   apply(blast)
  apply(rename_tac aa list)(*strict*)
  apply(rule table_domainDecomp)
  apply(auto)
  done

lemma NonTerminalFromtable_domainisNonterminal: "
  valid_cfg G
  \<Longrightarrow> teA A # w2 \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> A \<in> cfg_nonterminals G"
  apply(simp add: F_CFG_FIRST__table_domain_def valid_cfg_def)
  apply(auto)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x = "e"
      in ballE)
   apply(rename_tac e)(*strict*)
   apply(auto)
  apply(rename_tac e)(*strict*)
  apply(rule_tac
      ?w1.0 = "[]"
      in suffixes_setA_2)
   apply(rename_tac e)(*strict*)
   apply(blast)
  apply(rename_tac e)(*strict*)
  apply(auto)
  done

lemma table_domainDecomp3: "
  cfg_every_nonterminal_on_some_left_hand_side G
  \<Longrightarrow> valid_cfg G
  \<Longrightarrow> w1 @ teA A # w2 \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> [teA A] \<in> F_CFG_FIRST__table_domain G"
  apply(subgoal_tac "A \<in> cfg_nonterminals G")
   apply(simp add: F_CFG_FIRST__table_domain_def)
   apply(auto)
    apply(rename_tac e)(*strict*)
    apply(subgoal_tac "w1 = []")
     apply(rename_tac e)(*strict*)
     apply(subgoal_tac "w2 = []")
      apply(rename_tac e)(*strict*)
      apply(auto)
    apply(rename_tac e)(*strict*)
    apply(rule_tac
      ?w2.0 = "w2"
      in length_1_context_both_empty_left)
    apply(rule sym)
    apply(auto)
   apply(rename_tac e)(*strict*)
   apply(simp add: cfg_every_nonterminal_on_some_left_hand_side_def)
   apply(auto)
  apply(rule_tac
      ?w2.0 = "w2"
      in NonTerminalFromtable_domainisNonterminal)
   apply(auto)
  apply(rule table_domainDecomp2)
  apply(auto)
  done

lemma table_domain__Cons_lhs2: "
  cfg_every_nonterminal_on_some_left_hand_side G
  \<Longrightarrow> valid_cfg G
  \<Longrightarrow> w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> a \<in> setA w
  \<Longrightarrow> [teA a] \<in> F_CFG_FIRST__table_domain G"
  apply(subgoal_tac "\<exists>w1 w2. w1@[teA a]@w2=w")
   prefer 2
   apply(rule setA_decomp)
   apply(force)
  apply(erule exE)+
  apply(rename_tac w1 w2)(*strict*)
  apply(rule table_domainDecomp3)
    apply(rename_tac w1 w2)(*strict*)
    apply(force)
   apply(rename_tac w1 w2)(*strict*)
   apply(force)
  apply(rename_tac w1 w2)(*strict*)
  apply(force)
  done

lemma F_CFG_FIRST__TRANSFER_AT_kleene_starT: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G (\<lambda>x. {})"
  apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_02_def option_to_setMap_def F_CFG_FIRST__table__fp_invariant_01_def F_CFG_FIRST__table__fp_invariant_03_def F_CFG_FIRST__table__fp_invariant_04_def F_CFG_FIRST__table__fp_invariant_05_def F_CFG_FIRST__table__fp_invariant_06_def F_CFG_FIRST__table__fp_invariant_07_def F_CFG_FIRST__table__fp_invariant_08_def F_CFG_FIRST__table__fp_invariant_09_def F_CFG_FIRST__table__fp_invariant_10_def F_CFG_FIRST__table__fp_invariant_11_def F_CFG_FIRST__table__fp_invariant_12_def F_CFG_FIRST__table__fp_invariant_13_def F_CFG_FIRST__table__fp_invariant_14_def F_CFG_FIRST__table__fp_invariant_15_def F_CFG_FIRST__table__fp_invariant_16_def F_CFG_FIRST__table__fp_invariant_17_def )
  apply(rule conjI)
   apply(simp add: F_CFG_FIRST__table__fp_one_def)
   apply(rule emptyIntable_domain)
   apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
  apply(rule conjI)
   apply(auto)
    apply(rename_tac x l xa)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_one_def)
   apply(rename_tac x l)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(rename_tac A)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(subgoal_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac A)(*strict*)
   apply(subgoal_tac "[] \<in> F_CFG_FIRST__table_domain G")
    apply(rename_tac A)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x = "[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac A)(*strict*)
   apply(rule emptyIntable_domain)
   apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
  apply(rename_tac A)(*strict*)
  apply(rule table_domain__Cons_lhs)
  apply(blast)
  done

lemma F_CFG_FIRST__table_domain_in_cfg_events: "
  valid_cfg G
  \<Longrightarrow> teB b # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> b \<in> cfg_events G"
  apply(simp add: F_CFG_FIRST__table_domain_def)
  apply(auto)
  apply(rename_tac e)(*strict*)
  apply(case_tac e)
  apply(rename_tac e prod_lhs prod_rhsa)(*strict*)
  apply(auto)
  apply(rename_tac prod_lhs prod_rhs)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(rename_tac prod_lhsa prod_rhsa)(*strict*)
  apply(auto)
  apply(erule_tac
      x = "\<lparr>prod_lhs = prod_lhsa, prod_rhs = prod_rhsa\<rparr>"
      in ballE)
   apply(rename_tac prod_lhsa prod_rhsa)(*strict*)
   apply(auto)
  apply(rename_tac prod_lhs prod_rhs)(*strict*)
  apply(rule_tac
      A = "setB prod_rhs"
      in set_mp)
   apply(rename_tac prod_lhs prod_rhs)(*strict*)
   apply(auto)
  apply(rename_tac prod_lhs prod_rhs)(*strict*)
  apply(rule suffixes_setB_1)
  apply(blast)
  done

lemma F_CFG_FIRST__termLem1: "
  F_CFG_FIRST__table__fp_one G f \<noteq> f
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)"
  apply(unfold F_CFG_FIRST__table__fp_valid_input_def option_to_setMap_def WrapInSome_def F_CFG_FIRST__table__fp_one_def maps_to_cfg_events_def maps_only_from_table_domain_def)
  apply(auto)
  apply(rename_tac x xa)(*strict*)
  apply(case_tac x)
   apply(rename_tac x xa)(*strict*)
   apply(auto)
  apply(rename_tac xa a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac xa a list aa)(*strict*)
   apply(auto)
   apply(rename_tac xa list aa)(*strict*)
   apply(case_tac "None \<in> f ([teA aa])")
    apply(rename_tac xa list aa)(*strict*)
    apply(auto)
  apply(rename_tac list b)(*strict*)
  apply(rule_tac
      w = "list"
      in F_CFG_FIRST__table_domain_in_cfg_events)
   apply(rename_tac list b)(*strict*)
   apply(blast)
  apply(rename_tac list b)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_preserves_F_CFG_FIRST__table__fp_valid_input: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)"
  apply(case_tac "F_CFG_FIRST__table__fp_one G f = f")
   apply(clarsimp)
  apply(rule F_CFG_FIRST__termLem1)
   apply(auto)
  done

lemma F_CFG_FIRST__table__fp_one_trans: "
  x \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> f x \<subseteq> F_CFG_FIRST__table__fp_one G f x"
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  done

lemma finiteFirstDomStrings: "
  valid_cfg G
  \<Longrightarrow> finite (F_CFG_FIRST__table_domain G)"
  apply(simp add: F_CFG_FIRST__table_domain_def)
  apply(auto)
   apply(rule_tac
      B = "{x. \<exists>A. x = Cons (teA A) [] \<and> A \<in> cfg_nonterminals G}"
      in Finite_Set.finite_subset)
    apply(clarsimp)
    apply(rename_tac e)(*strict*)
    apply(simp add: valid_cfg_def)
   apply(rule_tac
      s = "((\<lambda>A. Cons (teA A) []) ` (cfg_nonterminals G))"
      and t = "{Cons (teA A) [] |A. A \<in> cfg_nonterminals G}"
      in ssubst)
    apply(auto)
   apply(rule_tac
      h = "\<lambda>A. Cons (teA A) []"
      in finite_imageI)
   apply(simp add: valid_cfg_def)
  apply(rule_tac
      s = "\<Union> {y. \<exists>x. y = (\<lambda>x. suffixes (prod_rhs x)) x \<and> x \<in> (cfg_productions G)}"
      and t = "{ws. \<exists>e. e \<in> cfg_productions G \<and> ws \<in> suffixes (prod_rhs e)}"
      in ssubst)
   apply(blast)
  apply(rule finite_big_union)
   apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule suffixes_finite)
  done

lemma changeOnlyOnOKPos: "
  F_CFG_FIRST__table__fp_one G f x \<noteq> f x
  \<Longrightarrow> maps_only_from_table_domain G f
  \<Longrightarrow> x \<in> F_CFG_FIRST__table_domain G"
  apply(simp add: F_CFG_FIRST__table__fp_one_def maps_only_from_table_domain_def)
  apply(auto)
  done

lemma F_CFG_FIRST__sumSmaller: "
  valid_cfg G
  \<Longrightarrow> maps_only_from_table_domain G f
  \<Longrightarrow> maps_to_cfg_events G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_one G f \<noteq> f
  \<Longrightarrow> (\<Sum>x \<in> F_CFG_FIRST__table_domain G. card (WrapInSome (cfg_events G) - F_CFG_FIRST__table__fp_one G f x)) < (\<Sum>x \<in> F_CFG_FIRST__table_domain G. card (WrapInSome (cfg_events G) - f x))"
  apply(subgoal_tac "F_CFG_FIRST__table__fp_one G f \<noteq> f \<Longrightarrow> valid_cfg G \<Longrightarrow> maps_only_from_table_domain G f \<Longrightarrow> maps_to_cfg_events G f \<Longrightarrow> (\<Sum>x \<in> F_CFG_FIRST__table_domain G. card (WrapInSome (cfg_events G) - F_CFG_FIRST__table__fp_one G f x)) < (\<Sum>x \<in> F_CFG_FIRST__table_domain G. card (WrapInSome (cfg_events G) - f x)) ")
   apply(blast)
  apply(rule strictly_smaller_set_map_has_strictly_fewer_image_elements)
     apply(auto)
     apply(rename_tac x)(*strict*)
     apply(rule finite_diff_WrapInSome)
     apply(simp add: valid_cfg_def)
    apply(rename_tac x xa)(*strict*)
    apply(subgoal_tac "xa \<in> F_CFG_FIRST__table__fp_one G f x")
     apply(rename_tac x xa)(*strict*)
     apply(blast)
    apply(rename_tac x xa)(*strict*)
    apply(rule_tac
      A = "f x"
      in set_mp)
     apply(rename_tac x xa)(*strict*)
     apply(rule_tac F_CFG_FIRST__table__fp_one_trans)
     apply(simp add: maps_only_from_table_domain_def)
     apply(auto)
   apply(subgoal_tac "\<exists>x. F_CFG_FIRST__table__fp_one G f x \<noteq> f x")
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    defer
    apply(rule unequal_maps_differ_somewhere)
    apply(blast)
   apply(rule finiteFirstDomStrings)
   apply(blast)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      x = "x"
      in bexI)
   apply(rename_tac x)(*strict*)
   apply(rule rev_subset)
    apply(rename_tac x)(*strict*)
    apply(rule Orderings.order_le_neq_trans)
     apply(rename_tac x)(*strict*)
     apply(rule_tac F_CFG_FIRST__table__fp_one_trans)
     apply(rule_tac
      f = "f"
      in changeOnlyOnOKPos)
      apply(rename_tac x)(*strict*)
      apply(blast)
     apply(rename_tac x)(*strict*)
     apply(simp add: maps_only_from_table_domain_def)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      f = "f"
      in changeOnlyOnOKPos)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(simp add: maps_only_from_table_domain_def)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_one G f \<noteq> f")
  apply(thin_tac "F_CFG_FIRST__table__fp_one G f x \<noteq> f x")
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(auto)
   apply(rename_tac x xa)(*strict*)
   apply(case_tac xa)
    apply(rename_tac x xa)(*strict*)
    apply(auto)
    apply(rename_tac x)(*strict*)
    apply(simp add: WrapInSome_def maps_to_cfg_events_def option_to_setMap_def)+
   apply(rename_tac x a)(*strict*)
   apply(auto)
  apply(rename_tac x xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac x xa)(*strict*)
   apply(auto)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(auto)
    apply(simp add: WrapInSome_def)
   apply(rename_tac a list)(*strict*)
   apply(case_tac a)
    apply(rename_tac a list aa)(*strict*)
    apply(auto)
     apply(rename_tac list aa)(*strict*)
     apply(case_tac list)
      apply(rename_tac list aa)(*strict*)
      apply(auto)
     apply(rename_tac aa)(*strict*)
     apply(simp add: WrapInSome_def maps_to_cfg_events_def option_to_setMap_def)+
  apply(rename_tac x a)(*strict*)
  apply(case_tac x)
   apply(rename_tac x a)(*strict*)
   apply(auto)
  apply(rename_tac a aa list)(*strict*)
  apply(case_tac aa)
   apply(rename_tac a aa list ab)(*strict*)
   apply(auto)
   apply(rename_tac a list ab)(*strict*)
   apply(case_tac "None \<in> f [teA ab]")
    apply(rename_tac a list ab)(*strict*)
    apply(simp add: maps_to_cfg_events_def option_to_setMap_def)
    apply(auto)
  apply(rename_tac list b)(*strict*)
  apply(subgoal_tac "b \<in> cfg_events G")
   apply(rename_tac list b)(*strict*)
   apply(blast)
  apply(rename_tac list b)(*strict*)
  apply(rule F_CFG_FIRST__table_domain_in_cfg_events)
   apply(rename_tac list b)(*strict*)
   apply(blast)
  apply(rename_tac list b)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB1: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> a = teB b
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_02 G (F_CFG_FIRST__table__fp_one G f) (a # w)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_02_def F_CFG_FIRST__table__fp_invariant_01_def F_CFG_FIRST__table__fp_valid_input_def cfgSTD_first_symbol_of_derivable_effect_def)
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "b\<in> cfg_events G \<and> x=Some b")
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = teB b # w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = teB b # w'\<rparr>}")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = Cons (teB b) w\<rparr>"
      in exI)
   apply(rule_tac
      x = "w"
      in exI)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
   apply(subgoal_tac "cfgSTD.derivation G (der1 \<lparr>cfg_conf = teB b # w\<rparr>)")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(simp add: der1_def)
   apply(rename_tac x)(*strict*)
   apply(rule cfgSTD.der1_is_derivation)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(case_tac "teB b # w \<notin> F_CFG_FIRST__table_domain G")
   apply(rename_tac x)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac x)(*strict*)
   apply(rule F_CFG_FIRST__table_domain_in_cfg_events)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_05_def)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB2: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> a = teB b
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_01 G (F_CFG_FIRST__table__fp_one G f) (a # w)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_02_def F_CFG_FIRST__table__fp_invariant_01_def F_CFG_FIRST__table__fp_valid_input_def cfgSTD_first_symbol_of_derivable_effect_def)
  apply(auto)
  apply(unfold option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
  apply(case_tac "teB b # w \<notin> F_CFG_FIRST__table_domain G")
   apply(auto)
  done

lemma DerivationExists: "
  F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> Some x \<in> f w
  \<Longrightarrow> \<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w'\<rparr>}"
  apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
  apply(erule conjE)
  apply(erule_tac
      x = "w"
      in allE)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_02_def)
  apply(erule conjE)
  apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def option_to_setMap_def)
  apply(blast)
  done

lemma DerivationExists2: "
  F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> None \<in> f [teA A]
  \<Longrightarrow> \<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}"
  apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
  apply(erule conjE)
  apply(erule_tac
      x = "Cons (teA A) []"
      in allE)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_01_def)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_1: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> teA A # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> x \<in> f w
  \<Longrightarrow> None \<in> f [teA A]
  \<Longrightarrow> x \<in> cfgSTD_first_symbol_of_derivable_effect G (teA A # w)"
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_02 G f [teA A]")
   prefer 2
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_02_def)
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_02 G f w")
   prefer 2
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_02_def)
  apply(subgoal_tac "None \<in> cfgSTD_first_symbol_of_derivable_effect G [teA A]")
   prefer 2
   apply(force)
  apply(subgoal_tac "x \<in> cfgSTD_first_symbol_of_derivable_effect G w")
   prefer 2
   apply(force)
  apply(thin_tac "F_CFG_FIRST__table__fp_invariants G f")
  apply(thin_tac "teA A # w \<in> F_CFG_FIRST__table_domain G")
  apply(thin_tac "x \<in> f w")
  apply(thin_tac "None \<in> f [teA A]")
  apply(thin_tac "f [teA A] \<subseteq> cfgSTD_first_symbol_of_derivable_effect G [teA A]")
  apply(thin_tac "f w \<subseteq> cfgSTD_first_symbol_of_derivable_effect G w")
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)")
  apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
  apply(case_tac x)
   apply(clarsimp)
   apply(rename_tac d da)(*strict*)
   apply(rename_tac d1 d2)
   apply(rename_tac d1 d2)(*strict*)
   apply(subgoal_tac "\<exists>x. maximum_of_domain d1 x")
    apply(rename_tac d1 d2)(*strict*)
    prefer 2
    apply(rule_tac cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac d1 d2)(*strict*)
   apply(subgoal_tac "\<exists>x. maximum_of_domain d2 x")
    apply(rename_tac d1 d2)(*strict*)
    prefer 2
    apply(rule_tac cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac d1 d2)(*strict*)
   apply(erule_tac exE)+
   apply(rename_tac d1 d2 x xa)(*strict*)
   apply(rename_tac m1 m2)
   apply(rename_tac d1 d2 m1 m2)(*strict*)
   apply(rule_tac
      x = "derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) d2 m1"
      in exI)
   apply(rule_tac
      s = "[teA A] @ w"
      and t = "teA A#w"
      in ssubst)
    apply(rename_tac d1 d2 m1 m2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 m1 m2)(*strict*)
   apply(rule concatExtendIsFromTo)
       apply(rename_tac d1 d2 m1 m2)(*strict*)
       apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
      apply(rename_tac d1 d2 m1 m2)(*strict*)
      apply(blast)
     apply(rename_tac d1 d2 m1 m2)(*strict*)
     apply(blast)
    apply(rename_tac d1 d2 m1 m2)(*strict*)
    apply(blast)
   apply(rename_tac d1 d2 m1 m2)(*strict*)
   apply(blast)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a d da w')(*strict*)
  apply(rename_tac a d1 d2 w')
  apply(rename_tac a d1 d2 w')(*strict*)
  apply(subgoal_tac "\<exists>x. maximum_of_domain d1 x")
   apply(rename_tac a d1 d2 w')(*strict*)
   prefer 2
   apply(rule_tac cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac a d1 d2 w')(*strict*)
  apply(subgoal_tac "\<exists>x. maximum_of_domain d2 x")
   apply(rename_tac a d1 d2 w')(*strict*)
   prefer 2
   apply(rule_tac cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac a d1 d2 w')(*strict*)
  apply(erule_tac exE)+
  apply(rename_tac a d1 d2 w' x xa)(*strict*)
  apply(rename_tac m1 m2)
  apply(rename_tac a d1 d2 w' m1 m2)(*strict*)
  apply(rule_tac
      x = "derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) d2 m1"
      in exI)
  apply(rule_tac
      x="w'"
      in exI)
  apply(rule_tac
      s = "[teA A] @ w"
      and t = "teA A#w"
      in ssubst)
   apply(rename_tac a d1 d2 w' m1 m2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a d1 d2 w' m1 m2)(*strict*)
  apply(rule concatExtendIsFromTo)
      apply(rename_tac a d1 d2 w' m1 m2)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
     apply(rename_tac a d1 d2 w' m1 m2)(*strict*)
     apply(blast)
    apply(rename_tac a d1 d2 w' m1 m2)(*strict*)
    apply(blast)
   apply(rename_tac a d1 d2 w' m1 m2)(*strict*)
   apply(blast)
  apply(rename_tac a d1 d2 w' m1 m2)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_2: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> teA A # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> Some x \<in> f [teA A]
  \<Longrightarrow> Some x \<in> cfgSTD_first_symbol_of_derivable_effect G (teA A # w)"
  apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
  apply(auto)
   apply(rule inSigma)
    apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
    apply(blast,blast)
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = Cons (teA A) []\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = (Cons (teB x) w')\<rparr>}")
   defer
   apply(rule DerivationExists)
    apply(blast)
   apply(blast)
  apply(auto)
  apply(rename_tac d w')(*strict*)
  apply(subgoal_tac "\<exists>x. maximum_of_domain d x")
   apply(rename_tac d w')(*strict*)
   apply(erule_tac exE)+
   apply(rename_tac d w' xa)(*strict*)
   apply(rename_tac m)
   apply(rename_tac d w' m)(*strict*)
   apply(rule_tac
      x = "derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)"
      in exI)
   apply(rule_tac
      x = "w' @ w"
      in exI)
   defer
   apply(rename_tac d w')(*strict*)
   apply(rule_tac cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac d w' m)(*strict*)
  apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>) \<lparr>cfg_conf = Cons (teA A) []\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>) \<lparr>cfg_conf = (Cons (teB x) w')\<rparr>)}")
   apply(rename_tac d w' m)(*strict*)
   prefer 2
   apply(rule contextExtendIsFromTo)
      apply(rename_tac d w' m)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
     apply(rename_tac d w' m)(*strict*)
     apply(blast)+
  apply(rename_tac d w' m)(*strict*)
  apply(auto)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_3: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> teA A # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> Some x \<in> f xa
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = xa\<rparr> \<in> cfg_productions G
  \<Longrightarrow> Some x \<in> cfgSTD_first_symbol_of_derivable_effect G (teA A # w)"
  apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
  apply(auto)
   apply(rule inSigma)
    apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
    apply(blast,blast)
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = xa\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = Cons (teB x) w'\<rparr>}")
   defer
   apply(rule DerivationExists)
    apply(blast)
   apply(blast)
  apply(auto)
  apply(rename_tac d w')(*strict*)
  apply(subgoal_tac "\<exists>x. maximum_of_domain d x")
   apply(rename_tac d w')(*strict*)
   apply(erule_tac exE)+
   apply(rename_tac d w' xb)(*strict*)
   apply(rename_tac m)
   apply(rename_tac d w' m)(*strict*)
   apply(rule_tac
      x = "derivation_append (\<lambda>n. (if (n = 0) then Some (pair None \<lparr>cfg_conf = Cons (teA A) w\<rparr>) else (if (n = Suc 0) then Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = xa\<rparr>) \<lparr>cfg_conf = xa @ w\<rparr>) else None))) (derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) (Suc 0)"
      in exI)
   apply(rename_tac d w' m)(*strict*)
   apply(rule_tac
      x = "w' @ w"
      in exI)
   defer
   apply(rename_tac d w')(*strict*)
   apply(rule_tac cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac d w' m)(*strict*)
  apply(rule_tac
      dJ = "\<lparr>cfg_conf=xa @ w\<rparr>"
      in cfgSTD.concatIsFromTo)
     apply(rename_tac d w' m)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
     apply(auto)
      apply(rename_tac d w' m n xaa)(*strict*)
      apply(simp add: cfgSTD_step_relation_def)
      apply(rule_tac
      x = "[]"
      in exI)
      apply(rule_tac
      x = "w"
      in exI)
      apply(simp add: concat_asso)
     apply(rename_tac d w' m n xaa i)(*strict*)
     apply(case_tac i)
      apply(rename_tac d w' m n xaa i)(*strict*)
      apply(auto)
    apply(rename_tac d w' m)(*strict*)
    apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>) \<lparr>cfg_conf = xa\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>) \<lparr>cfg_conf = Cons (teB x) w'\<rparr>)}")
     apply(rename_tac d w' m)(*strict*)
     prefer 2
     apply(rule contextExtendIsFromTo)
        apply(rename_tac d w' m)(*strict*)
        apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
       apply(rename_tac d w' m)(*strict*)
       apply(blast)+
    apply(rename_tac d w' m)(*strict*)
    apply(auto)
   apply(rename_tac d w' m)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac d w' m)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_SOUND_EMPTY_F_CFG_FIRST__table__fp_invariant_02: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_02 G (F_CFG_FIRST__table__fp_one G f) []"
  apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_02_def F_CFG_FIRST__table__fp_invariant_01_def F_CFG_FIRST__table__fp_valid_input_def cfgSTD_first_symbol_of_derivable_effect_def option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
  apply(clarsimp)
  apply(rule_tac
      x = "\<lambda>n. (if n = 0 then (Some (pair None \<lparr>cfg_conf = []\<rparr>)) else None)"
      in exI)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_SOUND_EMPTY_F_CFG_FIRST__table__fp_invariant_01: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_01 G (F_CFG_FIRST__table__fp_one G f) []"
  apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_02_def F_CFG_FIRST__table__fp_invariant_01_def F_CFG_FIRST__table__fp_valid_input_def cfgSTD_first_symbol_of_derivable_effect_def option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
  apply(auto)
  apply(rule_tac
      x = "\<lambda>n. (if n = 0 then (Some (pair None \<lparr>cfg_conf = []\<rparr>)) else None)"
      in exI)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
  apply(auto)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(auto)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_SOUND_EMPTY_step: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_02 G (F_CFG_FIRST__table__fp_one G f) (teA A # w) \<and> F_CFG_FIRST__table__fp_invariant_01 G (F_CFG_FIRST__table__fp_one G f) (teA A # w)"
  apply(auto)
   apply(simp add: F_CFG_FIRST__table__fp_invariant_02_def)
   apply(auto)
   apply(rename_tac x)(*strict*)
   apply(simp add: option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
   apply(case_tac "Cons (teA A) w \<notin> F_CFG_FIRST__table_domain G")
    apply(rename_tac x)(*strict*)
    apply(auto)
      apply(rename_tac x)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
      apply(erule conjE)
      apply(erule_tac
      x = "Cons (teA A) w"
      in allE)
      apply(auto)
      apply(simp add: F_CFG_FIRST__table__fp_invariant_02_def)
      apply(rule_tac
      A = "(f (Cons (teA A) w))"
      in set_mp)
       apply(rename_tac x)(*strict*)
       apply(simp add: option_to_setMap_def)
      apply(rename_tac x)(*strict*)
      apply(simp add: option_to_setMap_def)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(case_tac "None \<in> f (Cons (teA A) [])")
      apply(rename_tac x)(*strict*)
      apply(auto)
     apply(rename_tac x)(*strict*)
     apply(fold F_CFG_FIRST__table__fp_one_def)
     apply(rename_tac x)(*strict*)
     apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_1)
          apply(rename_tac x)(*strict*)
          apply(blast)+
    apply(rename_tac x)(*strict*)
    apply(case_tac w)
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
     prefer 2
     apply(rename_tac x a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac a list y)(*strict*)
     apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_2)
         apply(rename_tac a list y)(*strict*)
         apply(blast)+
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(rename_tac x xa)(*strict*)
    apply(case_tac w)
     apply(rename_tac x xa)(*strict*)
     apply(clarsimp)
     prefer 2
     apply(rename_tac x xa a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa a list y)(*strict*)
     apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_3)
          apply(rename_tac xa a list y)(*strict*)
          apply(blast)+
    apply(rename_tac x xa)(*strict*)
    prefer 3
    apply(simp add: F_CFG_FIRST__table__fp_invariant_01_def)
    apply(auto)
    apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)")
    apply(simp add: F_CFG_FIRST__table__fp_one_def)
    apply(case_tac "teA A # w \<notin> F_CFG_FIRST__table_domain G")
     apply(auto)
       apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
       apply(simp add: F_CFG_FIRST__table__fp_invariant_01_def)
      apply(case_tac w)
       apply(clarsimp)
       prefer 2
       apply(rename_tac a list)(*strict*)
       apply(clarsimp)
      prefer 3
      apply(rename_tac x)(*strict*)
      apply(case_tac w)
       apply(rename_tac x)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(rename_tac x a list)(*strict*)
       apply(clarsimp)
      apply(rename_tac x)(*strict*)
      prefer 3
      apply(case_tac "None \<in> f([teA A])")
       apply(auto)
      apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
      apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = Cons (teA A) []\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}")
       apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}")
        prefer 2
        apply(simp add: F_CFG_FIRST__table__fp_invariant_01_def)
       prefer 2
       apply(simp add: F_CFG_FIRST__table__fp_invariant_01_def)
      apply(auto)
      apply(rename_tac d da)(*strict*)
      apply(rename_tac d1 d2)
      apply(rename_tac d1 d2)(*strict*)
      apply(subgoal_tac "\<exists>x. maximum_of_domain d1 x")
       apply(rename_tac d1 d2)(*strict*)
       apply(subgoal_tac "\<exists>x. maximum_of_domain d2 x")
        apply(rename_tac d1 d2)(*strict*)
        apply(erule_tac exE)+
        apply(rename_tac d1 d2 x xa)(*strict*)
        apply(rename_tac m1 m2)
        apply(rename_tac d1 d2 m1 m2)(*strict*)
        apply(rule_tac
      x = "derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) d2 m1"
      in exI)
        prefer 2
        apply(rename_tac d1 d2)(*strict*)
        apply(rule_tac cfgSTD.to_has_maximum_of_domain)
        apply(rule cfgSTD.from_to_is_to)
        apply(blast)
       apply(rename_tac d1 d2 m1 m2)(*strict*)
       prefer 2
       apply(rename_tac d1 d2)(*strict*)
       apply(rule_tac cfgSTD.to_has_maximum_of_domain)
       apply(rule cfgSTD.from_to_is_to)
       apply(blast)
      apply(rename_tac d1 d2 m1 m2)(*strict*)
      apply(rule_tac
      s = "[teA A] @ w"
      and t = "teA A#w"
      in ssubst)
       apply(rename_tac d1 d2 m1 m2)(*strict*)
       apply(clarsimp)
      apply(rename_tac d1 d2 m1 m2)(*strict*)
      apply(rule concatExtendIsFromTo)
          apply(rename_tac d1 d2 m1 m2)(*strict*)
          apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
         apply(rename_tac d1 d2 m1 m2)(*strict*)
         apply(blast)+
     apply(rename_tac x)(*strict*)
     apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
     apply(simp add: F_CFG_FIRST__table__fp_invariant_01_def)
     apply(subgoal_tac "\<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = x\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}")
      apply(rename_tac x)(*strict*)
      prefer 2
      apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
     apply(rename_tac x)(*strict*)
     apply(simp add: F_CFG_FIRST__table__fp_invariant_01_def)
     apply(auto)
     apply(erule_tac
      x="x"
      in allE)
     apply(auto)
     apply(rename_tac x d)(*strict*)
     apply(subgoal_tac "\<exists>x. maximum_of_domain d x")
      apply(rename_tac x d)(*strict*)
      apply(auto)
      apply(rename_tac x d xa)(*strict*)
      prefer 2
      apply(rename_tac x d)(*strict*)
      apply(rule_tac cfgSTD.to_has_maximum_of_domain)
      apply(rule cfgSTD.from_to_is_to)
      apply(blast)
     apply(rename_tac x d xa)(*strict*)
     apply(rule_tac
      x = "derivation_append (\<lambda>n. (if(n = 0)then Some(pair None \<lparr>cfg_conf = [teA A]\<rparr>) else (if(n = Suc 0)then Some(pair (Some \<lparr>prod_lhs = A, prod_rhs = x\<rparr>) \<lparr>cfg_conf = x\<rparr>) else None) )) d (Suc 0)"
      in exI)
     apply(rename_tac x d xa)(*strict*)
     apply(rule cfgSTD.concatIsFromTo)
        apply(rename_tac x d xa)(*strict*)
        apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
        apply(auto)
       apply(rename_tac x d xa n xb)(*strict*)
       apply(simp add: cfgSTD_step_relation_def)
       apply(rule_tac
      x = "[]"
      in exI)
       apply(rule_tac
      x = "[]"
      in exI)
       apply(auto)
      apply(rename_tac x d xa n xb i)(*strict*)
      apply(case_tac i)
       apply(rename_tac x d xa n xb i)(*strict*)
       apply(auto)
     apply(rename_tac x d xa)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
    apply(simp add: F_CFG_FIRST__table__fp_invariant_01_def)
   apply(rename_tac x xa)(*strict*)
   apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_02 G f xa")
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariant_02_def)
   apply(subgoal_tac "x\<in> cfgSTD_first_symbol_of_derivable_effect G xa")
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(thin_tac "f xa \<subseteq> cfgSTD_first_symbol_of_derivable_effect G xa")
   apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
   apply(case_tac x)
    apply(rename_tac x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa d)(*strict*)
    apply(rename_tac xa d)
    apply(subgoal_tac "\<exists>x. maximum_of_domain d x")
     apply(rename_tac xa d)(*strict*)
     apply(erule_tac exE)+
     apply(rename_tac xa d x)(*strict*)
     apply(rename_tac m)
     apply(rename_tac xa d m)(*strict*)
     apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = xa\<rparr> \<lparr>cfg_conf = xa\<rparr> ) d (Suc 0)"
      in exI)
     apply(rename_tac xa d m)(*strict*)
     prefer 2
     apply(rename_tac xa d)(*strict*)
     apply(rule_tac cfgSTD.to_has_maximum_of_domain)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac xa d m)(*strict*)
    prefer 2
    apply(rename_tac x xa a)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa a d w')(*strict*)
    apply(subgoal_tac "\<exists>x. maximum_of_domain d x")
     apply(rename_tac xa a d w')(*strict*)
     apply(erule_tac exE)+
     apply(rename_tac xa a d w' x)(*strict*)
     apply(rename_tac m)
     apply(rename_tac xa a d w' m)(*strict*)
     apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = xa\<rparr> \<lparr>cfg_conf = xa\<rparr> ) d (Suc 0)"
      in exI)
     apply(rename_tac xa a d w' m)(*strict*)
     prefer 2
     apply(rename_tac xa a d w')(*strict*)
     apply(rule_tac cfgSTD.to_has_maximum_of_domain)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac xa a d w' m)(*strict*)
    apply(rule_tac
      x="w'"
      in exI)
    apply(rule_tac
      dJ="\<lparr>cfg_conf=xa\<rparr>"
      in cfgSTD.concatIsFromTo)
       apply(rename_tac xa a d w' m)(*strict*)
       apply(subgoal_tac "cfgSTD.derivation G (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = xa\<rparr> \<lparr>cfg_conf = xa\<rparr>)")
        apply(rename_tac xa a d w' m)(*strict*)
        apply(simp add: der2_def cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
        apply(force)
       apply(rename_tac xa a d w' m)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(simp add: cfgSTD_step_relation_def)
       apply(force)
      apply(rename_tac xa a d w' m)(*strict*)
      apply(force)
     apply(rename_tac xa a d w' m)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac xa a d w' m)(*strict*)
    apply(blast)
   apply(rename_tac xa d m)(*strict*)
   apply(subgoal_tac "cfgSTD.derivation G (derivation_append (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = xa\<rparr> \<lparr>cfg_conf = xa\<rparr>) d (Suc 0))")
    apply(rename_tac xa d m)(*strict*)
    apply(simp add: der2_def derivation_append_def cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
    apply(force)
   apply(rename_tac xa d m)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac xa d m)(*strict*)
     apply(rule cfgSTD.der2_is_derivation)
     apply(simp add: cfgSTD_step_relation_def)
     apply(force)
    apply(rename_tac xa d m)(*strict*)
    apply(simp add: der2_def derivation_append_def cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
   apply(rename_tac xa d m)(*strict*)
   apply(simp add: der2_def derivation_append_def cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
   apply(clarsimp)
   apply(rename_tac xa d m n x)(*strict*)
   apply(case_tac "d 0")
    apply(rename_tac xa d m n x)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa d m n x a)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_02 G f [teA A]")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_02_def)
  apply(force)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_SOUND_EMPTY: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_02 G (F_CFG_FIRST__table__fp_one G f) w \<and> F_CFG_FIRST__table__fp_invariant_01 G (F_CFG_FIRST__table__fp_one G f) w"
  apply(induct w)
   apply(rule conjI)
    apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_SOUND_EMPTY_F_CFG_FIRST__table__fp_invariant_02)
      apply(force)
     apply(force)
    apply(force)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_SOUND_EMPTY_F_CFG_FIRST__table__fp_invariant_01)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac a w)(*strict*)
  apply(case_tac "a")
   apply(rename_tac a w aa)(*strict*)
   defer
   apply(rename_tac a w b)(*strict*)
   apply(rule conjI)
    apply(rename_tac a w b)(*strict*)
    apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB1)
       apply(rename_tac a w b)(*strict*)
       apply(blast+)
   apply(rename_tac a w b)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB2)
      apply(rename_tac a w b)(*strict*)
      apply(blast+)
  apply(rename_tac a w aa)(*strict*)
  apply(clarify)
  apply(rename_tac A)
  apply(rename_tac a w A)(*strict*)
  apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_SOUND_EMPTY_step)
    apply(rename_tac a w A)(*strict*)
    apply(force)+
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_1a: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_03 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_03_def)
  apply(simp only: option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
  apply(case_tac "[] \<notin> F_CFG_FIRST__table_domain G")
   apply(clarsimp)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_1b: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_04 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_04_def)
  apply(simp only: option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
  apply(case_tac "[] \<notin> F_CFG_FIRST__table_domain G")
   apply(clarsimp)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_2a: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_05 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_05_def)
  apply(simp only: option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_2b: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_06 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_06_def)
  apply(simp only: option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_3: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_07 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_07_def)
  apply(auto)
  apply(rename_tac x A)(*strict*)
  apply(simp only: option_to_setMap_def F_CFG_FIRST__table__fp_one_def)
  apply(clarsimp)
  apply(case_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac x A)(*strict*)
   apply(auto)
    apply(rename_tac x A)(*strict*)
    apply(erule_tac
      x = "x"
      in allE)
    apply(erule_tac
      x = "A"
      in allE)
    apply(auto)
    apply(rename_tac x A v)(*strict*)
    apply(rule_tac
      x = "v"
      in exI)
    apply(auto)
    apply(rule table_domain__Cons_rhs)
    apply(blast)
   apply(rename_tac x A)(*strict*)
   apply(case_tac "None \<in> f [teA A]")
    apply(rename_tac x A)(*strict*)
    apply(auto)
   apply(rename_tac x A)(*strict*)
   apply(erule_tac
      x = "x"
      in allE)
   apply(erule_tac
      x = "A"
      in allE)
   apply(auto)
    apply(rename_tac x A)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_invariant_03_def F_CFG_FIRST__table__fp_invariant_04_def)
    apply(subgoal_tac "x = None")
     apply(rename_tac x A)(*strict*)
     apply(clarsimp)
    apply(rename_tac x A)(*strict*)
    apply(force)
   apply(rename_tac x A v)(*strict*)
   apply(rule_tac
      x = "v"
      in exI)
   apply(auto)
   apply(rule table_domain__Cons_rhs)
   apply(blast)
  apply(rename_tac x A xa)(*strict*)
  apply(rule_tac
      x = "xa"
      in exI)
  apply(auto)
  apply(rule table_domain__Cons_rhs)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_4: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_08 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_08_def)
  apply(auto)
  apply(rename_tac A v x)(*strict*)
  apply(subgoal_tac "v \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac A v x)(*strict*)
   apply(subgoal_tac "[] \<in> F_CFG_FIRST__table_domain G")
    apply(rename_tac A v x)(*strict*)
    apply(subgoal_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
     apply(rename_tac A v x)(*strict*)
     apply(simp add: F_CFG_FIRST__table__fp_one_def)
     apply(auto)
    apply(rename_tac A v x)(*strict*)
    apply(rule table_domain__Cons_lhs)
    apply(blast)
   apply(rename_tac A v x)(*strict*)
   apply(rule emptyIntable_domain)
   apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
  apply(rename_tac A v x)(*strict*)
  apply(rule table_domain__Cons_rhs)
  apply(blast)
  done

lemma table_domain__Cons_rhs2: "
  \<lparr>prod_lhs = y, prod_rhs = v @ w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> w \<in> F_CFG_FIRST__table_domain G"
  apply(simp add: F_CFG_FIRST__table_domain_def)
  apply(auto)
  apply(erule_tac
      x = "\<lparr>prod_lhs = y, prod_rhs = v @ w\<rparr>"
      in allE)
  apply(auto)
  apply(subgoal_tac "w \<in> suffixes (v @ w)")
   apply(blast)
  apply(rule suffixes_intro1)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_5: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_09 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_09_def)
  apply(auto)
  apply(rename_tac B u A w x)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(auto)
   apply(rename_tac B u A w x)(*strict*)
   apply(rule table_domain__Cons_rhs2)
   apply(blast)
  apply(rename_tac B u A x)(*strict*)
  apply(case_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac B u A x)(*strict*)
   apply(auto)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_6: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_10 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_10_def)
  apply(auto)
  apply(rename_tac B u A w)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(rule table_domain__Cons_rhs2)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_7: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_11 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_11_def)
  apply(auto)
  apply(rename_tac A x w)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_8: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_12 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp only: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_12_def)
  apply(auto)
  apply(rename_tac A x w)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(case_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac A x w)(*strict*)
   apply(auto)
  apply(rename_tac A x w)(*strict*)
  apply(case_tac "teA A # w \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac A x w)(*strict*)
   apply(auto)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_9: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_13 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp (no_asm) only: F_CFG_FIRST__table__fp_invariant_13_def)
  apply(rule allI)+
  apply(rename_tac w A x)(*strict*)
  apply(subgoal_tac "[teA A] \<in> F_CFG_FIRST__table_domain G \<longrightarrow> Some x \<notin> F_CFG_FIRST__table__fp_one G f w \<longrightarrow> Some x \<notin> F_CFG_FIRST__table__fp_one G f [teA A] \<longrightarrow> Some x \<notin> F_CFG_FIRST__table__fp_one G f (teA A # w)")
   apply(rename_tac w A x)(*strict*)
   apply(clarsimp)
  apply(rename_tac w A x)(*strict*)
  apply(rule impI)+
  apply(simp (no_asm) only: F_CFG_FIRST__table__fp_one_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac w A x)(*strict*)
   apply(rule impI)
   apply(case_tac w)
    apply(rename_tac w A x)(*strict*)
    apply(clarsimp)
    apply(rename_tac A x)(*strict*)
    apply(rule conjI)
     apply(rename_tac A x)(*strict*)
     apply(rule_tac
      B = "F_CFG_FIRST__table__fp_one G f [teA A]"
      in nset_mp)
      apply(rename_tac A x)(*strict*)
      apply(rule F_CFG_FIRST__table__fp_one_trans)
      apply(blast)
     apply(rename_tac A x)(*strict*)
     apply(clarsimp)
    apply(rename_tac A x)(*strict*)
    apply(rule conjI)
     apply(rename_tac A x)(*strict*)
     apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_03 G f")
      apply(rename_tac A x)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_invariant_03_def)
      apply(rule_tac
      B = "{None}"
      in nset_mp)
       apply(rename_tac A x)(*strict*)
       apply(clarsimp)
      apply(rename_tac A x)(*strict*)
      apply(clarsimp)
     apply(rename_tac A x)(*strict*)
     apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
    apply(rename_tac A x)(*strict*)
    apply(rule allI)
    apply(rename_tac A x xa)(*strict*)
    apply(rule impI)
    apply(case_tac "\<lparr>prod_lhs = A, prod_rhs = xa\<rparr> \<notin> cfg_productions G")
     apply(rename_tac A x xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac A x xa)(*strict*)
    apply(subgoal_tac "Some x \<in> F_CFG_FIRST__table__fp_one G f [teA A]")
     apply(rename_tac A x xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac A x xa)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_one_def)
   apply(rename_tac w A x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac A x a list)(*strict*)
   apply(rule conjI)
    apply(rename_tac A x a list)(*strict*)
    apply(case_tac "Some x \<notin> f (teA A # a # list)")
     apply(rename_tac A x a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac A x a list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_13 G f")
     apply(rename_tac A x a list)(*strict*)
     apply(simp only: F_CFG_FIRST__table__fp_invariant_13_def)
     apply(clarsimp)
     apply(erule_tac
      x = "a#list"
      in allE)
     apply(erule_tac
      x = "A"
      in allE)
     apply(clarsimp)
     apply(erule_tac
      x = "x"
      in allE)
     apply(clarsimp)
     apply(erule impE)
      apply(rename_tac A x a list)(*strict*)
      apply(rule_tac
      B = "F_CFG_FIRST__table__fp_one G f (a # list)"
      in nset_mp)
       apply(rename_tac A x a list)(*strict*)
       apply(rule F_CFG_FIRST__table__fp_one_trans)
       apply(rule table_domainDecomp)
       apply(blast)
      apply(rename_tac A x a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac A x a list)(*strict*)
     apply(subgoal_tac "Some x \<in> F_CFG_FIRST__table__fp_one G f [teA A]")
      apply(rename_tac A x a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac A x a list)(*strict*)
     apply(rule_tac
      A = "f [teA A]"
      in set_mp)
      apply(rename_tac A x a list)(*strict*)
      apply(rule F_CFG_FIRST__table__fp_one_trans)
      apply(clarsimp)
     apply(rename_tac A x a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac A x a list)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
   apply(rename_tac A x a list)(*strict*)
   apply(rule conjI)
    apply(rename_tac A x a list)(*strict*)
    apply(rule_tac
      B = "F_CFG_FIRST__table__fp_one G f [teA A]"
      in nset_mp)
     apply(rename_tac A x a list)(*strict*)
     apply(rule F_CFG_FIRST__table__fp_one_trans)
     apply(clarsimp)
    apply(rename_tac A x a list)(*strict*)
    apply(blast)
   apply(rename_tac A x a list)(*strict*)
   apply(rule conjI)
    apply(rename_tac A x a list)(*strict*)
    apply(rule_tac
      B = "F_CFG_FIRST__table__fp_one G f (a#list)"
      in nset_mp)
     apply(rename_tac A x a list)(*strict*)
     apply(rule F_CFG_FIRST__table__fp_one_trans)
     apply(rule table_domainDecomp)
     apply(blast)
    apply(rename_tac A x a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac A x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac A x a list xa)(*strict*)
   apply(subgoal_tac "Some x \<in> F_CFG_FIRST__table__fp_one G f [teA A]")
    apply(rename_tac A x a list xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac A x a list xa)(*strict*)
   apply(simp only: F_CFG_FIRST__table__fp_one_def)
   apply(clarsimp)
  apply(rename_tac w A x)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac w A x)(*strict*)
   defer
   apply(rename_tac w A x)(*strict*)
   apply(clarsimp)
   apply(rename_tac A x)(*strict*)
   apply(rule conjI)
    apply(rename_tac A x)(*strict*)
    apply(rule_tac
      B = "F_CFG_FIRST__table__fp_one G f [teA A]"
      in nset_mp)
     apply(rename_tac A x)(*strict*)
     apply(rule F_CFG_FIRST__table__fp_one_trans)
     apply(blast)
    apply(rename_tac A x)(*strict*)
    apply(blast)
   apply(rename_tac A x)(*strict*)
   apply(clarsimp)
   apply(rename_tac A x xa)(*strict*)
   apply(subgoal_tac "Some x \<in> F_CFG_FIRST__table__fp_one G f [teA A]")
    apply(rename_tac A x xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac A x xa)(*strict*)
   apply(simp (no_asm) add: F_CFG_FIRST__table__fp_one_def)
   apply(clarsimp)
  apply(rename_tac w A x)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac w A x)(*strict*)
   defer
   apply(rule conjI)
    apply(rename_tac w A x)(*strict*)
    apply(rule_tac
      B = "F_CFG_FIRST__table__fp_one G f [teA A]"
      in nset_mp)
     apply(rename_tac w A x)(*strict*)
     apply(rule F_CFG_FIRST__table__fp_one_trans)
     apply(blast)
    apply(rename_tac w A x)(*strict*)
    apply(blast)
   apply(rename_tac w A x)(*strict*)
   apply(clarsimp)
   apply(rename_tac w A x xa)(*strict*)
   apply(subgoal_tac "Some x \<in> F_CFG_FIRST__table__fp_one G f [teA A]")
    apply(rename_tac w A x xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac w A x xa)(*strict*)
   apply(simp (no_asm) add: F_CFG_FIRST__table__fp_one_def)
   apply(clarsimp)
  apply(rename_tac w A x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Some x \<in> F_CFG_FIRST__table__fp_one G f [teA A]")
   apply(rename_tac w A x)(*strict*)
   apply(blast)
  apply(rename_tac w A x)(*strict*)
  apply(thin_tac "Some x \<notin> F_CFG_FIRST__table__fp_one G f [teA A]")
  apply(simp (no_asm) only: F_CFG_FIRST__table__fp_one_def)
  apply(clarsimp)
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_12 G f")
   apply(rename_tac w A x)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariant_12_def)
   apply(erule_tac
      x = "A"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x = "x"
      in allE)
   apply(clarsimp)
  apply(rename_tac w A x)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_invariants_def)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_10: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_14 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp (no_asm) only: F_CFG_FIRST__table__fp_invariant_14_def)
  apply(auto)
  apply(rename_tac A)(*strict*)
  apply(subgoal_tac "[] \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac A)(*strict*)
   apply(subgoal_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
    apply(rename_tac A)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_one_def)
    apply(auto)
   apply(rename_tac A)(*strict*)
   apply(rule table_domain__Cons_lhs)
   apply(blast)
  apply(rename_tac A)(*strict*)
  apply(rule emptyIntable_domain)
  apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
  done

lemma insertFunfirst1ByEdge: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> None \<in> f w
  \<Longrightarrow> None \<in> F_CFG_FIRST__table__fp_one G f [teA A]"
  apply(subgoal_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
   apply(simp add: F_CFG_FIRST__table__fp_one_def)
   apply(auto)
  apply(rule table_domain__Cons_lhs)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_11: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_15 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp (no_asm) only: F_CFG_FIRST__table__fp_invariant_15_def)
  apply(auto)
  apply(rename_tac A w)(*strict*)
  apply(subgoal_tac "None \<in> F_CFG_FIRST__table__fp_one G f w")
   apply(rename_tac A w)(*strict*)
   apply(rule insertFunfirst1ByEdge)
     apply(rename_tac A w)(*strict*)
     apply(blast)+
  done

lemma F_CFG_FIRST__table_recursive_out: "
  F_CFG_FIRST__table_recursive n G (F_CFG_FIRST__table__fp_one G f) = F_CFG_FIRST__table_recursive (Suc n) G f"
  apply(induct_tac n)
   apply(auto)
  done

lemma F_CFG_FIRST__table_recursive_out2: "
  F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table_recursive n G f) = F_CFG_FIRST__table_recursive (Suc n) G f"
  apply(subgoal_tac "\<forall>f. F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table_recursive n G f) = F_CFG_FIRST__table_recursive (Suc n) G f")
   apply(blast)
  apply(induct_tac n)
   apply(auto)
  done

lemma F_CFG_FIRST__table_recursive_trans2: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> F_CFG_FIRST__table_recursive n G f w \<subseteq> F_CFG_FIRST__table_recursive (n + m) G f w"
  apply(induct_tac m)
   apply(simp)
  apply(rename_tac na)(*strict*)
  apply(rule_tac
      B = "F_CFG_FIRST__table_recursive (n+na) G f w"
      in subset_trans)
   apply(rename_tac na)(*strict*)
   apply(blast)
  apply(rename_tac na)(*strict*)
  apply(rule_tac
      s = "Suc (n+na)"
      and t = "n+Suc na"
      in ssubst)
   apply(rename_tac na)(*strict*)
   apply(arith)
  apply(rename_tac na)(*strict*)
  apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table_recursive (n+na) G f)"
      and t = "F_CFG_FIRST__table_recursive (Suc (n+na)) G f"
      in ssubst)
   apply(rename_tac na)(*strict*)
   apply(rule sym)
   apply(rule F_CFG_FIRST__table_recursive_out2)
  apply(rename_tac na)(*strict*)
  apply(rule F_CFG_FIRST__table__fp_one_trans)
  apply(auto)
  done

declare F_CFG_FIRST__table_recursive.simps [simp del]

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_12: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_16 G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp (no_asm) only: F_CFG_FIRST__table__fp_invariant_16_def)
  apply(auto)
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "\<forall>w. w \<in> F_CFG_FIRST__table_domain G \<and> w\<noteq>[] \<and> setB w = {} \<and> (\<forall>i<length w. None \<in> F_CFG_FIRST__table__fp_one G f [w ! i]) \<longrightarrow> None \<in> F_CFG_FIRST__table_recursive (length w) G (F_CFG_FIRST__table__fp_one G f) w")
   apply(rename_tac w)(*strict*)
   apply(blast)
  apply(rename_tac w)(*strict*)
  apply(thin_tac "w \<in> F_CFG_FIRST__table_domain G")
  apply(thin_tac "setB w = {}")
  apply(thin_tac "\<forall>i<length w. None \<in> F_CFG_FIRST__table__fp_one G f [w ! i]")
  apply(thin_tac "w\<noteq>[]")
  apply(rule allI)
  apply(rename_tac w wa)(*strict*)
  apply(rule_tac
      xs = "wa"
      in length_induct)
  apply(rename_tac w wa xs)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs)(*strict*)
  apply(case_tac xs)
   apply(rename_tac xs)(*strict*)
   apply(auto)
  apply(rename_tac a list)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac A w)(*strict*)
  apply(erule_tac
      x = "w"
      in allE)
  apply(auto)
    apply(rename_tac A w)(*strict*)
    apply(rule table_domainDecomp)
    apply(blast)
   apply(rename_tac A)(*strict*)
   apply(simp add: F_CFG_FIRST__table_recursive.simps)
   apply(subgoal_tac "None \<in> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table__fp_one G f) [A]")
    apply(rename_tac A)(*strict*)
    apply(blast)
   apply(rename_tac A)(*strict*)
   apply(rule_tac
      A = "F_CFG_FIRST__table__fp_one G f [A]"
      in set_mp)
    apply(rename_tac A)(*strict*)
    apply(rule F_CFG_FIRST__table__fp_one_trans)
    apply(blast)
   apply(rename_tac A)(*strict*)
   apply(blast)
  apply(rename_tac A w)(*strict*)
  apply(rule_tac
      s = "F_CFG_FIRST__table_recursive (Suc(Suc(length w))) G f"
      and t = "F_CFG_FIRST__table_recursive (Suc (length w)) G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac A w)(*strict*)
   apply(rule F_CFG_FIRST__table_recursive_out)
  apply(rename_tac A w)(*strict*)
  apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table_recursive (Suc(length w)) G f)"
      and t = "F_CFG_FIRST__table_recursive (Suc (Suc (length w))) G f"
      in ssubst)
   apply(rename_tac A w)(*strict*)
   apply(rule sym)
   apply(rule F_CFG_FIRST__table_recursive_out2)
  apply(rename_tac A w)(*strict*)
  apply(case_tac A)
   apply(rename_tac A w a)(*strict*)
   apply(auto)
  apply(rename_tac w a)(*strict*)
  apply(rename_tac A)
  apply(rename_tac w A)(*strict*)
  apply(simp (no_asm) only: F_CFG_FIRST__table__fp_one_def)
  apply(case_tac "teA A # w \<notin> F_CFG_FIRST__table_domain G")
   apply(rename_tac w A)(*strict*)
   apply(clarsimp)
  apply(rename_tac w A)(*strict*)
  apply(clarsimp)
  apply(auto)
    apply(rename_tac w A)(*strict*)
    apply(simp add: F_CFG_FIRST__table_recursive.simps)
   apply(rename_tac w A)(*strict*)
   apply(erule_tac
      x = "0"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "None \<in> F_CFG_FIRST__table_recursive (Suc (length w)) G f [teA A]")
    apply(rename_tac w A)(*strict*)
    apply(blast)
   apply(rename_tac w A)(*strict*)
   apply(rule_tac
      A = "F_CFG_FIRST__table__fp_one G f [teA A]"
      in set_mp)
    apply(rename_tac w A)(*strict*)
    defer
    apply(blast)
   apply(rename_tac A)(*strict*)
   apply(simp add: F_CFG_FIRST__table_recursive.simps)
  apply(rename_tac w A)(*strict*)
  apply(rule_tac
      s = "Suc 0+length w"
      and t = "Suc (length w)"
      in ssubst)
   apply(rename_tac w A)(*strict*)
   apply(arith)
  apply(rename_tac w A)(*strict*)
  apply(rule_tac
      s = "F_CFG_FIRST__table_recursive (Suc 0) G f"
      and t = "F_CFG_FIRST__table__fp_one G f"
      in ssubst)
   apply(rename_tac w A)(*strict*)
   apply(simp add: F_CFG_FIRST__table_recursive.simps)
  apply(rename_tac w A)(*strict*)
  apply(rule F_CFG_FIRST__table_recursive_trans2)
   apply(rename_tac w A)(*strict*)
   apply(blast)
  apply(rename_tac w A)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(case_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
   apply(rename_tac w A)(*strict*)
   apply(clarsimp)+
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_13: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_17 G (F_CFG_FIRST__table__fp_one G f)"
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_17 G f")
   prefer 2
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_17_def)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_17_def)
  apply(auto)
   apply(rename_tac w x)(*strict*)
   apply(erule_tac
      x="w"
      in ballE)
    apply(rename_tac w x)(*strict*)
    apply(case_tac "None \<in> f w")
     apply(rename_tac w x)(*strict*)
     apply(clarsimp)
    apply(rename_tac w x)(*strict*)
    apply(thin_tac "None \<in> f w \<longrightarrow> setB w = {} \<and> (\<forall>i<length w. None \<in> f [w ! i])")
    apply(simp add: F_CFG_FIRST__table__fp_one_def)
    apply(auto)
   apply(rename_tac w x)(*strict*)
   apply(case_tac w)
    apply(rename_tac w x)(*strict*)
    apply(auto)
    apply(rename_tac x a list)(*strict*)
    apply(case_tac a)
     apply(rename_tac x a list aa)(*strict*)
     apply(auto)
      apply(rename_tac x list aa)(*strict*)
      apply(case_tac list)
       apply(rename_tac x list aa)(*strict*)
       apply(auto)
     apply(rename_tac x list aa)(*strict*)
     apply(case_tac "None \<in> f [teA aa]")
      apply(rename_tac x list aa)(*strict*)
      apply(auto)
     apply(rename_tac x list aa)(*strict*)
     apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_17 G f")
      apply(rename_tac x list aa)(*strict*)
      prefer 2
      apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_17_def)
     apply(rename_tac x list aa)(*strict*)
     apply(simp add: F_CFG_FIRST__table__fp_invariant_17_def)
     apply(subgoal_tac "list \<in> F_CFG_FIRST__table_domain G")
      apply(rename_tac x list aa)(*strict*)
      apply(erule_tac
      x="list"
      in ballE)
       apply(rename_tac x list aa)(*strict*)
       apply(clarsimp)
      apply(rename_tac x list aa)(*strict*)
      apply(force)
     apply(rename_tac x list aa)(*strict*)
     apply(rule table_domainDecomp)
     apply(force)
    apply(rename_tac x list aa xa)(*strict*)
    apply(case_tac list)
     apply(rename_tac x list aa xa)(*strict*)
     apply(auto)
   apply(rename_tac x a list)(*strict*)
   apply(case_tac a)
    apply(rename_tac x a list aa)(*strict*)
    apply(auto)
  apply(rename_tac w i)(*strict*)
  apply(subgoal_tac "[w!i] \<in> F_CFG_FIRST__table_domain G \<or> setB w \<noteq> {}")
   apply(rename_tac w i)(*strict*)
   prefer 2
   apply(case_tac "setB w = {}")
    apply(rename_tac w i)(*strict*)
    apply(clarsimp)
    apply(case_tac "(w!i)")
     apply(rename_tac w i a)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      ?w1.0="take i w"
      and ?w2.0="drop (Suc i) w"
      in table_domainDecomp3)
       apply(rename_tac w i a)(*strict*)
       apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
      apply(rename_tac w i a)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
     apply(rename_tac w i a)(*strict*)
     apply(rule_tac
      t="(take i w) @ teA a # drop (Suc i) w"
      and s="w"
      in ssubst)
      apply(rename_tac w i a)(*strict*)
      apply(rule_tac
      t="teA a"
      and s="w!i"
      in ssubst)
       apply(rename_tac w i a)(*strict*)
       apply(force)
      apply(rename_tac w i a)(*strict*)
      apply(rule_tac
      t="take i w @ w ! i # drop (Suc i) w"
      and s="take i w @ [w ! i] @ drop (Suc i) w"
      in ssubst)
       apply(rename_tac w i a)(*strict*)
       apply(force)
      apply(rename_tac w i a)(*strict*)
      apply(rule nth_take_drop_split)
      apply(force)
     apply(rename_tac w i a)(*strict*)
     apply(force)
    apply(rename_tac w i b)(*strict*)
    apply(subgoal_tac "b \<in> setB w")
     apply(rename_tac w i b)(*strict*)
     apply(force)
    apply(rename_tac w i b)(*strict*)
    apply(rule_tac
      s="(take i w) @ [w!i] @ drop (Suc i) w"
      and t="w"
      in subst)
     apply(rename_tac w i b)(*strict*)
     apply(rule nth_take_drop_split)
     apply(force)
    apply(rename_tac w i b)(*strict*)
    apply(simp add: concat_asso setBConcat)
   apply(rename_tac w i)(*strict*)
   apply(force)
  apply(rename_tac w i)(*strict*)
  apply(erule_tac
      x="w"
      in ballE)
   apply(rename_tac w i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w i)(*strict*)
  apply(case_tac "None \<in> f w")
   apply(rename_tac w i)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      A="f [w ! i]"
      in set_mp)
    apply(rename_tac w i)(*strict*)
    apply(rule F_CFG_FIRST__table__fp_one_trans)
    apply(force)
   apply(rename_tac w i)(*strict*)
   apply(force)
  apply(rename_tac w i)(*strict*)
  apply(clarsimp)
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  apply(case_tac w)
   apply(rename_tac w i)(*strict*)
   apply(clarsimp)
  apply(rename_tac w i a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac i a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i list aa)(*strict*)
   apply(auto)
          apply(rename_tac i list aa x)(*strict*)
          apply(case_tac list)
           apply(rename_tac i list aa x)(*strict*)
           apply(clarsimp)
          apply(rename_tac i list aa x a lista)(*strict*)
          apply(clarsimp)
         apply(rename_tac i list aa x)(*strict*)
         apply(case_tac list)
          apply(rename_tac i list aa x)(*strict*)
          apply(clarsimp)
         apply(rename_tac i list aa x a lista)(*strict*)
         apply(clarsimp)
        apply(rename_tac i list aa)(*strict*)
        apply(case_tac list)
         apply(rename_tac i list aa)(*strict*)
         apply(clarsimp)
        apply(rename_tac i list aa a lista)(*strict*)
        apply(clarsimp)
       apply(rename_tac i list aa x)(*strict*)
       apply(case_tac "None \<in> f [teA aa]")
        apply(rename_tac i list aa x)(*strict*)
        apply(clarsimp)
        apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_17 G f")
         apply(rename_tac i list aa x)(*strict*)
         prefer 2
         apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_17_def)
        apply(rename_tac i list aa x)(*strict*)
        apply(simp add: F_CFG_FIRST__table__fp_invariant_17_def)
        apply(erule_tac
      x="list"
      in ballE)
         apply(rename_tac i list aa x)(*strict*)
         apply(clarsimp)
        apply(rename_tac i list aa x)(*strict*)
        apply(subgoal_tac "list\<in> F_CFG_FIRST__table_domain G")
         apply(rename_tac i list aa x)(*strict*)
         apply(force)
        apply(rename_tac i list aa x)(*strict*)
        apply(rule table_domainDecomp)
        apply(force)
       apply(rename_tac i list aa x)(*strict*)
       apply(clarsimp)
      apply(rename_tac i list aa x)(*strict*)
      apply(case_tac "None \<in> f [teA aa]")
       apply(rename_tac i list aa x)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_17 G f")
        apply(rename_tac i list aa x)(*strict*)
        prefer 2
        apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_17_def)
       apply(rename_tac i list aa x)(*strict*)
       apply(simp add: F_CFG_FIRST__table__fp_invariant_17_def)
       apply(erule_tac
      x="list"
      in ballE)
        apply(rename_tac i list aa x)(*strict*)
        apply(clarsimp)
       apply(rename_tac i list aa x)(*strict*)
       apply(subgoal_tac "list\<in> F_CFG_FIRST__table_domain G")
        apply(rename_tac i list aa x)(*strict*)
        apply(force)
       apply(rename_tac i list aa x)(*strict*)
       apply(rule table_domainDecomp)
       apply(force)
      apply(rename_tac i list aa x)(*strict*)
      apply(clarsimp)
     apply(rename_tac i list aa)(*strict*)
     apply(case_tac "None \<in> f [teA aa]")
      apply(rename_tac i list aa)(*strict*)
      apply(clarsimp)
      apply(case_tac i)
       apply(rename_tac i list aa)(*strict*)
       apply(clarsimp)
      apply(rename_tac i list aa nat)(*strict*)
      apply(clarsimp)
      apply(rename_tac list aa nat)(*strict*)
      apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_17 G f")
       apply(rename_tac list aa nat)(*strict*)
       prefer 2
       apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_17_def)
      apply(rename_tac list aa nat)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_invariant_17_def)
      apply(erule_tac
      x="list"
      in ballE)
       apply(rename_tac list aa nat)(*strict*)
       apply(clarsimp)
      apply(rename_tac list aa nat)(*strict*)
      apply(subgoal_tac "list\<in> F_CFG_FIRST__table_domain G")
       apply(rename_tac list aa nat)(*strict*)
       apply(force)
      apply(rename_tac list aa nat)(*strict*)
      apply(rule table_domainDecomp)
      apply(force)
     apply(rename_tac i list aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac i list aa x xa)(*strict*)
    apply(case_tac list)
     apply(rename_tac i list aa x xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac i list aa x xa a lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac i list aa x xa)(*strict*)
   apply(case_tac list)
    apply(rename_tac i list aa x xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac i list aa x xa a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac i list aa x)(*strict*)
  apply(case_tac list)
   apply(rename_tac i list aa x)(*strict*)
   apply(clarsimp)
  apply(rename_tac i list aa x a lista)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_ALL: "
  F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G (F_CFG_FIRST__table__fp_one G f)"
  apply(simp (no_asm) add: F_CFG_FIRST__table__fp_invariants_def)
  apply(rule conjI)
   apply(rule allI)
   apply(rename_tac w)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_SOUND_EMPTY)
     apply(rename_tac w)(*strict*)
     apply(blast)+
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_1a)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_1b)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_2a)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_2b)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_3)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_4)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_5)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_6)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_7)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_8)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_9)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_10)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_11)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_12)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_eB3_13)
     apply(blast+)
  done

lemma F_CFG_FIRST__fp_one_Meta_Lift: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> (\<And>G f. F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp_one G f) \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f \<Longrightarrow> P (F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)) G \<Longrightarrow> P (F_CFG_FIRST__table__fp G f) G)
  \<Longrightarrow> (\<And>G f. F_CFG_FIRST__table__fp_one G f = f \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G f \<Longrightarrow> F_CFG_FIRST__table__fp_invariants G f \<Longrightarrow> P (F_CFG_FIRST__table__fp G f) G )
  \<Longrightarrow> P (F_CFG_FIRST__fp_one G) G"
  apply(rule_tac
      t = "F_CFG_FIRST__fp_one G"
      and s = "F_CFG_FIRST__table__fp G (\<lambda>x. {})"
      in ssubst)
   apply(rule HOL.ext)
   apply(rename_tac x)(*strict*)
   apply(simp only: F_CFG_FIRST__fp_one_def)
  apply(subgoal_tac "(\<lambda>G f. F_CFG_FIRST__table__fp_invariants G f \<longrightarrow> (P (F_CFG_FIRST__table__fp G f) G)) G (\<lambda>x. {})")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_CFG_FIRST__TRANSFER_AT_kleene_starT)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G,f). F_CFG_FIRST__table__fp_invariants G f \<longrightarrow> (P (F_CFG_FIRST__table__fp G f) G)) (G,(\<lambda>x. {}))")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,f). F_CFG_FIRST__table__fp_valid_input G f"
      and RECURSIVE_COND = "\<lambda>(G,f). F_CFG_FIRST__table__fp_one G f\<noteq>f"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,f). (G,F_CFG_FIRST__table__fp_one G f)"
      and MEASURE = "\<lambda>(G,f). (sum (\<lambda>x. card((WrapInSome (cfg_events G))-(f x))) (F_CFG_FIRST__table_domain G))"
      and TERM_FUN = "(\<lambda>(G,f). F_CFG_FIRST__table__fp_invariants G f \<longrightarrow> (P (F_CFG_FIRST__table__fp G f) G))"
      and y = "(G,\<lambda>x. {})"
      in partial_termination_wf)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a b)(*strict*)
      apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
      apply(rename_tac G f)
      apply(rename_tac G f)(*strict*)
      apply(rule F_CFG_FIRST__table__fp_one_preserves_F_CFG_FIRST__table__fp_valid_input)
      apply(blast)
     apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
     apply(clarsimp)
     apply(rename_tac a b)(*strict*)
     apply(rename_tac G f)
     apply(rename_tac G f)(*strict*)
     apply(rule F_CFG_FIRST__sumSmaller)
        apply(rename_tac G f)(*strict*)
        apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
       apply(rename_tac G f)(*strict*)
       apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
      apply(rename_tac G f)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
     apply(rename_tac G f)(*strict*)
     apply(blast)
    prefer 3
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(erule impE)
   apply(rename_tac a b)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_one_TRANSFER_TRANSFERS_ALL)
     apply(rename_tac a b)(*strict*)
     apply(blast)+
  done

lemma F_CFG_FIRST__table__fp_termination: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_dom (G,f)"
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,f). F_CFG_FIRST__table__fp_valid_input G f"
      and RECURSIVE_COND = "\<lambda>(G,f). F_CFG_FIRST__table__fp_one G f\<noteq>f"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,f). (G,F_CFG_FIRST__table__fp_one G f)"
      and MEASURE = "\<lambda>(G,f). (sum (\<lambda>x. card(WrapInSome(cfg_events G)-(f x))) (F_CFG_FIRST__table_domain G))"
      in partial_termination_wf)
      apply(auto)
     apply(rename_tac a b)(*strict*)
     apply(rule F_CFG_FIRST__termLem1)
      apply(rename_tac a b)(*strict*)
      apply(blast,blast)
    apply(rename_tac a b)(*strict*)
    apply(rule F_CFG_FIRST__sumSmaller)
       apply(rename_tac a b)(*strict*)
       apply(simp only: F_CFG_FIRST__table__fp_valid_input_def)
      apply(rename_tac a b)(*strict*)
      apply(simp only: F_CFG_FIRST__table__fp_valid_input_def)
     apply(rename_tac a b)(*strict*)
     apply(simp only: F_CFG_FIRST__table__fp_valid_input_def)
    apply(rename_tac a b)(*strict*)
    apply(blast)
   apply(rename_tac a b)(*strict*)
   apply(rule F_CFG_FIRST__table__fp.domintros,blast)
  apply(rename_tac a b)(*strict*)
  apply(rule F_CFG_FIRST__table__fp.domintros,blast)
  done

lemma F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp G f = F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
  apply(rule_tac
      s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
   apply(rule F_CFG_FIRST__table__fp.psimps)
   apply(rule F_CFG_FIRST__table__fp_termination)
   apply(blast)
  apply(clarsimp)
  apply(rule_tac
      s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
   apply(rule F_CFG_FIRST__table__fp.psimps)
   apply(rule F_CFG_FIRST__table__fp_termination)
   apply(blast)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G) = F_CFG_FIRST__fp_one G"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplication1: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> P f
  \<Longrightarrow> F_CFG_FIRST__table__fp_one G f = f
  \<Longrightarrow> P (F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table__fp G f))"
  apply(rule_tac
      s = "f"
      and t = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table__fp G f)"
      in ssubst)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(clarsimp)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_04_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G) [] = {None}"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_04_def)
   apply(clarsimp)
   apply(rule_tac
      P="\<lambda>f. f [] = {None}"
      in F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplication1)
     apply(rename_tac G f)(*strict*)
     apply(simp)+
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      and t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_04: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_04 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_04_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_04_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_preserves_termination: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp G f)"
  apply(subgoal_tac "(\<lambda>(G,f). F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp G f))(G,f)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,f). F_CFG_FIRST__table__fp_valid_input G f"
      and RECURSIVE_COND = "\<lambda>(G,f). F_CFG_FIRST__table__fp_one G f\<noteq>f"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,f). (G,F_CFG_FIRST__table__fp_one G f)"
      and MEASURE = "\<lambda>(G,f). (sum (\<lambda>x. card(WrapInSome(cfg_events G)-(f x))) (F_CFG_FIRST__table_domain G))"
      and y = "(G,f)"
      in partial_termination_wf)
      apply(auto)
     apply(rename_tac a b)(*strict*)
     apply(rule F_CFG_FIRST__termLem1)
      apply(rename_tac a b)(*strict*)
      apply(blast,blast)
    apply(rename_tac a b)(*strict*)
    apply(rule F_CFG_FIRST__sumSmaller)
       apply(rename_tac a b)(*strict*)
       apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
      apply(rename_tac a b)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
     apply(rename_tac a b)(*strict*)
     apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
    apply(rename_tac a b)(*strict*)
    apply(blast)
   apply(rename_tac a b)(*strict*)
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G f")
   apply(rename_tac G f)
   apply(rename_tac G f)(*strict*)
   apply(rule_tac
      s = "f"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
    apply(rename_tac G f)(*strict*)
    apply(rule_tac
      s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
     apply(rename_tac G f)(*strict*)
     apply(rule F_CFG_FIRST__table__fp.psimps)
     apply(rule F_CFG_FIRST__table__fp_termination)
     apply(blast)
    apply(rename_tac G f)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G f")
  apply(rename_tac G f)
  apply(rename_tac G f)(*strict*)
  apply(case_tac "F_CFG_FIRST__table__fp_one G f = f")
   apply(rename_tac G f)(*strict*)
   apply(rule_tac
      s = "f"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
    apply(rename_tac G f)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
     apply(rename_tac G f)(*strict*)
     apply(rule F_CFG_FIRST__table__fp.psimps)
     apply(rule F_CFG_FIRST__table__fp_termination)
     apply(blast)
    apply(rename_tac G f)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f)(*strict*)
  apply(rule_tac
      s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
   apply(rename_tac G f)(*strict*)
   apply(rule F_CFG_FIRST__table__fp.psimps)
   apply(rule F_CFG_FIRST__table__fp_termination)
   apply(blast)
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_06_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>x l. F_CFG_FIRST__fp_one G (teB x # l) \<subseteq> {Some x}"
  apply(rule allI)+
  apply(rename_tac x l)(*strict*)
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(rename_tac x l)(*strict*)
    apply(blast)
   apply(rename_tac x l Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac x l G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac x l G f xa)(*strict*)
   apply(rename_tac G f w)
   apply(rename_tac x l G f w)(*strict*)
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f (teB x # l) = {Some x}")
    apply(rename_tac x l G f w)(*strict*)
    apply(clarsimp)
   apply(rename_tac x l G f w)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac x l G f w)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(rename_tac x l G f w)(*strict*)
   apply(clarsimp)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_05_def F_CFG_FIRST__table__fp_invariant_06_def)
   apply(clarsimp)
   apply(erule_tac
      x = "x"
      and P="\<lambda>x. \<forall>l. teB x # l \<in> F_CFG_FIRST__table_domain G \<longrightarrow> f (teB x # l) = {Some x}"
      in allE)
   apply(erule_tac
      x = "l"
      and P="\<lambda>l. teB x # l \<in> F_CFG_FIRST__table_domain G \<longrightarrow> f (teB x # l) = {Some x}"
      in allE)
   apply(erule impE)
    apply(rename_tac x l G f w)(*strict*)
    apply(auto)
   apply(rename_tac x l G f w)(*strict*)
   apply(subgoal_tac "F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__table__fp G f)")
    apply(rename_tac x l G f w)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
    apply(auto)
    apply(simp add: maps_only_from_table_domain_def)
    apply(auto)
   apply(rename_tac x l G f w)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_preserves_termination)
   apply(blast)
  apply(rename_tac x l Ga f xa)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac x l G f xa)(*strict*)
  apply(rename_tac G f w)
  apply(rename_tac x l G f w)(*strict*)
  apply(case_tac w)
   apply(rename_tac x l G f w)(*strict*)
   apply(auto)
   apply(rename_tac x l G f)(*strict*)
   apply(subgoal_tac "None \<notin> F_CFG_FIRST__table__fp G f (teB x#l)")
    apply(rename_tac x l G f)(*strict*)
    apply(blast)
   apply(rename_tac x l G f)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac x l G f)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(rename_tac x l G f)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac x l G f a)(*strict*)
  apply(case_tac "a = x")
   apply(rename_tac x l G f a)(*strict*)
   apply(auto)
  apply(rename_tac x l G f a)(*strict*)
  apply(subgoal_tac "Some a \<notin> F_CFG_FIRST__table__fp G f (teB x # l)")
   apply(rename_tac x l G f a)(*strict*)
   apply(blast)
  apply(rename_tac x l G f a)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
   apply(rename_tac x l G f a)(*strict*)
   apply(rule F_CFG_FIRST__table__fp.psimps)
   apply(rule F_CFG_FIRST__table__fp_termination)
   apply(blast)+
  apply(rename_tac x l G f a)(*strict*)
  apply(clarsimp)
  apply(force)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_05_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>x l. teB x # l \<in> F_CFG_FIRST__table_domain G \<longrightarrow> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G) (teB x # l) = {Some x}"
  apply(subgoal_tac "(\<forall>x l. F_CFG_FIRST__fp_one G (teB x # l) \<subseteq> {Some x})")
   prefer 2
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_06_unfold)
   apply(auto)
   apply(rename_tac x l xa)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_one_def)
   apply(auto)
  apply(rename_tac x l)(*strict*)
  apply(simp add: F_CFG_FIRST__table__fp_one_def)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_05: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_05 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_05_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_05_unfold)
  apply(blast)
  done

lemma hasEdge1: "
  teA A # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> \<exists>u B. \<lparr>prod_lhs = B, prod_rhs = u @ teA A # w\<rparr> \<in> cfg_productions G"
  apply(simp add: F_CFG_FIRST__table_domain_def)
  apply(auto)
  apply(rename_tac e)(*strict*)
  apply(case_tac e)
  apply(rename_tac e prod_lhs prod_rhsa)(*strict*)
  apply(auto)
  apply(rename_tac prod_lhs prod_rhs)(*strict*)
  apply(rename_tac B r)
  apply(rename_tac B r)(*strict*)
  apply(subgoal_tac "\<exists>x. x @ (teA A # w) = r")
   apply(rename_tac B r)(*strict*)
   apply(clarsimp)
   apply(rename_tac B x)(*strict*)
   apply(rule_tac
      x = "x"
      in exI)
   apply(rule_tac
      x = "B"
      in exI)
   apply(clarsimp)
  apply(rename_tac B r)(*strict*)
  apply(rule suffixes_intro2_rev)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplication0: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> P f
  \<Longrightarrow> F_CFG_FIRST__table__fp_one G f = f
  \<Longrightarrow> P (F_CFG_FIRST__table__fp G f)"
  apply(rule_tac
      s = "f"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(clarsimp)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_09_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>B u A w x. \<lparr>prod_lhs = B, prod_rhs = u @ teA A # w\<rparr> \<in> cfg_productions G \<and> Some x \<in> (F_CFG_FIRST__fp_one G) [teA A] \<longrightarrow> Some x \<in> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G) (teA A # w)"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f B u A w x)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_09_def)
   apply(erule conjE)+
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f B u A w x)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(rename_tac G f B u A w x)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x = "B"
      in allE)
   apply(erule_tac
      x = "u"
      and P="\<lambda>u. \<forall>A w x. \<lparr>prod_lhs = B, prod_rhs = u @ teA A # w\<rparr> \<in> cfg_productions G \<and> Some x \<in> f [teA A] \<longrightarrow> Some x \<in> f (teA A # w)"
      in allE)
   apply(rename_tac G f B u A w x)(*strict*)
   apply(erule_tac
      x = "A"
      in allE)
   apply(erule_tac
      x = "w"
      and P="\<lambda>w. \<forall>x. \<lparr>prod_lhs = B, prod_rhs = u @ teA A # w\<rparr> \<in> cfg_productions G \<and> Some x \<in> f [teA A] \<longrightarrow> Some x \<in> f (teA A # w)"
      in allE)
   apply(rename_tac G f B u A w x)(*strict*)
   apply(erule_tac
      x = "x"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "Some x \<notin> (F_CFG_FIRST__table__fp G f) [teA A]")
    apply(rename_tac G f B u A w x)(*strict*)
    apply(blast)
   apply(rename_tac G f B u A w x)(*strict*)
   apply(rule_tac
      P="\<lambda>f. Some x \<notin> f [teA A]"
      in F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplication0)
     apply(rename_tac G f B u A w x)(*strict*)
     apply(blast)+
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(auto)
  apply(rename_tac G f B u A w x)(*strict*)
  apply(erule_tac
      x = "B"
      in allE)
  apply(erule_tac
      x = "u"
      in allE)
  apply(erule_tac
      x = "A"
      in allE)
  apply(erule_tac
      x = "w"
      in allE)
  apply(erule_tac
      x = "x"
      in allE)
  apply(auto)
   apply(rename_tac G f B u A w x)(*strict*)
   apply(subgoal_tac "Some x \<in> F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f) [teA A]")
    apply(rename_tac G f B u A w x)(*strict*)
    apply(blast)
   apply(rename_tac G f B u A w x)(*strict*)
   apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f B u A w x)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f B u A w x)(*strict*)
   apply(blast)
  apply(rename_tac G f B u A w x)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f B u A w x)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f B u A w x)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_09: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_09 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_09_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_09_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_elem_PostExtend1: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> (teA A)#w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> Some x \<in> F_CFG_FIRST__fp_one G [teA A]
  \<Longrightarrow> Some x \<in> F_CFG_FIRST__fp_one G ((teA A)#w)"
  apply(case_tac "w = []")
   apply(clarsimp)
  apply(subgoal_tac "\<exists>u B. \<lparr>prod_lhs = B,prod_rhs = u @ (teA A)#w\<rparr> \<in> cfg_productions G")
   apply(clarsimp)
   apply(rename_tac u B)(*strict*)
   defer
   apply(rule hasEdge1)
    apply(blast)+
  apply(rename_tac u B)(*strict*)
  apply(subgoal_tac "Some x \<in> F_CFG_FIRST__fp_one G [teA A]")
   apply(rename_tac u B)(*strict*)
   apply(clarsimp)
   apply(auto)
  apply(rename_tac u B)(*strict*)
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_09 G (F_CFG_FIRST__fp_one G)")
   apply(rename_tac u B)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariant_09_def)
   apply(erule_tac
      x = "B"
      in allE)
   apply(erule_tac
      x = "u"
      in allE)
   apply(erule_tac
      x = "A"
      in allE)
   apply(erule_tac
      x = "w"
      in allE)
   apply(erule_tac
      x = "x"
      in allE)
   apply(erule_tac impE)
    apply(rename_tac u B)(*strict*)
    prefer 2
    apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
     apply(rename_tac u B)(*strict*)
     apply(rule sym)
     apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
     apply(blast)+
  apply(rename_tac u B)(*strict*)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_09)
  apply(blast)
  done

lemma F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplicationRev0: "
  F_CFG_FIRST__table__fp_valid_input G f
  \<Longrightarrow> P (F_CFG_FIRST__table__fp G f)
  \<Longrightarrow> F_CFG_FIRST__table__fp_one G f = f
  \<Longrightarrow> P f"
  apply(rule_tac
      t = "f"
      and s = "F_CFG_FIRST__table__fp G f"
      in ssubst)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(clarsimp)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_11_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>A x w. None \<in> (F_CFG_FIRST__fp_one G) [teA A] \<and> x \<in> (F_CFG_FIRST__fp_one G) w \<and> teA A # w \<in> F_CFG_FIRST__table_domain G \<longrightarrow> x \<in> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G) (teA A # w)"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f A x w)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_11_def)
   apply(erule conjE)+
   apply(auto)
   apply(erule_tac
      x = "A"
      in allE)
   apply(erule_tac
      x = "x"
      in allE)
   apply(erule_tac
      x = "w"
      and P="\<lambda>w. None \<in> f [teA A] \<and> x \<in> f w \<and> teA A # w \<in> F_CFG_FIRST__table_domain G \<longrightarrow> x \<in> f (teA A # w)"
      in allE)
   apply(rule F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplication1)
     apply(rename_tac G f A x w)(*strict*)
     apply(blast)
    apply(rename_tac G f A x w)(*strict*)
    apply(erule impE)
     apply(rename_tac G f A x w)(*strict*)
     apply(auto)
    apply(rename_tac G f A x w)(*strict*)
    apply(rule_tac
      P = "\<lambda>f. None \<in> f [teA A]"
      in F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplicationRev0)
      apply(rename_tac G f A x w)(*strict*)
      apply(blast)
     apply(rename_tac G f A x w)(*strict*)
     apply(blast)+
   apply(rename_tac G f A x w)(*strict*)
   apply(rule_tac
      P = "\<lambda>f. x \<in> f w"
      in F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplicationRev0)
     apply(rename_tac G f A x w)(*strict*)
     apply(blast)
    apply(rename_tac G f A x w)(*strict*)
    apply(blast)+
  apply(rename_tac Ga f A x w)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f A x w)(*strict*)
  apply(erule_tac
      x = "A"
      in allE)
  apply(erule_tac
      x = "x"
      in allE)
  apply(erule_tac
      x = "w"
      in allE)
  apply(erule_tac impE)
   apply(rename_tac G f A x w)(*strict*)
   apply(auto)
    apply(rename_tac G f A x w)(*strict*)
    apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
     apply(rename_tac G f A x w)(*strict*)
     apply(rule sym)
     apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
     apply(blast)
    apply(rename_tac G f A x w)(*strict*)
    apply(blast)
   apply(rename_tac G f A x w)(*strict*)
   apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f A x w)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f A x w)(*strict*)
   apply(blast)
  apply(rename_tac G f A x w)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f A x w)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f A x w)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_11: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_11 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_11_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_11_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_elem_PostExtend3: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> teA A # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> None \<in> F_CFG_FIRST__fp_one G [teA A]
  \<Longrightarrow> Some x \<in> F_CFG_FIRST__fp_one G w
  \<Longrightarrow> Some x \<in> F_CFG_FIRST__fp_one G (teA A # w)"
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_11 G (F_CFG_FIRST__fp_one G)")
   prefer 2
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_11)
   apply(blast)
  apply(simp add: F_CFG_FIRST__table__fp_invariant_11_def)
  apply(erule_tac
      x = "A"
      in allE)
  apply(erule_tac
      x = "Some x"
      in allE)
  apply(erule_tac
      x = "w"
      in allE)
  apply(auto)
  apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
   apply(rule sym)
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
   apply(blast)+
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_13_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>w A x. [teA A] \<in> F_CFG_FIRST__table_domain G \<longrightarrow> Some x \<in> (F_CFG_FIRST__fp_one G) (teA A # w) \<longrightarrow> Some x \<notin> (F_CFG_FIRST__fp_one G) w \<longrightarrow> Some x \<in> (F_CFG_FIRST__fp_one G) [teA A]"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f w A x)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_13_def)
   apply(erule conjE)+
   apply(erule_tac
      x = "w"
      and P="\<lambda>w. \<forall>A. [teA A] \<in> F_CFG_FIRST__table_domain G \<longrightarrow> (\<forall>x. Some x \<in> f (teA A # w) \<longrightarrow> Some x \<notin> f w \<longrightarrow> Some x \<in> f [teA A])"
      in allE)
   apply(rename_tac G f w A x)(*strict*)
   apply(erule_tac
      x = "A"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x = "x"
      in allE)
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f w A x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f w A x)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f w A x)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(rename_tac G f w A x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f w A x)(*strict*)
  apply(erule_tac
      x = "w"
      in allE)
  apply(erule_tac
      x = "A"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x = "x"
      in allE)
  apply(erule impE)
   apply(rename_tac G f w A x)(*strict*)
   apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f w A x)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f w A x)(*strict*)
   apply(blast)
  apply(rename_tac G f w A x)(*strict*)
  apply(erule impE)
   apply(rename_tac G f w A x)(*strict*)
   apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f w A x)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f w A x)(*strict*)
   apply(blast)
  apply(rename_tac G f w A x)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f w A x)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f w A x)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_13: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_13 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_13_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_13_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_elem_PostExtend4: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> [teA A] \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> None \<in> F_CFG_FIRST__fp_one G [teA A]
  \<Longrightarrow> Some x \<in> F_CFG_FIRST__fp_one G (teA A # w)
  \<Longrightarrow> Some x \<notin> F_CFG_FIRST__fp_one G w
  \<Longrightarrow> Some x \<in> F_CFG_FIRST__fp_one G [teA A]"
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_13 G (F_CFG_FIRST__fp_one G)")
   apply(simp add: F_CFG_FIRST__table__fp_invariant_13_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_13)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_17_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>w \<in> F_CFG_FIRST__table_domain G. None \<in> (F_CFG_FIRST__fp_one G) w \<longrightarrow> setB w = {} \<and> (\<forall>i<length w. None \<in> (F_CFG_FIRST__fp_one G) [w ! i])"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f w)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_17_def)
   apply(erule conjE)+
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f w)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f w)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f w)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)
   apply(rename_tac G f w)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f w)(*strict*)
  apply(erule_tac
      x = "w"
      in ballE)
   apply(rename_tac G f w)(*strict*)
   apply(erule impE)
    apply(rename_tac G f w)(*strict*)
    apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in subst)
     apply(rename_tac G f w)(*strict*)
     apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
     apply(blast)
    apply(rename_tac G f w)(*strict*)
    apply(force)
   apply(rename_tac G f w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f w i)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f w i)(*strict*)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f w i)(*strict*)
   apply(force)
  apply(rename_tac G f w)(*strict*)
  apply(force)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_16_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>w \<in> F_CFG_FIRST__table_domain G. setB w = {} \<and> w\<noteq>[] \<and> (\<forall>i<length w. None \<in> (F_CFG_FIRST__fp_one G) [w ! i]) \<longrightarrow> None \<in> F_CFG_FIRST__table_recursive (length w) G (F_CFG_FIRST__fp_one G) w"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f w)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_16_def)
   apply(erule conjE)+
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f w)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f w)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f w)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)
   apply(rename_tac G f w)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f w)(*strict*)
  apply(erule_tac
      x = "w"
      in ballE)
   apply(rename_tac G f w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f w)(*strict*)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f w)(*strict*)
   apply(erule impE)
    apply(rename_tac G f w)(*strict*)
    apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
     apply(rename_tac G f w)(*strict*)
     apply(rule sym)
     apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
     apply(blast)
    apply(rename_tac G f w)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f w)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table_recursive_idemp: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__fp_one G = F_CFG_FIRST__table_recursive n G (F_CFG_FIRST__fp_one G)"
  apply(induct_tac n)
   apply(simp add: F_CFG_FIRST__table_recursive.simps)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table_recursive n G (F_CFG_FIRST__fp_one G))"
      and t = "F_CFG_FIRST__table_recursive (Suc n) G (F_CFG_FIRST__fp_one G)"
      in ssubst)
   apply(rename_tac n)(*strict*)
   apply(rule sym)
   apply(rule F_CFG_FIRST__table_recursive_out2)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
  apply(auto)
  done

lemma F_CFG_FIRST__fp_one_elem_teANoneEq: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> teA A # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> [teA A] \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> None \<in> F_CFG_FIRST__fp_one G [teA A]
  \<Longrightarrow> (F_CFG_FIRST__fp_one G [teA A]) \<union> (F_CFG_FIRST__fp_one G w) - {x. x=None \<and> None \<notin> F_CFG_FIRST__fp_one G w} = (F_CFG_FIRST__fp_one G (teA A # w))"
  apply(rule order_antisym)
   apply(auto)
       apply(rename_tac x)(*strict*)
       apply(case_tac x)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(rename_tac x a)(*strict*)
       apply(subgoal_tac "x \<in> F_CFG_FIRST__fp_one G (teA A # w)")
        apply(rename_tac x a)(*strict*)
        apply(force)
       apply(rename_tac x a)(*strict*)
       apply(rule_tac
      t="x"
      and s="Some a"
      in ssubst)
        apply(rename_tac x a)(*strict*)
        apply(clarsimp)
       apply(rename_tac x a)(*strict*)
       apply(rule F_CFG_FIRST__fp_one_elem_PostExtend1)
         apply(rename_tac x a)(*strict*)
         apply(blast)+
      apply(rename_tac x)(*strict*)
      apply(subgoal_tac "x \<in> F_CFG_FIRST__fp_one G (teA A # w)")
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(thin_tac "x \<notin> F_CFG_FIRST__fp_one G (teA A # w)")
      apply(rule_tac
      t="F_CFG_FIRST__fp_one G (teA A#w)"
      and s="F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table__fp G (\<lambda>x. {})) (teA A #w)"
      in ssubst)
       apply(rename_tac x)(*strict*)
       prefer 2
       apply(subgoal_tac "F_CFG_FIRST__fp_one G = F_CFG_FIRST__table__fp G (\<lambda>x. {})")
        apply(rename_tac x)(*strict*)
        apply(simp add: F_CFG_FIRST__table__fp_one_def)
       apply(rename_tac x)(*strict*)
       apply(rule ext)
       apply(rename_tac x xa)(*strict*)
       apply(simp add: F_CFG_FIRST__fp_one_def)
      apply(rename_tac x)(*strict*)
      apply(rule_tac
      s="F_CFG_FIRST__fp_one G"
      and t="F_CFG_FIRST__table__fp G (\<lambda>x. {})"
      in subst)
       apply(rename_tac x)(*strict*)
       apply(rule ext)
       apply(rename_tac x xa)(*strict*)
       apply(simp add: F_CFG_FIRST__fp_one_def)
      apply(rename_tac x)(*strict*)
      apply(rule_tac
      t="F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and s="F_CFG_FIRST__fp_one G"
      and P="\<lambda>f. F_CFG_FIRST__fp_one G (teA A # w)= f (teA A # w)"
      in ssubst)
       apply(rename_tac x)(*strict*)
       apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(case_tac x)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x a)(*strict*)
     apply(subgoal_tac "x \<in> F_CFG_FIRST__fp_one G (teA A # w)")
      apply(rename_tac x a)(*strict*)
      apply(force)
     apply(rename_tac x a)(*strict*)
     apply(rule_tac
      t="x"
      and s="Some a"
      in ssubst)
      apply(rename_tac x a)(*strict*)
      apply(clarsimp)
     apply(rename_tac x a)(*strict*)
     apply(thin_tac "x \<notin> F_CFG_FIRST__fp_one G (teA A # w)")
     apply(clarsimp)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      t="F_CFG_FIRST__fp_one G (teA A#w)"
      and s="F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table__fp G (\<lambda>x. {})) (teA A #w)"
      in ssubst)
      apply(rename_tac a)(*strict*)
      prefer 2
      apply(subgoal_tac "F_CFG_FIRST__fp_one G = F_CFG_FIRST__table__fp G (\<lambda>x. {})")
       apply(rename_tac a)(*strict*)
       apply(simp add: F_CFG_FIRST__table__fp_one_def)
      apply(rename_tac a)(*strict*)
      apply(rule ext)
      apply(rename_tac a x)(*strict*)
      apply(simp add: F_CFG_FIRST__fp_one_def)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      s="F_CFG_FIRST__fp_one G"
      and t="F_CFG_FIRST__table__fp G (\<lambda>x. {})"
      in subst)
      apply(rename_tac a)(*strict*)
      apply(rule ext)
      apply(rename_tac a x)(*strict*)
      apply(simp add: F_CFG_FIRST__fp_one_def)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      t="F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and s="F_CFG_FIRST__fp_one G"
      and P="\<lambda>f. F_CFG_FIRST__fp_one G (teA A # w)= f (teA A # w)"
      in ssubst)
      apply(rename_tac a)(*strict*)
      apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "x \<in> F_CFG_FIRST__fp_one G (teA A # w)")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(thin_tac "x \<notin> F_CFG_FIRST__fp_one G (teA A # w)")
    apply(rule_tac
      t="F_CFG_FIRST__fp_one G (teA A#w)"
      and s="F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table__fp G (\<lambda>x. {})) (teA A #w)"
      in ssubst)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(subgoal_tac "F_CFG_FIRST__fp_one G = F_CFG_FIRST__table__fp G (\<lambda>x. {})")
      apply(rename_tac x)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_one_def)
     apply(rename_tac x)(*strict*)
     apply(rule ext)
     apply(rename_tac x xa)(*strict*)
     apply(simp add: F_CFG_FIRST__fp_one_def)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      s="F_CFG_FIRST__fp_one G"
      and t="F_CFG_FIRST__table__fp G (\<lambda>x. {})"
      in subst)
     apply(rename_tac x)(*strict*)
     apply(rule ext)
     apply(rename_tac x xa)(*strict*)
     apply(simp add: F_CFG_FIRST__fp_one_def)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      t="F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and s="F_CFG_FIRST__fp_one G"
      and P="\<lambda>f. F_CFG_FIRST__fp_one G (teA A # w)= f (teA A # w)"
      in ssubst)
     apply(rename_tac x)(*strict*)
     apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(rule F_CFG_FIRST__fp_one_elem_PostExtend4)
       apply(rename_tac a)(*strict*)
       apply(blast)+
  apply(subgoal_tac "w\<in> F_CFG_FIRST__table_domain G")
   prefer 2
   apply(rule table_domainDecomp)
   apply(force)
  apply(case_tac w)
   apply(clarsimp)
   apply(subgoal_tac "F_CFG_FIRST__fp_one G [] = {None}")
    apply(force)
   apply(rule_tac
      t="F_CFG_FIRST__fp_one G"
      and s="F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      in subst)
    apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
    apply(force)
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_04_unfold)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "w\<noteq>[]")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "w=a#list")
  apply(subgoal_tac "None \<in> F_CFG_FIRST__fp_one G w")
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "None \<notin> F_CFG_FIRST__fp_one G w")
  apply(subgoal_tac "\<forall>w\<in> F_CFG_FIRST__table_domain G. setB w = {} \<and> w \<noteq> [] \<and> (\<forall>i<length w. None \<in> F_CFG_FIRST__fp_one G [w ! i]) \<longrightarrow> None \<in> F_CFG_FIRST__table_recursive (length w) G (F_CFG_FIRST__fp_one G) w")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_16_unfold)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(erule_tac
      x="w"
      in ballE)
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(erule impE)
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(subgoal_tac "F_CFG_FIRST__fp_one G = F_CFG_FIRST__table_recursive (length w) G (F_CFG_FIRST__fp_one G)")
    apply(rename_tac a list)(*strict*)
    prefer 2
    apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table_recursive_idemp)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<forall>w\<in> F_CFG_FIRST__table_domain G. None \<in> F_CFG_FIRST__fp_one G w \<longrightarrow> setB w = {} \<and> (\<forall>i<length w. None \<in> F_CFG_FIRST__fp_one G [w ! i])")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_17_unfold)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(erule_tac
      x="(teA A)#w"
      in ballE)
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(erule impE)
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(erule_tac
      x="Suc i"
      in allE)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(force)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_TERM: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__fp_one G)"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_Elem_table_domain: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> x \<in> F_CFG_FIRST__fp_one G w
  \<Longrightarrow> w \<in> F_CFG_FIRST__table_domain G"
  apply(subgoal_tac "F_CFG_FIRST__table__fp_valid_input G (F_CFG_FIRST__fp_one G)")
   apply(simp add: F_CFG_FIRST__table__fp_valid_input_def maps_only_from_table_domain_def)
   apply(auto)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_TERM)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_12_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>A x w. [teA A] \<in> F_CFG_FIRST__table_domain G \<longrightarrow> None \<notin> (F_CFG_FIRST__fp_one G) [teA A] \<longrightarrow> Some x \<in> (F_CFG_FIRST__fp_one G) (teA A # w) \<longrightarrow> Some x \<in> (F_CFG_FIRST__fp_one G) [teA A]"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f A x w)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_12_def)
   apply(erule conjE)+
   apply(erule_tac
      x = "A"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f A x w)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x = "x"
      in allE)
    apply(clarsimp)
   apply(rename_tac G f A x w)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f A x w)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(rename_tac G f A x w)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f A x w)(*strict*)
  apply(erule_tac
      x = "A"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac G f A x w)(*strict*)
   apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f A x w)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f A x w)(*strict*)
   apply(blast)
  apply(rename_tac G f A x w)(*strict*)
  apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f A x w)(*strict*)
   apply(rule sym)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f A x w)(*strict*)
  apply(erule_tac
      x = "x"
      in allE)
  apply(erule impE)
   apply(rename_tac G f A x w)(*strict*)
   apply(rule_tac
      x = "w"
      in exI)
   apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f A x w)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f A x w)(*strict*)
   apply(blast)
  apply(rename_tac G f A x w)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f A x w)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f A x w)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_12: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_12 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_12_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_12_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_elem_PostExtend5: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> [teA A] \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> None \<notin> F_CFG_FIRST__fp_one G [teA A]
  \<Longrightarrow> Some x \<in> F_CFG_FIRST__fp_one G (teA A # w)
  \<Longrightarrow> Some x \<in> F_CFG_FIRST__fp_one G [teA A]"
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_12 G (F_CFG_FIRST__fp_one G)")
   apply(simp add: F_CFG_FIRST__table__fp_invariant_12_def)
   apply(erule_tac
      x = "A"
      in allE)
   apply(clarsimp)
   apply(erule_tac
      x = "x"
      in allE)
   apply(clarsimp)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_12)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_elem_teANotNoneEq: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> [teA A] \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> teA A # w \<in> F_CFG_FIRST__table_domain G
  \<Longrightarrow> None \<notin> F_CFG_FIRST__fp_one G [teA A]
  \<Longrightarrow> (F_CFG_FIRST__fp_one G [teA A]) = (F_CFG_FIRST__fp_one G (teA A # w))"
  apply(auto)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(rule F_CFG_FIRST__fp_one_elem_PostExtend1)
     apply(rename_tac a)(*strict*)
     apply(blast)+
  apply(rename_tac x)(*strict*)
  apply(case_tac x)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(rule F_CFG_FIRST__fp_one_elem_PostExtend5)
      apply(rename_tac a)(*strict*)
      apply(blast)+
  apply(subgoal_tac "\<forall>w\<in> F_CFG_FIRST__table_domain G. setB w = {} \<and> w \<noteq> [] \<and> (\<forall>i<length w. None \<in> F_CFG_FIRST__fp_one G [w ! i]) \<longrightarrow> None \<in> F_CFG_FIRST__table_recursive (length w) G (F_CFG_FIRST__fp_one G) w")
   prefer 2
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_16_unfold)
   apply(force)
  apply(erule_tac
      x="teA A#w"
      in ballE)
   prefer 2
   apply(force)
  apply(erule impE)
   prefer 2
   apply(subgoal_tac "F_CFG_FIRST__fp_one G = F_CFG_FIRST__table_recursive (length w) G (F_CFG_FIRST__fp_one G)")
    prefer 2
    apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table_recursive_idemp)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "\<forall>w\<in> F_CFG_FIRST__table_domain G. None \<in> F_CFG_FIRST__fp_one G w \<longrightarrow> setB w = {} \<and> (\<forall>i<length w. None \<in> F_CFG_FIRST__fp_one G [w ! i])")
    prefer 2
    apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_17_unfold)
    apply(force)
   apply(erule_tac
      x="(teA A)#w"
      in ballE)
    prefer 2
    apply(force)
   apply(erule impE)
    prefer 2
    apply(clarsimp)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
   apply(force)
  apply(subgoal_tac "\<forall>w\<in> F_CFG_FIRST__table_domain G. None \<in> F_CFG_FIRST__fp_one G w \<longrightarrow> setB w = {} \<and> (\<forall>i<length w. None \<in> F_CFG_FIRST__fp_one G [w ! i])")
   prefer 2
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_17_unfold)
   apply(force)
  apply(erule_tac
      x="teA A #w"
      in ballE)
   apply(clarsimp)
  apply(force)
  done

lemma F_CFG_FIRST__fp_eq_to_FUNFirstA_on_table_domain: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> w \<in> F_CFG_FIRST__table_domain G \<longrightarrow> F_CFG_FIRST__fp G w = F_CFG_FIRST__fp_one G w"
  apply(rule_tac
      xs = "w"
      in List.length_induct)
  apply(rename_tac xs)(*strict*)
  apply(clarify)
  apply(case_tac xs)
   apply(rename_tac xs)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_04 G (F_CFG_FIRST__fp_one G)")
    apply(simp add: F_CFG_FIRST__table__fp_invariant_04_def)
    apply(subgoal_tac "(F_CFG_FIRST__fp_one G) [] = {None}")
     apply(simp add: option_to_setMap_def)
    apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
     apply(rule sym)
     apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
     apply(blast)
    apply(blast)
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_04)
   apply(blast)
  apply(rename_tac xs a list)(*strict*)
  apply(simp del: F_CFG_FIRST__fp.simps)
  apply(clarify)
  apply(erule_tac
      x = "list"
      in allE)
  apply(erule impE)
   apply(rename_tac xs a list)(*strict*)
   apply(blast)
  apply(rename_tac xs a list)(*strict*)
  apply(erule impE)
   apply(rename_tac xs a list)(*strict*)
   apply(rule table_domainDecomp)
   apply(blast)
  apply(rename_tac xs a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac xs a list aa)(*strict*)
   defer
   apply(rename_tac xs a list b)(*strict*)
   apply(clarsimp)
   apply(rename_tac list b)(*strict*)
   apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_05 G (F_CFG_FIRST__fp_one G)")
    apply(rename_tac list b)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_invariant_05_def)
    apply(erule_tac
      x = "b"
      in allE)
    apply(erule_tac
      x = "list"
      in allE)
    apply(clarsimp)
    apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
     apply(rename_tac list b)(*strict*)
     apply(rule sym)
     apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
     apply(blast)
    apply(rename_tac list b)(*strict*)
    apply(clarsimp)
   apply(rename_tac list b)(*strict*)
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_05)
   apply(blast)
  apply(rename_tac xs a list aa)(*strict*)
  apply(simp del: F_CFG_FIRST__fp.simps)
  apply(rename_tac a list aa)(*strict*)
  apply(clarify)
  apply(rule_tac
      t = "F_CFG_FIRST__fp G (teA aa # list)"
      and s = "(F_CFG_FIRST__fp_one G [teA aa]- {None}) \<union> (if None \<in> F_CFG_FIRST__fp_one G [teA aa] then F_CFG_FIRST__fp G list else {})"
      in ssubst)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list aa)(*strict*)
  apply(rule_tac
      t="F_CFG_FIRST__fp G list"
      and s="F_CFG_FIRST__fp_one G list"
      in ssubst)
   apply(rename_tac a list aa)(*strict*)
   apply(force)
  apply(rename_tac a list aa)(*strict*)
  apply(thin_tac "F_CFG_FIRST__fp G list = F_CFG_FIRST__fp_one G list")
  apply(case_tac "None \<in> F_CFG_FIRST__fp_one G [teA aa]")
   apply(rename_tac a list aa)(*strict*)
   apply(rule_tac
      t="F_CFG_FIRST__fp_one G (teA aa # list)"
      and s="F_CFG_FIRST__fp_one G [teA aa] \<union> F_CFG_FIRST__fp_one G list - {x. x=None \<and> None \<notin> F_CFG_FIRST__fp_one G list}"
      in subst)
    apply(rename_tac a list aa)(*strict*)
    apply(rule F_CFG_FIRST__fp_one_elem_teANoneEq)
       apply(rename_tac a list aa)(*strict*)
       apply(force)
      apply(rename_tac a list aa)(*strict*)
      apply(force)
     apply(rename_tac a list aa)(*strict*)
     apply(rule table_domain__Cons_lhs2)
        apply(rename_tac a list aa)(*strict*)
        apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
       apply(rename_tac a list aa)(*strict*)
       apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
      apply(rename_tac a list aa)(*strict*)
      apply(force)
     apply(rename_tac a list aa)(*strict*)
     apply(force)
    apply(rename_tac a list aa)(*strict*)
    apply(force)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac list aa)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac list aa)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac list aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac list aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac list aa x)(*strict*)
    apply(case_tac x)
     apply(rename_tac list aa x)(*strict*)
     apply(clarsimp)
    apply(rename_tac list aa x a)(*strict*)
    apply(clarsimp)
   apply(rename_tac list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac list aa)(*strict*)
  apply(rule F_CFG_FIRST__fp_one_elem_teANotNoneEq)
     apply(rename_tac list aa)(*strict*)
     apply(blast)+
    apply(rename_tac list aa)(*strict*)
    defer
    apply(blast)+
  apply(rename_tac list aa)(*strict*)
  apply(rule_tac
      ?w1.0 = "[]"
      in table_domainDecomp3)
    apply(rename_tac list aa)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)+
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_08_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>A v x. \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G \<and> x \<in> (F_CFG_FIRST__fp_one G) v \<longrightarrow> x \<in> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G) [teA A]"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f A v x)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_08_def)
   apply(erule conjE)+
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f A v x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f A v x)(*strict*)
   apply(erule_tac
      x = "A"
      in allE)
   apply(erule_tac
      x = "v"
      and P="\<lambda>v. \<forall>x. \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G \<and> x \<in> f v \<longrightarrow> x \<in> f [teA A]"
      in allE)
   apply(erule_tac
      x = "x"
      in allE)
   apply(clarsimp)
   apply(rename_tac G f A v x)(*strict*)
   apply(rule_tac
      P="\<lambda>g. g = f"
      in F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplication0)
     apply(rename_tac G f A v x)(*strict*)
     apply(blast)+
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(auto)
  apply(rename_tac G f A v x)(*strict*)
  apply(erule_tac
      x = "A"
      in allE)
  apply(erule_tac
      x = "v"
      in allE)
  apply(erule_tac
      x = "x"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac G f A v x)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      and s = "F_CFG_FIRST__table__fp G f"
      in ssubst)
    apply(rename_tac G f A v x)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f A v x)(*strict*)
   apply(blast)
  apply(rename_tac G f A v x)(*strict*)
  apply(rule_tac
      s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      and t = "F_CFG_FIRST__table__fp G f"
      in ssubst)
   apply(rename_tac G f A v x)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f A v x)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_08: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_08 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_08_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_08_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_SingleProd: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> x \<in> F_CFG_FIRST__fp G w
  \<Longrightarrow> \<lparr>prod_lhs = A,prod_rhs = w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> x \<in> F_CFG_FIRST__fp G [teA A]"
  apply(subgoal_tac "[teA A] \<in> F_CFG_FIRST__table_domain G")
   prefer 2
   apply(rule table_domain__Cons_lhs)
   apply(force)
  apply(subgoal_tac "x \<in> ((F_CFG_FIRST__fp_one G w))")
   apply(subgoal_tac "x \<in> ((F_CFG_FIRST__fp_one G [teA A]))")
    apply(subgoal_tac "[teA A] \<in> F_CFG_FIRST__table_domain G \<longrightarrow> F_CFG_FIRST__fp G [teA A] = F_CFG_FIRST__fp_one G [teA A]")
     apply(erule impE)
      apply(force)
     apply(force)
    apply(rule F_CFG_FIRST__fp_eq_to_FUNFirstA_on_table_domain)
    apply(force)
   defer
   apply(subgoal_tac "w \<in> F_CFG_FIRST__table_domain G \<longrightarrow> F_CFG_FIRST__fp G w = (F_CFG_FIRST__fp_one G w)")
    apply(erule impE)
     apply(rule table_domain__Cons_rhs)
     apply(blast)
    apply(blast)
   apply(rule F_CFG_FIRST__fp_eq_to_FUNFirstA_on_table_domain)
   apply(blast)
  apply(thin_tac "x \<in> F_CFG_FIRST__fp G w")
  apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_08 G (F_CFG_FIRST__fp_one G)")
   apply(simp add: F_CFG_FIRST__table__fp_invariant_08_def)
   apply(erule_tac
      x = "A"
      in allE)
   apply(erule_tac
      x = "w"
      in allE)
   apply(erule_tac
      x = "x"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
    defer
    apply(clarsimp)
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_08)
   apply(blast)
  apply(rule sym)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_14_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>A. \<lparr>prod_lhs = A, prod_rhs = []\<rparr> \<in> cfg_productions G \<longrightarrow> None \<in> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)) [teA A]"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f A)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_14_def)
   apply(erule conjE)+
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f A)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f A)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f A)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(rename_tac G f A)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f A)(*strict*)
  apply(erule_tac
      x = "A"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f A)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f A)(*strict*)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_14: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_14 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_14_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_14_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_16: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_16 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_16_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_16_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_15_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>A w. \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<in> cfg_productions G \<and> None \<in> (F_CFG_FIRST__fp_one G) w \<longrightarrow> None \<in> F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G) [teA A]"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f A w)(*strict*)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_15_def)
   apply(erule conjE)+
   apply(subgoal_tac "F_CFG_FIRST__table__fp G f = f")
    apply(rename_tac G f A w)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x = "A"
      in allE)
    apply(clarsimp)
   apply(rename_tac G f A w)(*strict*)
   apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f A w)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)+
   apply(rename_tac G f A w)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f A w)(*strict*)
  apply(erule_tac
      x = "A"
      in allE)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
   apply(rename_tac G f A w)(*strict*)
   apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
   apply(blast)
  apply(rename_tac G f A w)(*strict*)
  apply(erule impE)
   apply(rename_tac G f A w)(*strict*)
   apply(rule_tac
      x = "w"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      s = "F_CFG_FIRST__table__fp G f"
      and t = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f)"
      in ssubst)
    apply(rename_tac G f A w)(*strict*)
    apply(rule sym)
    apply(rule F_CFG_FIRST__table__fp_F_CFG_FIRST__table__fp_one_idemp2)
    apply(blast)
   apply(rename_tac G f A w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f A w)(*strict*)
  apply(force)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_15: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> F_CFG_FIRST__table__fp_invariant_15 G (F_CFG_FIRST__fp_one G)"
  apply(unfold F_CFG_FIRST__table__fp_invariant_15_def)
  apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_15_unfold)
  apply(blast)
  done

lemma F_CFG_FIRST__fp_one_NoneDeri_NoneElem: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> maximum_of_domain d (Suc k)
  \<Longrightarrow> None \<in> F_CFG_FIRST__fp_one G [teA A]"
  apply(subgoal_tac "\<forall>k d A. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<longrightarrow> maximum_of_domain d (Suc k) \<longrightarrow> None \<in> F_CFG_FIRST__fp_one G [teA A]")
   apply(blast)
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}")
  apply(thin_tac "maximum_of_domain d (Suc k)")
  apply(rule allI)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      n = "k"
      in nat_less_induct)
  apply(rename_tac k n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d A)(*strict*)
  apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
   apply(rename_tac n d A)(*strict*)
   defer
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_def)
   apply(clarsimp)
   apply(erule_tac
      x = "Suc 0"
      and P="\<lambda>x. case x of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (d 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G i'2 i1v i2)) (d i'))) (d x)"
      in allE)
   apply(rename_tac n d A)(*strict*)
   apply(auto)
   apply(case_tac "d 0")
    apply(rename_tac n d A)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d A a)(*strict*)
   apply(case_tac a)
   apply(rename_tac n d A a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d A)(*strict*)
  apply(subgoal_tac "\<exists>xa. d (Suc n) = Some (pair xa \<lparr>cfg_conf = []\<rparr>)")
   apply(rename_tac n d A)(*strict*)
   prefer 2
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rename_tac n d A)(*strict*)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac n d A)(*strict*)
   apply(blast)
  apply(rename_tac n d A)(*strict*)
  apply(case_tac n)
   apply(rename_tac n d A)(*strict*)
   apply(auto)
   apply(rename_tac d A xa)(*strict*)
   apply(subgoal_tac "\<lparr>prod_lhs = A,prod_rhs = []\<rparr> \<in> cfg_productions G")
    apply(rename_tac d A xa)(*strict*)
    apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_14 G (F_CFG_FIRST__fp_one G)")
     apply(rename_tac d A xa)(*strict*)
     apply(simp only: F_CFG_FIRST__table__fp_invariant_14_def)
     apply(erule_tac
      x = "A"
      in allE)
     apply(clarsimp)
     apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
      apply(rename_tac d A xa)(*strict*)
      apply(rule sym)
      apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
      apply(blast)+
     apply(rename_tac d A xa)(*strict*)
     apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
      apply(rename_tac d A xa)(*strict*)
      apply(rule sym)
      apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
      apply(blast)+
    apply(rename_tac d A xa)(*strict*)
    apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_14)
    apply(blast)
   apply(rename_tac d A xa)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_def)
   apply(clarsimp)
   apply(erule_tac
      x = "Suc 0"
      in allE)
   apply(auto)
   apply(case_tac "d (Suc 0)")
    apply(rename_tac d A xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac d A xa a)(*strict*)
   apply(case_tac a)
   apply(rename_tac d A xa a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A xa)(*strict*)
   apply(case_tac xa)
    apply(rename_tac d A xa)(*strict*)
    apply(auto)
   apply(rename_tac d A a)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d a)(*strict*)
   apply(case_tac a,clarsimp)
  apply(rename_tac d A nat xa)(*strict*)
  apply(subgoal_tac "\<exists>w. d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = A,prod_rhs = w\<rparr>) \<lparr>cfg_conf = w\<rparr>) \<and> \<lparr>prod_lhs = A,prod_rhs = w\<rparr> \<in> cfg_productions G")
   apply(rename_tac d A nat xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A nat xa w)(*strict*)
   apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_15 G (F_CFG_FIRST__fp_one G)")
    apply(rename_tac d A nat xa w)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_invariant_15_def)
    apply(erule_tac
      x = "A"
      in allE)
    apply(erule impE)
     apply(rename_tac d A nat xa w)(*strict*)
     apply(rule_tac
      x = "w"
      in exI)
     apply(clarsimp)
     apply(subgoal_tac "F_CFG_FIRST__table__fp_invariant_16 G (F_CFG_FIRST__fp_one G)")
      apply(rename_tac d A nat xa w)(*strict*)
      apply(simp add: F_CFG_FIRST__table__fp_invariant_16_def)
      apply(erule_tac
      x = "w"
      in ballE)
       apply(rename_tac d A nat xa w)(*strict*)
       apply(erule impE)
        apply(rename_tac d A nat xa w)(*strict*)
        defer
        apply(rule_tac
      s = "F_CFG_FIRST__table_recursive (length w) G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
         apply(rename_tac d A nat xa w)(*strict*)
         defer
         apply(clarsimp)
        apply(rename_tac d A nat xa w)(*strict*)
        apply(subgoal_tac "w \<in> F_CFG_FIRST__table_domain G")
         apply(rename_tac d A nat xa w)(*strict*)
         apply(blast)
        apply(rename_tac d A nat xa w)(*strict*)
        apply(rule table_domain__Cons_rhs)
        apply(blast)
       apply(rename_tac d A nat xa w)(*strict*)
       apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_16)
       apply(blast)
      apply(rename_tac d A nat xa w)(*strict*)
      apply(rule_tac
      s = "F_CFG_FIRST__table__fp_one G (F_CFG_FIRST__fp_one G)"
      and t = "F_CFG_FIRST__fp_one G"
      in ssubst)
       apply(rename_tac d A nat xa w)(*strict*)
       defer
       apply(blast)
      apply(rename_tac d A nat xa w)(*strict*)
      apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_15)
      apply(blast)
     apply(rename_tac d A nat xa)(*strict*)
     apply(case_tac "d (Suc 0)")
      apply(rename_tac d A nat xa)(*strict*)
      apply(rule_tac
      n = "Suc 0"
      in cfgSTD.maximum_of_domainSmaller)
         apply(rename_tac d A nat xa)(*strict*)
         apply(blast)
        apply(rename_tac d A nat xa)(*strict*)
        apply(rule cfgSTD.from_to_is_der)
        apply(blast)
       apply(rename_tac d A nat xa)(*strict*)
       apply(arith)
      apply(rename_tac d A nat xa)(*strict*)
      apply(blast)
     apply(rename_tac d A nat xa a)(*strict*)
     apply(case_tac "d (Suc 0)")
      apply(rename_tac d A nat xa a)(*strict*)
      apply(rule_tac
      n = "Suc 0"
      in cfgSTD.maximum_of_domainSmaller)
         apply(rename_tac d A nat xa a)(*strict*)
         apply(blast)
        apply(rename_tac d A nat xa a)(*strict*)
        apply(rule cfgSTD.from_to_is_der)
        apply(blast)
       apply(rename_tac d A nat xa a)(*strict*)
       apply(arith)
      apply(rename_tac d A nat xa a)(*strict*)
      apply(blast)
     apply(rename_tac d A nat xa a aa)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_def cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac d A nat xa a)(*strict*)
     apply(erule_tac
      x = "Suc 0"
      and P="\<lambda>x. case x of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (d 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G i'2 i1v i2)) (d i'))) (d x)"
      in allE)
     apply(rename_tac d A nat xa a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac d A nat xa a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d A nat xa option b)(*strict*)
     apply(case_tac option)
      apply(rename_tac d A nat xa option b)(*strict*)
      apply(clarsimp)
     apply(rename_tac d A nat xa option b a)(*strict*)
     apply(clarsimp)
     apply(rename_tac d A nat xa b a)(*strict*)
     apply(case_tac a)
     apply(rename_tac d A nat xa b a prod_lhs prod_rhs)(*strict*)
     apply(clarsimp)
     apply(rename_tac d A nat xa b prod_lhs prod_rhs)(*strict*)
     apply(case_tac b)
     apply(rename_tac d A nat xa b prod_lhs prod_rhs cfg_conf)(*strict*)
     apply(clarsimp)
     apply(rename_tac d A nat xa prod_lhs prod_rhs cfg_conf)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac d A nat xa prod_lhs prod_rhs l r)(*strict*)
     apply(case_tac l)
      apply(rename_tac d A nat xa prod_lhs prod_rhs l r)(*strict*)
      apply(clarsimp)
     apply(rename_tac d A nat xa prod_lhs prod_rhs l r a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac d A nat xa w)(*strict*)
    defer
    apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table_recursive_idemp)
    apply(blast)
   apply(rename_tac d A nat xa w)(*strict*)
   apply(rule sym)
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_one_idemp)
   apply(blast)
  apply(rename_tac d A nat xa w)(*strict*)
  apply(subgoal_tac "setB w = {} \<and> (\<forall>i<length w. \<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [w!i]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<and> (\<forall>k. maximum_of_domain d k \<longrightarrow> (k<Suc nat \<or> (k = Suc nat \<and> length w = 1))))")
   apply(rename_tac d A nat xa w)(*strict*)
   prefer 2
   apply(rule_tac
      d = "derivation_drop d (Suc 0)"
      in canElimAll)
       apply(rename_tac d A nat xa w)(*strict*)
       apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
      apply(rename_tac d A nat xa w)(*strict*)
      prefer 2
      apply(rule derivation_drop_preserves_generates_maximum_of_domain)
      apply(blast)
     apply(rename_tac d A nat xa w)(*strict*)
     apply(rule_tac
      m = "Suc nat"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
        apply(rename_tac d A nat xa w)(*strict*)
        apply(blast)
       apply(rename_tac d A nat xa w)(*strict*)
       apply(rule_tac
      s = "Suc (Suc nat)"
      in ssubst)
        apply(rename_tac d A nat xa w)(*strict*)
        apply(arith)
       apply(rename_tac d A nat xa w)(*strict*)
       apply(blast)
      apply(rename_tac d A nat xa w)(*strict*)
      apply(blast)
     apply(rename_tac d A nat xa w)(*strict*)
     apply(clarsimp)
    apply(rename_tac d A nat xa w)(*strict*)
    apply(simp add: derivation_drop_def)
   apply(rename_tac d A nat xa w)(*strict*)
   apply(simp add: derivation_drop_def)
  apply(rename_tac d A nat xa w)(*strict*)
  apply(rule conjI)
   apply(rename_tac d A nat xa w)(*strict*)
   apply(blast)
  apply(rename_tac d A nat xa w)(*strict*)
  apply(rule conjI)
   apply(rename_tac d A nat xa w)(*strict*)
   defer
   apply(rename_tac d A nat xa w)(*strict*)
   apply(rule allI)
   apply(rename_tac d A nat xa w i)(*strict*)
   apply(rule impI)
   apply(erule conjE)
   apply(erule_tac
      x = "i"
      and P="\<lambda>i. i < length w \<longrightarrow> (\<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [w ! i]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<and> (\<forall>k. maximum_of_domain d k \<longrightarrow> k < Suc nat \<or> k = Suc nat \<and> length w = 1))"
      in allE)
   apply(rename_tac d A nat xa w i)(*strict*)
   apply(erule impE)
    apply(rename_tac d A nat xa w i)(*strict*)
    apply(clarsimp)
   apply(rename_tac d A nat xa w i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A nat xa w i da)(*strict*)
   apply(subgoal_tac "\<exists>m. maximum_of_domain da (Suc m)")
    apply(rename_tac d A nat xa w i da)(*strict*)
    apply(clarsimp)
    apply(rename_tac d A nat xa w i da m)(*strict*)
    apply(erule_tac
      x = "m"
      and P="\<lambda>m. m < Suc nat \<longrightarrow> (\<forall>d A. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<longrightarrow> maximum_of_domain d (Suc m) \<longrightarrow> None \<in> F_CFG_FIRST__fp_one G [teA A])"
      in allE)
    apply(rename_tac d A nat xa w i da m)(*strict*)
    apply(erule impE)
     apply(rename_tac d A nat xa w i da m)(*strict*)
     apply(erule_tac
      x = "Suc m"
      in allE)
     apply(erule impE)
      apply(rename_tac d A nat xa w i da m)(*strict*)
      apply(clarsimp)
     apply(rename_tac d A nat xa w i da m)(*strict*)
     apply(erule disjE)
      apply(rename_tac d A nat xa w i da m)(*strict*)
      apply(clarsimp)
     apply(rename_tac d A nat xa w i da m)(*strict*)
     apply(clarsimp)
    apply(rename_tac d A nat xa w i da m)(*strict*)
    prefer 2
    apply(rename_tac d A nat xa w i da)(*strict*)
    apply(subgoal_tac "\<exists>m. maximum_of_domain da m")
     apply(rename_tac d A nat xa w i da)(*strict*)
     apply(clarsimp)
     apply(rename_tac d A nat xa w i da m)(*strict*)
     prefer 2
     apply(rename_tac d A nat xa w i da)(*strict*)
     apply(rule cfgSTD.to_has_maximum_of_domain)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac d A nat xa w i da m)(*strict*)
    apply(case_tac m)
     apply(rename_tac d A nat xa w i da m)(*strict*)
     apply(clarsimp)
     apply(rename_tac d A nat xa w i da)(*strict*)
     apply(subgoal_tac "[w!i] = []")
      apply(rename_tac d A nat xa w i da)(*strict*)
      apply(clarsimp)
     apply(rename_tac d A nat xa w i da)(*strict*)
     apply(rule emptyDerOfEmpty)
      apply(rename_tac d A nat xa w i da)(*strict*)
      apply(blast)
     apply(rename_tac d A nat xa w i da)(*strict*)
     apply(blast)
    apply(rename_tac d A nat xa w i da m nata)(*strict*)
    apply(blast)
   apply(rename_tac d A nat xa w i da m)(*strict*)
   apply(erule_tac
      x = "da"
      in allE)
   apply(subgoal_tac "\<exists>A. w!i = teA A")
    apply(rename_tac d A nat xa w i da m)(*strict*)
    apply(clarsimp)
   apply(rename_tac d A nat xa w i da m)(*strict*)
   apply(rule has_elem_setA)
    apply(rename_tac d A nat xa w i da m)(*strict*)
    apply(blast)
   apply(rename_tac d A nat xa w i da m)(*strict*)
   apply(blast)
  apply(rename_tac d A nat xa w)(*strict*)
  apply(case_tac w)
   apply(rename_tac d A nat xa w)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A nat xa)(*strict*)
   defer
   apply(rename_tac d A nat xa w a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d A nat xa)(*strict*)
  apply(rule_tac
      m = "Suc 0"
      in cfgSTD.noDeadEndBeforeMaxDom)
      apply(rename_tac d A nat xa)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac d A nat xa)(*strict*)
     apply(blast)
    apply(rename_tac d A nat xa)(*strict*)
    apply(blast)
   apply(rename_tac d A nat xa)(*strict*)
   apply(arith)
  apply(rename_tac d A nat xa)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  done

lemma soundnessPt2: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> x \<in> cfg_events G
  \<Longrightarrow> \<forall>n w d w'. setB w \<subseteq> cfg_events G \<and> setA w \<subseteq> cfg_nonterminals G \<and> maximum_of_domain d n \<and> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = (Cons (teB x) w')\<rparr>} \<longrightarrow> Some x \<in> F_CFG_FIRST__fp G w"
  apply(rule allI)
  apply(rename_tac n)(*strict*)
  apply(rule nat_less_induct)
  apply(rename_tac n na)(*strict*)
  apply(case_tac na)
   apply(rename_tac n na)(*strict*)
   apply(clarsimp)
   apply(rename_tac w d w')(*strict*)
   apply(subgoal_tac "w=teB x#w'")
    apply(rename_tac w d w')(*strict*)
    apply(clarsimp)
   apply(rename_tac w d w')(*strict*)
   apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
    apply(rename_tac w d w')(*strict*)
    apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = teB x#w'\<rparr>)")
     apply(rename_tac w d w')(*strict*)
     apply(clarsimp)
    apply(rename_tac w d w')(*strict*)
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac w d w')(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac w d w')(*strict*)
    apply(clarsimp)
   apply(rename_tac w d w')(*strict*)
   apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w\<rparr>}. d 0 = Some x")
    apply(rename_tac w d w')(*strict*)
    apply(blast)
   apply(rename_tac w d w')(*strict*)
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac n na nat)(*strict*)
  apply(rule allI)
  apply(rename_tac n na nat w)(*strict*)
  apply(rule_tac
      xs = "w"
      in length_induct)
  apply(rename_tac n na nat w xs)(*strict*)
  apply(case_tac "length xs")
   apply(rename_tac n na nat w xs)(*strict*)
   apply(subgoal_tac "xs = []")
    apply(rename_tac n na nat w xs)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat d w')(*strict*)
    apply(rule_tac
      M = "G"
      and ?c1.0 = "\<lparr>cfg_conf = []\<rparr>"
      in cfgSTD.noNonEmptyDeriFromEmpty)
      apply(rename_tac nat d w')(*strict*)
      apply(clarsimp)
      apply(rename_tac nat d w' e c2)(*strict*)
      apply(simp add: cfgSTD_step_relation_def)
     apply(rename_tac nat d w')(*strict*)
     apply(blast)
    apply(rename_tac nat d w')(*strict*)
    apply(rule cfgSTD.from_to_is_from)
    apply(blast)
   apply(rename_tac n na nat w xs)(*strict*)
   apply(blast)
  apply(rename_tac n na nat w xs nata)(*strict*)
  apply(case_tac xs)
   apply(rename_tac n na nat w xs nata)(*strict*)
   apply(force)
  apply(rename_tac n na nat w xs nata a list)(*strict*)
  apply(rule allI)+
  apply(rename_tac n na nat w xs nata a list d w')(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(rename_tac n1 dl n3 w1 w2 n4 y w3 d w4)
  apply(rename_tac n1 dl n3 w1 w2 n4 y w3 d w4)(*strict*)
  apply(simp del: F_CFG_FIRST__fp.simps)
  apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
  apply(subgoal_tac " (\<exists>d w''. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [y]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w''\<rparr>} \<and> (\<forall>k. (maximum_of_domain d k \<longrightarrow> (k \<le> dl)) ) ) \<or> ((\<exists>d1 d2 k1 k2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = [y]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<and> maximum_of_domain d1 (Suc k1) \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w4\<rparr>} \<and> maximum_of_domain d2 k2 \<and> (Suc k1)+k2 = dl )) ")
   apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
   apply(erule disjE)
    apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
    apply(clarify)
    apply(rename_tac dl n3 w2 n4 y w3 d w4 da w'')(*strict*)
    apply(simp del: F_CFG_FIRST__fp.simps)
    apply(rename_tac n3 y w3 d w4 da w'')(*strict*)
    apply(subgoal_tac "\<exists>m. maximum_of_domain da m")
     apply(rename_tac n3 y w3 d w4 da w'')(*strict*)
     prefer 2
     apply(rule_tac cfgSTD.to_has_maximum_of_domain)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac n3 y w3 d w4 da w'')(*strict*)
    apply(erule exE)
    apply(rename_tac n3 y w3 d w4 da w'' m)(*strict*)
    apply(subgoal_tac "m \<le> Suc n3")
     apply(rename_tac n3 y w3 d w4 da w'' m)(*strict*)
     prefer 2
     apply(erule_tac
      x = "m"
      and P="\<lambda>m. maximum_of_domain da m \<longrightarrow> m \<le> Suc n3"
      in allE)
     apply(clarsimp)
    apply(rename_tac n3 y w3 d w4 da w'' m)(*strict*)
    apply(case_tac "w3")
     apply(rename_tac n3 y w3 d w4 da w'' m)(*strict*)
     apply(simp del: F_CFG_FIRST__fp.simps)
     apply(clarify)
     apply(thin_tac "(\<exists>d. maximum_of_domain d (Suc n3) \<and> (\<exists>w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = []\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w'\<rparr>})) \<longrightarrow> Some x \<in> F_CFG_FIRST__fp G []")
     apply(rename_tac n3 y w3 d w4 da w'' m)(*strict*)
     apply(thin_tac "cfgSTD.derivation_from_to G da {pair None \<lparr>cfg_conf = [y]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w''\<rparr>}")
     apply(rename_tac n3 y w3 d w4 da w'' m)(*strict*)
     apply(thin_tac "\<forall>k. maximum_of_domain da k \<longrightarrow> k \<le> Suc n3")
     apply(thin_tac "maximum_of_domain da m")
     apply(simp del: F_CFG_FIRST__fp.simps)
     apply(rename_tac n3 y d w4)(*strict*)
     apply(subgoal_tac "Some x \<in> (case y of teA A \<Rightarrow> (F_CFG_FIRST__fp_one G ([y])) | teB a \<Rightarrow> {Some a})")
      apply(rename_tac n3 y d w4)(*strict*)
      apply(simp)
      apply(case_tac "y")
       apply(rename_tac n3 y d w4 a)(*strict*)
       apply(clarsimp)
      apply(rename_tac n3 y d w4 b)(*strict*)
      apply(clarsimp)
     apply(rename_tac n3 y d w4)(*strict*)
     apply(case_tac y)
      apply(rename_tac n3 y d w4 a)(*strict*)
      apply(simp del: F_CFG_FIRST__fp.simps)
      apply(clarify)
      prefer 2
      apply(rename_tac n3 y d w4 b)(*strict*)
      apply(clarsimp)
      apply(rename_tac n3 d w4 b)(*strict*)
      apply(rule noStepFromTerminal)
      apply(blast)
     apply(rename_tac n3 y d w4 a)(*strict*)
     apply(subgoal_tac "\<exists>w. (cfgSTD_step_relation G \<lparr>cfg_conf = [teA a]\<rparr> \<lparr>prod_lhs = a,prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr> \<and> (d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = a,prod_rhs = w\<rparr>) \<lparr>cfg_conf = w\<rparr>)) \<and> \<lparr>prod_lhs = a,prod_rhs = w\<rparr> \<in> cfg_productions G) ")
      apply(rename_tac n3 y d w4 a)(*strict*)
      apply(erule exE)+
      apply(rename_tac n3 y d w4 a w)(*strict*)
      apply(erule_tac
      x = "n3"
      in allE)
      apply(simp del: F_CFG_FIRST__fp.simps,clarify)
      apply(rename_tac n3 d w4 a w)(*strict*)
      apply(erule_tac
      x = "w"
      in allE)
      apply(erule impE)
       apply(rename_tac n3 d w4 a w)(*strict*)
       prefer 2
       apply(subgoal_tac "Some x \<in> F_CFG_FIRST__fp G [teA a]")
        apply(rename_tac n3 d w4 a w)(*strict*)
        apply(clarsimp)
        apply(case_tac "None \<in> F_CFG_FIRST__fp_one G [teA a]")
         apply(rename_tac n3 d w4 a w)(*strict*)
         apply(clarsimp)
        apply(rename_tac n3 d w4 a w)(*strict*)
        apply(clarsimp)
       apply(rename_tac n3 d w4 a w)(*strict*)
       apply(rule_tac
      w = "w"
      in F_CFG_FIRST__fp_SingleProd)
         apply(rename_tac n3 d w4 a w)(*strict*)
         apply(clarsimp)
        apply(rename_tac n3 d w4 a w)(*strict*)
        apply(clarsimp)
       apply(rename_tac n3 d w4 a w)(*strict*)
       apply(clarsimp)
      apply(rename_tac n3 d w4 a w)(*strict*)
      apply(rule conjI)
       apply(rename_tac n3 d w4 a w)(*strict*)
       apply(rule prod_rhs_in_cfg_events2)
        apply(rename_tac n3 d w4 a w)(*strict*)
        apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
       apply(rename_tac n3 d w4 a w)(*strict*)
       apply(blast)+
      apply(rename_tac n3 d w4 a w)(*strict*)
      apply(rule conjI)
       apply(rename_tac n3 d w4 a w)(*strict*)
       apply(rule prod_rhs_in_nonterms)
        apply(rename_tac n3 d w4 a w)(*strict*)
        apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
       apply(rename_tac n3 d w4 a w)(*strict*)
       apply(blast)+
      apply(rename_tac n3 d w4 a w)(*strict*)
      apply(rule_tac
      x = "derivation_drop d (Suc 0)"
      in exI)
      apply(rule conjI)
       apply(rename_tac n3 d w4 a w)(*strict*)
       apply(rule derivation_drop_preserves_generates_maximum_of_domain)
       apply(blast)
      apply(rename_tac n3 d w4 a w)(*strict*)
      apply(rule_tac
      x = "w4"
      in exI)
      apply(rule_tac
      m = "n3"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
         apply(rename_tac n3 d w4 a w)(*strict*)
         apply(blast)
        apply(rename_tac n3 d w4 a w)(*strict*)
        apply(rule_tac
      s = "Suc n3"
      in ssubst)
         apply(rename_tac n3 d w4 a w)(*strict*)
         apply(arith)
        apply(rename_tac n3 d w4 a w)(*strict*)
        apply(blast)
       apply(rename_tac n3 d w4 a w)(*strict*)
       apply(blast)
      apply(rename_tac n3 d w4 a w)(*strict*)
      apply(clarsimp)
      apply(rename_tac d w4 a w)(*strict*)
      apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = teB x#w4\<rparr>)")
       apply(rename_tac d w4 a w)(*strict*)
       apply(clarsimp)
      apply(rename_tac d w4 a w)(*strict*)
      apply(rule cfgSTD.reachesToAtMaxDom)
       apply(rename_tac d w4 a w)(*strict*)
       apply(rule cfgSTD.from_to_is_to)
       apply(blast)
      apply(rename_tac d w4 a w)(*strict*)
      apply(blast)
     apply(rename_tac n3 y d w4 a)(*strict*)
     apply(rule hasStep)
      apply(rename_tac n3 y d w4 a)(*strict*)
      apply(blast)
     apply(rename_tac n3 y d w4 a)(*strict*)
     apply(blast)
    apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
    defer
    apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
    apply(simp del: F_CFG_FIRST__fp.simps)
    apply(clarify)
    apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
    apply(subgoal_tac "Some x \<in> F_CFG_FIRST__fp G w3")
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
     apply(subgoal_tac "None \<in> F_CFG_FIRST__fp_one G [y]")
      apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
      apply(clarsimp)
      apply(rename_tac y w3 d w4 d1 d2 k1 k2)(*strict*)
      apply(case_tac y)
       apply(rename_tac y w3 d w4 d1 d2 k1 k2 a)(*strict*)
       apply(clarsimp)
      apply(rename_tac y w3 d w4 d1 d2 k1 k2 b)(*strict*)
      apply(clarsimp)
      apply(rename_tac w3 d w4 d1 d2 k1 k2 b)(*strict*)
      apply(subgoal_tac "\<forall>x l. F_CFG_FIRST__fp_one SSG (teB x # l) \<subseteq> {Some x}" for SSG)
       apply(rename_tac w3 d w4 d1 d2 k1 k2 b)(*strict*)
       prefer 2
       apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_06_unfold)
       apply(blast)
      apply(rename_tac w3 d w4 d1 d2 k1 k2 b)(*strict*)
      apply(erule_tac
      x = "b"
      in allE)
      apply(erule_tac
      x = "[]"
      and P="\<lambda>l. F_CFG_FIRST__fp_one G (teB b # l) \<subseteq> {Some b}"
      in allE)
      apply(force)
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
     prefer 2
     apply(erule_tac
      x = "k2"
      in allE)
     apply(erule impE)
      apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
      apply(arith)
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
     apply(erule_tac
      x = "w3"
      and P="\<lambda>w3. setB w3 \<subseteq> cfg_events G \<and> setA w3 \<subseteq> cfg_nonterminals G \<and> (\<exists>d. maximum_of_domain d k2 \<and> (\<exists>w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w'\<rparr>})) \<longrightarrow> Some x \<in> F_CFG_FIRST__fp G w3"
      in allE)
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
     apply(erule impE)
      apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
      apply(clarsimp)
      apply(rename_tac y w3 d w4 d1 d2 k1 k2)(*strict*)
      apply(rule_tac
      x = "d2"
      in exI)
      apply(clarsimp)
      apply(rule_tac
      x = "w4"
      in exI)
      apply(clarsimp)
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
     apply(clarsimp)
    apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
    apply(subgoal_tac "\<exists>A. y = teA A")
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
     apply(erule exE)
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 A)(*strict*)
     apply(simp del: F_CFG_FIRST__fp.simps)
     apply(rename_tac y w3 d w4 d1 d2 k1 k2 A)(*strict*)
     apply(clarify)
     apply(rule F_CFG_FIRST__fp_one_NoneDeri_NoneElem)
       apply(rename_tac y w3 d w4 d1 d2 k1 k2 A)(*strict*)
       apply(blast)
      apply(rename_tac y w3 d w4 d1 d2 k1 k2 A)(*strict*)
      apply(blast)
     apply(rename_tac y w3 d w4 d1 d2 k1 k2 A)(*strict*)
     apply(blast)
    apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2)(*strict*)
    apply(case_tac y)
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 a)(*strict*)
     apply(clarsimp)
    apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
    apply(clarify)
    apply(subgoal_tac "d1 0 = Some (pair None \<lparr>cfg_conf = [teB b]\<rparr>)")
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
     apply(subgoal_tac "\<exists>e. d1 (Suc k1) = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
      apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
      apply(subgoal_tac "(\<exists>e w. d1 ((Suc k1)) = Some (pair e \<lparr>cfg_conf = teB b # w\<rparr>))")
       apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
       apply(clarsimp)
      apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
      apply(rule_tac
      ?e1.0 = "None"
      and w = "[]"
      and m = "0"
      and n = "Suc k1"
      in terminal_at_beginning_are_never_modified)
          apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
          apply(rule cfgSTD.from_to_is_der)
          apply(force)
         apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
         apply(rule_tac
      s = "Suc k1"
      in ssubst)
          apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
          apply(arith)
         apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
         apply(clarsimp)
        apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
        apply(clarsimp)
       apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
       apply(arith)
      apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
      apply(arith)
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
     apply(rule cfgSTD.reachesToAtMaxDom)
      apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
      apply(rule cfgSTD.from_to_is_to)
      apply(force)
     apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
     apply(force)
    apply(rename_tac dl n3 w2 n4 y w3 d w4 d1 d2 k1 k2 b)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_def)
    apply(rename_tac w3 d w4 d1 d2 k1 k2 b)(*strict*)
    apply(case_tac "d1 0")
     apply(rename_tac w3 d w4 d1 d2 k1 k2 b)(*strict*)
     apply(clarsimp)
    apply(rename_tac w3 d w4 d1 d2 k1 k2 b a)(*strict*)
    apply(case_tac a)
    apply(rename_tac w3 d w4 d1 d2 k1 k2 b a option ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
   apply(rule_tac
      s = "Suc n3"
      and t = "dl"
      in ssubst)
    apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
    apply(clarify)
   apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
   apply(rule twoCasesOfDerivations)
    apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
    apply(blast)
   apply(rename_tac dl n3 w2 n4 y w3 d w4)(*strict*)
   apply(blast)
  apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
  apply(subgoal_tac "Some x \<in> F_CFG_FIRST__fp G [y]")
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac n3 y d w4 da w'' m a list)(*strict*)
   apply(case_tac y)
    apply(rename_tac n3 y d w4 da w'' m a list aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n3 d w4 da w'' m a list aa)(*strict*)
    apply(rule conjI)
     apply(rename_tac n3 d w4 da w'' m a list aa)(*strict*)
     apply(rule impI)
     apply(clarsimp)
    apply(rename_tac n3 d w4 da w'' m a list aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac n3 y d w4 da w'' m a list b)(*strict*)
   apply(clarsimp)
  apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
  apply(case_tac "m<Suc n3")
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(erule_tac
      x = "m"
      and P="\<lambda>m. m < Suc n3 \<longrightarrow> (\<forall>w. setB w \<subseteq> cfg_events G \<and> setA w \<subseteq> cfg_nonterminals G \<and> (\<exists>d. maximum_of_domain d m \<and> (\<exists>w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w'\<rparr>})) \<longrightarrow> Some x \<in> F_CFG_FIRST__fp G w)"
      in allE)
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(erule impE)
    apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(erule_tac
      x = "[y]"
      and P="\<lambda>y. setB y \<subseteq> cfg_events G \<and> setA y \<subseteq> cfg_nonterminals G \<and> (\<exists>d. maximum_of_domain d m \<and> (\<exists>w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = y\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w'\<rparr>})) \<longrightarrow> Some x \<in> F_CFG_FIRST__fp G y"
      in allE)
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(erule impE)
    apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
    apply(rule conjI,clarsimp)
    apply(rule conjI,clarsimp)
    apply(rule_tac
      x = "da"
      in exI)
    apply(rule conjI)
     apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
    apply(rule_tac
      x = "w''"
      in exI)
    apply(clarsimp)
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
  apply(erule_tac
      x = "[y]"
      in allE)
  apply(erule impE)
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
  apply(erule impE)
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   defer
   apply(clarsimp)
  apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
  apply(rule conjI,clarsimp)
  apply(rule conjI,clarsimp)
  apply(rule_tac
      x = "da"
      in exI)
  apply(rule conjI)
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(subgoal_tac "m = Suc n3")
    apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
   apply(arith)
  apply(rename_tac n3 y w3 d w4 da w'' m a list)(*strict*)
  apply(rule_tac
      x = "w''"
      in exI)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_02_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>w. F_CFG_FIRST__fp_one G w \<subseteq> cfgSTD_first_symbol_of_derivable_effect G w"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(rename_tac G f)
   apply(clarsimp)
   apply(rename_tac G f w x)(*strict*)
   apply(rule_tac
      A = "(f w)"
      in set_mp)
    apply(rename_tac G f w x)(*strict*)
    apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_02_def)
   apply(rename_tac G f w x)(*strict*)
   apply(rule_tac
      P="\<lambda>f. x \<in> (f w)"
      in F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplicationRev0)
     apply(rename_tac G f w x)(*strict*)
     apply(blast)+
  apply(rename_tac Ga f)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f w x)(*strict*)
  apply(rule_tac
      A = "(F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f) w)"
      in set_mp)
   apply(rename_tac G f w x)(*strict*)
   apply(blast)
  apply(rename_tac G f w x)(*strict*)
  apply(rule_tac
      A = "(F_CFG_FIRST__table__fp G f w)"
      in set_mp)
   apply(rename_tac G f w x)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac G f w x)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f w"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f) w"
      in ssubst)
   apply(rename_tac G f w x)(*strict*)
   apply(case_tac "f = F_CFG_FIRST__table__fp_one G f")
    apply(rename_tac G f w x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f w x)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x w = F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f) w"
      and t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f w x)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)
   apply(rename_tac G f w x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f w x)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_01_unfold: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>w. None \<in> (F_CFG_FIRST__fp_one G w) \<longrightarrow> (\<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>})"
  apply(rule F_CFG_FIRST__fp_one_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga f)(*strict*)
   defer
   apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
   apply(rename_tac G f)(*strict*)
   apply(clarsimp)
   apply(rename_tac G f w)(*strict*)
   apply(rename_tac G f w)
   apply(simp add: F_CFG_FIRST__table__fp_invariants_def F_CFG_FIRST__table__fp_invariant_01_def)
   apply(erule conjE)
   apply(erule_tac
      x = "w"
      in allE)
   apply(auto)
   apply(subgoal_tac "None \<in> f w")
    apply(rename_tac G f w)(*strict*)
    apply(blast)
   apply(rename_tac G f w)(*strict*)
   apply(rule_tac
      P="\<lambda>f. None \<in> f w"
      in F_CFG_FIRST__table__fp_one_F_CFG_FIRST__table__fp_endSimpsApplicationRev0)
     apply(rename_tac G f w)(*strict*)
     apply(blast)+
  apply(rename_tac Ga f w)(*strict*)
  apply(thin_tac "F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})")
  apply(rename_tac G f w)(*strict*)
  apply(rename_tac G f w)
  apply(erule_tac
      x = "w"
      in allE)
  apply(auto)
  apply(subgoal_tac "None \<in> F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f) w")
   apply(rename_tac G f w)(*strict*)
   apply(blast)
  apply(rename_tac G f w)(*strict*)
  apply(rule_tac
      A = "F_CFG_FIRST__table__fp G f w"
      in set_mp)
   apply(rename_tac G f w)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac G f w)(*strict*)
  apply(rule_tac
      t = "F_CFG_FIRST__table__fp G f w"
      and s = "F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f) w"
      in ssubst)
   apply(rename_tac G f w)(*strict*)
   apply(case_tac "f = F_CFG_FIRST__table__fp_one G f")
    apply(rename_tac G f w)(*strict*)
    apply(clarsimp)
   apply(rename_tac G f w)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x w = F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f) w"
      and t = "F_CFG_FIRST__table__fp G f"
      and s = "(if F_CFG_FIRST__table__fp_one G f = f then f else F_CFG_FIRST__table__fp G (F_CFG_FIRST__table__fp_one G f))"
      in ssubst)
    apply(rename_tac G f w)(*strict*)
    apply(rule F_CFG_FIRST__table__fp.psimps)
    apply(rule F_CFG_FIRST__table__fp_termination)
    apply(blast)
   apply(rename_tac G f w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f w)(*strict*)
  apply(clarsimp)
  done

lemma SOUND1: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> \<forall>w. setB w \<subseteq> cfg_events G \<and> setA w \<subseteq> cfg_nonterminals G \<longrightarrow> F_CFG_FIRST__fp G w \<subseteq> cfgSTD_first_symbol_of_derivable_effect G w"
  apply(rule allI)
  apply(rename_tac w)(*strict*)
  apply(rule_tac
      list = "w"
      in list.induct)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
   apply(rule_tac
      x = "\<lambda>x. if x = 0 then Some (pair None \<lparr>cfg_conf = []\<rparr>) else None"
      in exI)
   apply(simp add: derivation_append_def cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
   apply(fold der1_def)
   apply(rule cfgSTD.der1_is_derivation)
  apply(rename_tac w a list)(*strict*)
  apply(rule impI)+
  apply(erule impE)
   apply(rename_tac w a list)(*strict*)
   apply(rule conjI)
    apply(rename_tac w a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac w a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac w a list aa)(*strict*)
   defer
   apply(rename_tac w a list b)(*strict*)
   apply(clarsimp)
   apply(rename_tac list b)(*strict*)
   apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
   apply(rule_tac
      x = "\<lambda>n. if(n = 0)then Some(pair None \<lparr>cfg_conf = teB b#list\<rparr>) else None"
      in exI)
   apply(rule_tac
      x = "list"
      in exI)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
   apply(clarsimp)
   apply(rename_tac list b i)(*strict*)
   apply(case_tac i)
    apply(rename_tac list b i)(*strict*)
    apply(clarsimp)
   apply(rename_tac list b i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac w a list aa)(*strict*)
  apply(rename_tac X y w A)
  apply(rename_tac X y w A)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac y w A)(*strict*)
  apply(clarify)
  apply(rename_tac y w A x)(*strict*)
  apply(simp del: F_CFG_FIRST__fp.simps)
  apply(rename_tac w A x)(*strict*)
  apply(erule disjE)
   apply(rename_tac w A x)(*strict*)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac w A x y)(*strict*)
   apply(simp del: F_CFG_FIRST__fp.simps)
   apply(subgoal_tac "\<forall>w. (F_CFG_FIRST__fp_one G w) \<subseteq> cfgSTD_first_symbol_of_derivable_effect G w")
    apply(rename_tac w A x y)(*strict*)
    prefer 2
    apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_02_unfold)
    apply(force)
   apply(rename_tac w A x y)(*strict*)
   apply(erule_tac
      x="[teA A]"
      in allE)
   apply(subgoal_tac "option_to_setMap (cfgSTD_first_symbol_of_derivable_effect G [teA A]) \<subseteq> option_to_setMap (cfgSTD_first_symbol_of_derivable_effect G ([teA A] @ w))")
    apply(rename_tac w A x y)(*strict*)
    prefer 2
    apply(rule table_domainContext)
    apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
   apply(rename_tac w A x y)(*strict*)
   apply(rule_tac
      t="[teA A]@w"
      and s="teA A#w"
      in ssubst)
    apply(rename_tac w A x y)(*strict*)
    apply(force)
   apply(rename_tac w A x y)(*strict*)
   apply(simp add: option_to_setMap_def)
   apply(force)
  apply(rename_tac w A x)(*strict*)
  apply(subgoal_tac "x \<in> F_CFG_FIRST__fp G w \<and> None \<in> F_CFG_FIRST__fp_one G [teA A]")
   apply(rename_tac w A x)(*strict*)
   prefer 2
   apply(case_tac "None \<in> F_CFG_FIRST__fp_one G [teA A]")
    apply(rename_tac w A x)(*strict*)
    apply(clarsimp)
   apply(rename_tac w A x)(*strict*)
   apply(clarsimp)
  apply(rename_tac w A x)(*strict*)
  apply(erule conjE)+
  apply(thin_tac "x \<in> (if None \<in> F_CFG_FIRST__fp_one G [teA A] then F_CFG_FIRST__fp G w else {})")
  apply(subgoal_tac "x \<in> cfgSTD_first_symbol_of_derivable_effect G w")
   apply(rename_tac w A x)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac w A x)(*strict*)
  apply(thin_tac "F_CFG_FIRST__fp G w \<subseteq> cfgSTD_first_symbol_of_derivable_effect G w")
  apply(thin_tac "x \<in> F_CFG_FIRST__fp G w")
  apply(subgoal_tac "\<forall>w. (F_CFG_FIRST__fp_one G w) \<subseteq> cfgSTD_first_symbol_of_derivable_effect G w")
   apply(rename_tac w A x)(*strict*)
   prefer 2
   apply(rule F_CFG_FIRST__fp_one_F_CFG_FIRST__table__fp_invariant_02_unfold)
   apply(force)
  apply(rename_tac w A x)(*strict*)
  apply(erule_tac
      x="[teA A]"
      in allE)
  apply(subgoal_tac "None \<in> cfgSTD_first_symbol_of_derivable_effect G [teA A]")
   apply(rename_tac w A x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w A x)(*strict*)
  apply(thin_tac "F_CFG_FIRST__fp_one G [teA A] \<subseteq> cfgSTD_first_symbol_of_derivable_effect G [teA A]")
  apply(thin_tac "None \<in> F_CFG_FIRST__fp_one G [teA A]")
  apply(case_tac x)
   apply(rename_tac w A x)(*strict*)
   prefer 2
   apply(rename_tac w A x a)(*strict*)
   apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
   apply(clarsimp)
   apply(rename_tac w A a d da w')(*strict*)
   apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
    apply(rename_tac w A a d da w')(*strict*)
    apply(subgoal_tac "\<exists>n. maximum_of_domain da n")
     apply(rename_tac w A a d da w')(*strict*)
     apply(erule exE)+
     apply(rename_tac w A a d da w' n na)(*strict*)
     apply(rule_tac
      x = "derivation_append (derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) da n"
      in exI)
     apply(rule_tac
      x = "w'"
      in exI)
     apply(rule_tac
      s = "[teA A] @ w"
      and t = "teA A#w"
      in ssubst)
      apply(rename_tac w A a d da w' n na)(*strict*)
      apply(clarsimp)
     apply(rename_tac w A a d da w' n na)(*strict*)
     apply(rule concatExtendIsFromTo)
         apply(rename_tac w A a d da w' n na)(*strict*)
         apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
        apply(rename_tac w A a d da w' n na)(*strict*)
        apply(blast)+
    apply(rename_tac w A a d da w')(*strict*)
    apply(rule_tac cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac w A a d da w')(*strict*)
   apply(rule_tac cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac w A x)(*strict*)
  apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
  apply(clarsimp)
  apply(rename_tac w A d da)(*strict*)
  apply(subgoal_tac "\<exists>n. maximum_of_domain da n")
   apply(rename_tac w A d da)(*strict*)
   apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
    apply(rename_tac w A d da)(*strict*)
    apply(erule exE)+
    apply(rename_tac w A d da n na)(*strict*)
    apply(rule_tac
      x = "derivation_append (derivation_map da (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) d n"
      in exI)
    apply(rule_tac
      s = "[teA A] @ w"
      and t = "teA A#w"
      in ssubst)
     apply(rename_tac w A d da n na)(*strict*)
     apply(clarsimp)
    apply(rename_tac w A d da n na)(*strict*)
    apply(rule concatExtendIsFromTo)
        apply(rename_tac w A d da n na)(*strict*)
        apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
       apply(rename_tac w A d da n na)(*strict*)
       apply(blast)
      apply(rename_tac w A d da n na)(*strict*)
      apply(blast)+
   apply(rename_tac w A d da)(*strict*)
   apply(rule_tac cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac w A d da)(*strict*)
  apply(rule_tac cfgSTD.to_has_maximum_of_domain)
  apply(rule cfgSTD.from_to_is_to)
  apply(blast)
  done

corollary F_CFG_FIRST__fpSound: "
  F_CFG_FIRST__table__fp_valid_input G (\<lambda>x. {})
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> F_CFG_FIRST__fp G w = cfgSTD_first_symbol_of_derivable_effect G w"
  apply(rule Orderings.order_antisym)
   prefer 2
   apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def del: F_CFG_FIRST__fp.simps)
   apply(rule conjI)
    apply(clarify)
    apply(rename_tac x v d w')(*strict*)
    apply(subgoal_tac "\<forall>n w d w'. setB w \<subseteq> cfg_events G \<and> setA w \<subseteq> cfg_nonterminals G \<and> maximum_of_domain d n \<and> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB v # w'\<rparr>} \<longrightarrow> Some v \<in> F_CFG_FIRST__fp G w")
     apply(rename_tac x v d w')(*strict*)
     prefer 2
     apply(rule soundnessPt2)
      apply(rename_tac x v d w')(*strict*)
      apply(blast)
     apply(rename_tac x v d w')(*strict*)
     apply(blast)
    apply(rename_tac x v d w')(*strict*)
    apply(subgoal_tac "\<exists>m. maximum_of_domain d m")
     apply(rename_tac x v d w')(*strict*)
     apply(erule exE)
     apply(rename_tac x v d w' m)(*strict*)
     apply(erule_tac
      x = "m"
      in allE)
     apply(erule_tac
      x = "w"
      in allE)
     apply(erule_tac
      x = "d"
      in allE)
     apply(erule_tac
      x = "w'"
      in allE)
     apply(erule impE)
      apply(rename_tac x v d w' m)(*strict*)
      apply(rule conjI, clarsimp)
      apply(rule conjI, clarsimp)
      apply(rule conjI, clarsimp)
      apply(blast)
     apply(rename_tac x v d w' m)(*strict*)
     apply(simp add: option_to_setMap_def)
    apply(rename_tac x v d w')(*strict*)
    apply(rule cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   prefer 2
   apply(subgoal_tac "\<forall>w. setB w \<subseteq> cfg_events G \<and> setA w \<subseteq> cfg_nonterminals G \<longrightarrow> F_CFG_FIRST__fp G w \<subseteq> ((cfgSTD_first_symbol_of_derivable_effect G w))")
    prefer 2
    apply(rule SOUND1)
    apply(blast)
   apply(erule_tac
      x = "w"
      in allE)
   apply(erule impE)
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(induct w arbitrary: d)
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w d)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = [a]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = [] ")
   apply(rename_tac a w d)(*strict*)
   prefer 2
   apply(rule derivationCanBeDecomposed)
   apply(clarsimp)
   apply(blast)
  apply(rename_tac a w d)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2)(*strict*)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d1 n")
   apply(rename_tac a w d d1 d2)(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(force)
  apply(rename_tac a w d d1 d2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 n)(*strict*)
  apply(subgoal_tac "n\<noteq>0")
   apply(rename_tac a w d d1 d2 n)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgSTD.modifying_derivation_is_not_empty)
     apply(rename_tac a w d d1 d2 n)(*strict*)
     apply(force)
    apply(rename_tac a w d d1 d2 n)(*strict*)
    apply(force)
   apply(rename_tac a w d d1 d2 n)(*strict*)
   apply(force)
  apply(rename_tac a w d d1 d2 n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac a w d d1 d2 n)(*strict*)
   apply(force)
  apply(rename_tac a w d d1 d2 n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 nat)(*strict*)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d2 n")
   apply(rename_tac a w d d1 d2 nat)(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(force)
  apply(rename_tac a w d d1 d2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 nat n)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w d d1 d2 nat n aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w d d1 d2 nat n aa)(*strict*)
   apply(rule F_CFG_FIRST__fp_one_NoneDeri_NoneElem)
     apply(rename_tac w d d1 d2 nat n aa)(*strict*)
     apply(force)
    apply(rename_tac w d d1 d2 nat n aa)(*strict*)
    apply(force)
   apply(rename_tac w d d1 d2 nat n aa)(*strict*)
   apply(force)
  apply(rename_tac a w d d1 d2 nat n b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w d d1 d2 nat n b)(*strict*)
  apply(subgoal_tac "\<exists>e w. d1 (Suc nat) = Some (pair e \<lparr>cfg_conf = teB b#w\<rparr>)")
   apply(rename_tac w d d1 d2 nat n b)(*strict*)
   apply(subgoal_tac "\<exists>e. d1 (Suc nat) = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
    apply(rename_tac w d d1 d2 nat n b)(*strict*)
    apply(force)
   apply(rename_tac w d d1 d2 nat n b)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac w d d1 d2 nat n b e wa na nb nc x xa xaa)(*strict*)
   apply(subgoal_tac "nb=Suc nat")
    apply(rename_tac w d d1 d2 nat n b e wa na nb nc x xa xaa)(*strict*)
    apply(clarsimp)
   apply(rename_tac w d d1 d2 nat n b e wa na nb nc x xa xaa)(*strict*)
   apply(rule_tac
      d="d1"
      in cfgSTD.maximum_of_domainUnique)
     apply(rename_tac w d d1 d2 nat n b e wa na nb nc x xa xaa)(*strict*)
     apply(force)
    apply(rename_tac w d d1 d2 nat n b e wa na nb nc x xa xaa)(*strict*)
    apply(force)
   apply(rename_tac w d d1 d2 nat n b e wa na nb nc x xa xaa)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac w d d1 d2 nat n b)(*strict*)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d1 n")
   apply(rename_tac w d d1 d2 nat n b)(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(force)
  apply(rename_tac w d d1 d2 nat n b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w d d1 d2 nat n b na)(*strict*)
  apply(subgoal_tac "\<exists>e2. d1 na = Some (pair e2 SSC)" for SSC)
   apply(rename_tac w d d1 d2 nat n b na)(*strict*)
   prefer 2
   apply(rule cfgSTD.toAtMaxDom)
    apply(rename_tac w d d1 d2 nat n b na)(*strict*)
    apply(force)
   apply(rename_tac w d d1 d2 nat n b na)(*strict*)
   apply(force)
  apply(rename_tac w d d1 d2 nat n b na)(*strict*)
  apply(clarsimp)
  apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
  apply(subgoal_tac "d1 0 = Some (pair None SSF)" for SSF)
   apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
   prefer 2
   apply(rule cfgSTD.fromAtZero)
    apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
    apply(force)
   apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
   apply(force)
  apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
  apply(rule_tac
      m="0"
      and n="Suc nat"
      in terminal_at_beginning_are_never_modified)
      apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(force)
     apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
     apply(force)
    apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
    apply(force)
   apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
   apply(force)
  apply(rename_tac w d d1 d2 nat n b na e2)(*strict*)
  apply(force)
  done

lemma F_CFG_FIRST__fpSound0: "
  setA w = {}
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> F_CFG_FIRST__fp G w = cfgSTD_first_symbol_of_derivable_marked_effect G w"
  apply(case_tac w)
   apply(clarsimp)
   apply(rule cfgSTD_first_symbol_of_derivable_marked_effect_Nil)
  apply(rename_tac a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b)(*strict*)
  apply(simp only: cfgSTD_first_symbol_of_derivable_marked_effect_def)
  apply(rule order_antisym)
   apply(rename_tac list b)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="\<lambda>n. if n=0 then Some (pair None \<lparr>cfg_conf = teB b # list\<rparr>) else None"
      in exI)
   apply(rule_tac
      x="list"
      in exI)
   apply(rule conjI)
    apply(rename_tac list b)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
    apply(fold der1_def)
    apply(rule cfgSTD.der1_is_derivation)
   apply(rename_tac list b)(*strict*)
   apply(force)
  apply(rename_tac list b)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac list b)(*strict*)
   apply(clarsimp)
   apply(rename_tac list b v d w')(*strict*)
   apply(rule derivation_from_to_noModOnTerminalStart)
   apply(blast)
  apply(rename_tac list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b d)(*strict*)
  apply(rename_tac d1)
  apply(rename_tac list b d1)(*strict*)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d1 n")
   apply(rename_tac list b d1)(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(force)
  apply(rename_tac list b d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b d1 n)(*strict*)
  apply(subgoal_tac "n\<noteq>0")
   apply(rename_tac list b d1 n)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgSTD.modifying_derivation_is_not_empty)
     apply(rename_tac list b d1 n)(*strict*)
     apply(force)
    apply(rename_tac list b d1 n)(*strict*)
    apply(force)
   apply(rename_tac list b d1 n)(*strict*)
   apply(force)
  apply(rename_tac list b d1 n)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac list b d1 n)(*strict*)
   apply(force)
  apply(rename_tac list b d1 n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b d1 nat)(*strict*)
  apply(subgoal_tac "\<exists>e w. d1 (Suc nat) = Some (pair e \<lparr>cfg_conf = teB b#w\<rparr>)")
   apply(rename_tac list b d1 nat)(*strict*)
   apply(subgoal_tac "\<exists>e. d1 (Suc nat) = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
    apply(rename_tac list b d1 nat)(*strict*)
    apply(force)
   apply(rename_tac list b d1 nat)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac list b d1 nat e w n x)(*strict*)
   apply(subgoal_tac "n=Suc nat")
    apply(rename_tac list b d1 nat e w n x)(*strict*)
    apply(clarsimp)
   apply(rename_tac list b d1 nat e w n x)(*strict*)
   apply(rule_tac
      d="d1"
      in cfgSTD.maximum_of_domainUnique)
     apply(rename_tac list b d1 nat e w n x)(*strict*)
     apply(force)
    apply(rename_tac list b d1 nat e w n x)(*strict*)
    apply(force)
   apply(rename_tac list b d1 nat e w n x)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac list b d1 nat)(*strict*)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d1 n")
   apply(rename_tac list b d1 nat)(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(force)
  apply(rename_tac list b d1 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b d1 nat n)(*strict*)
  apply(subgoal_tac "\<exists>e2. d1 n = Some (pair e2 SSC)" for SSC)
   apply(rename_tac list b d1 nat n)(*strict*)
   prefer 2
   apply(rule cfgSTD.toAtMaxDom)
    apply(rename_tac list b d1 nat n)(*strict*)
    apply(force)
   apply(rename_tac list b d1 nat n)(*strict*)
   apply(force)
  apply(rename_tac list b d1 nat n)(*strict*)
  apply(clarsimp)
  apply(rename_tac list b d1 nat n e2)(*strict*)
  apply(subgoal_tac "d1 0 = Some (pair None SSF)" for SSF)
   apply(rename_tac list b d1 nat n e2)(*strict*)
   prefer 2
   apply(rule cfgSTD.fromAtZero)
    apply(rename_tac list b d1 nat n e2)(*strict*)
    apply(force)
   apply(rename_tac list b d1 nat n e2)(*strict*)
   apply(force)
  apply(rename_tac list b d1 nat n e2)(*strict*)
  apply(rule_tac
      m="0"
      and n="Suc nat"
      in terminal_at_beginning_are_never_modified)
      apply(rename_tac list b d1 nat n e2)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(force)
     apply(rename_tac list b d1 nat n e2)(*strict*)
     apply(force)
    apply(rename_tac list b d1 nat n e2)(*strict*)
    apply(force)
   apply(rename_tac list b d1 nat n e2)(*strict*)
   apply(force)
  apply(rename_tac list b d1 nat n e2)(*strict*)
  apply(force)
  done

lemma FB_first_teA_not_None: "
  setA w \<noteq> {}
  \<Longrightarrow> \<exists>x \<in> setA w. FB_first_teA w = Some x"
  apply(subgoal_tac "\<forall>w. setA w \<noteq> {} \<longrightarrow> (\<exists>x\<in> (setA w). FB_first_teA w=Some x)")
   apply(force)
  apply(rule allI)
  apply(rename_tac wa)(*strict*)
  apply(thin_tac "setA w \<noteq> {}")
  apply(rename_tac w)(*strict*)
  apply(induct_tac w)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
  apply(rename_tac w a list)(*strict*)
  apply(rule impI)
  apply(case_tac "setA list={}")
   apply(rename_tac w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(case_tac a)
    apply(rename_tac a list aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a list b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w a list)(*strict*)
  apply(erule impE)
   apply(rename_tac w a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac w a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac w a list aa)(*strict*)
   apply(rule_tac
      x="aa"
      in bexI)
    apply(rename_tac w a list aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac w a list aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac w a list b)(*strict*)
  apply(auto)
  done

corollary F_CFG_FIRST__fpF_CFG_EBSound: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> F_CFG_FIRST__input_valid G' w = cfgSTD_first_symbol_of_derivable_marked_effect G w"
  apply(subgoal_tac "cfg_every_nonterminal_on_some_left_hand_side G'")
   prefer 2
   apply(rule F_CFG_EBMakescfg_every_nonterminal_on_some_left_hand_side)
    apply(blast,blast)
  apply(simp only: F_CFG_FIRST__input_valid_def)
  apply(case_tac "setA w \<subseteq> cfg_nonterminals G'")
   apply(subgoal_tac "F_CFG_FIRST__fp G' w = cfgSTD_first_symbol_of_derivable_marked_effect G w")
    apply(clarsimp)
   apply(rule_tac
      s="cfgSTD_first_symbol_of_derivable_marked_effect G' w"
      and t="cfgSTD_first_symbol_of_derivable_marked_effect G w"
      in ssubst)
    apply(rule F_CFG_EBSound0)
       apply(blast)+
   apply(rule_tac
      s="cfgSTD_first_symbol_of_derivable_effect G' w"
      and t="cfgSTD_first_symbol_of_derivable_marked_effect G' w"
      in ssubst)
    apply(rule sym)
    apply(rule F_CFG_EBSound1)
       apply(rule F_CFG_EBSound3)
        apply(blast)+
      apply(rule_tac
      s="cfgSTD_Nonblockingness_nonterminals G"
      and t="cfgSTD_Nonblockingness_nonterminals G'"
      in ssubst)
       defer
       apply(rule F_CFG_EBSoundA)
        apply(blast)+
     apply(rule_tac
      s="cfg_events G"
      and t="cfg_events G'"
      in ssubst)
      apply(rule sym)
      apply(rule F_CFG_EBSound4)
       apply(blast)+
    apply(rule F_CFG_FIRST__fpSound)
      apply(simp add: F_CFG_FIRST__table__fp_valid_input_def)
      apply(rule conjI)
       apply(rule F_CFG_EBSound3)
        apply(blast)
       apply(blast)
      apply(simp add: maps_to_cfg_events_def)
      apply(simp add: option_to_setMap_def)
      apply(simp add: maps_only_from_table_domain_def)
      apply(simp add: cfg_has_production_def)
      apply(clarsimp)
      apply(simp add: F_CFG_EB_def)
      apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
       apply(clarsimp)
       apply(subgoal_tac "\<exists>x. prod_lhs x = cfg_initial G \<and> x \<in> cfg_productions G \<and> setA (prod_rhs x) \<subseteq> F_CFG_EB__fp G {}")
        apply(clarsimp)
       apply(rule F_CFG_EBSound5)
        apply(blast)+
      apply(clarsimp)
     apply(blast)
    apply(rule_tac
      s="cfg_events G"
      and t="cfg_events G'"
      in ssubst)
     apply(rule sym)
     apply(rule F_CFG_EBSound4)
      apply(blast)
     apply(blast)
    apply(blast)
   apply(subgoal_tac "{}=cfgSTD_first_symbol_of_derivable_marked_effect G w")
    apply(clarsimp)
   apply(simp add: cfgSTD_first_symbol_of_derivable_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "setA w \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "cfgSTD_Nonblockingness_nonterminals G = cfg_nonterminals G'")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule F_CFG_EBSoundA)
     apply(rename_tac x)(*strict*)
     apply(blast)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(rule canElimCombine2)
      apply(rename_tac x)(*strict*)
      apply(blast)
     apply(rename_tac x)(*strict*)
     apply(blast)
    apply(rename_tac x)(*strict*)
    apply(blast)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rule order_antisym)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
   apply(clarsimp)
   apply(rename_tac x d w')(*strict*)
   apply(rule conjI)
    apply(rename_tac x d w')(*strict*)
    apply(subgoal_tac "cfg_nonterminals G' \<subseteq> cfg_nonterminals G")
     apply(rename_tac x d w')(*strict*)
     apply(force)
    apply(rename_tac x d w')(*strict*)
    apply(rule_tac
      t="cfg_nonterminals G'"
      and s="F_CFG_EB__fp G {}"
      in ssubst)
     apply(rename_tac x d w')(*strict*)
     apply(simp add: F_CFG_EB_def)
     apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
      apply(rename_tac x d w')(*strict*)
      apply(force)
     apply(rename_tac x d w')(*strict*)
     apply(force)
    apply(rename_tac x d w')(*strict*)
    apply(rule F_CFG_EB_F_CFG_EB__fp_invariant_02_unfold)
    apply(simp add: F_CFG_EB__fp_valid_input_def)
   apply(rename_tac x d w')(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule_tac
      x="w'"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d w')(*strict*)
    apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
     apply(rename_tac x d w')(*strict*)
     apply(erule exE)
     apply(rename_tac x d w' n)(*strict*)
     apply(rule_tac
      ?G1.0="G'"
      in cfg_subInheritsDerivation)
       apply(rename_tac x d w' n)(*strict*)
       apply(rule F_CFG_EB_makes_cfg_sub)
        apply(rename_tac x d w' n)(*strict*)
        apply(blast)
       apply(rename_tac x d w' n)(*strict*)
       apply(blast)
      apply(rename_tac x d w' n)(*strict*)
      apply(blast)
     apply(rename_tac x d w' n)(*strict*)
     apply(blast)
    apply(rename_tac x d w')(*strict*)
    apply(rule cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac x d w')(*strict*)
   apply(blast)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d w')(*strict*)
  apply(rule conjI)
   apply(rename_tac x d w')(*strict*)
   apply(rule_tac
      t="cfg_nonterminals G'"
      and s="cfgSTD_Nonblockingness_nonterminals G"
      in ssubst)
    apply(rename_tac x d w')(*strict*)
    apply(rule sym)
    apply(rule F_CFG_EBSoundA)
     apply(rename_tac x d w')(*strict*)
     apply(blast)+
   apply(rename_tac x d w')(*strict*)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
   apply(blast)
  apply(rename_tac x d w')(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule_tac
      x="w'"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   apply(rename_tac x d w')(*strict*)
   apply(erule exE)
   apply(rename_tac x d w' n)(*strict*)
   apply(rule canMimik)
        apply(rename_tac x d w' n)(*strict*)
        apply(blast)+
      apply(rename_tac x d w' n)(*strict*)
      defer
      apply(simp add: setB_def)
     apply(rename_tac x d w' n)(*strict*)
     apply(clarsimp)
    apply(rename_tac x d w' n)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d w')(*strict*)
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac x d w' n)(*strict*)
  apply(simp (no_asm) add: setA_def)
  apply(rule_tac
      t="cfg_nonterminals G'"
      and s="cfgSTD_Nonblockingness_nonterminals G"
      in ssubst)
   apply(rename_tac x d w' n)(*strict*)
   apply(rule sym)
   apply(rule F_CFG_EBSoundA)
    apply(rename_tac x d w' n)(*strict*)
    apply(blast)+
  apply(rename_tac x d w' n)(*strict*)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(blast)
  done

corollary F_CFG_FIRST__enforce_NonblockingnessSound: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> F_CFG_FIRST__enforce_Nonblockingness G w = cfgSTD_first_symbol_of_derivable_marked_effect G w"
  apply(case_tac "setA w={}")
   apply(subgoal_tac "F_CFG_FIRST__fp G w = cfgSTD_first_symbol_of_derivable_marked_effect G w")
    apply(simp add: F_CFG_FIRST__enforce_Nonblockingness_def)
   apply(rule F_CFG_FIRST__fpSound0)
    apply(blast,blast)
  apply(subgoal_tac "\<exists>A\<in> (setA w). FB_first_teA w=Some A")
   prefer 2
   apply(rule FB_first_teA_not_None)
   apply(blast)
  apply(erule bexE)
  apply(rename_tac A)(*strict*)
  apply(case_tac "F_CFG_EB (G(|cfg_initial:=A|))")
   apply(rename_tac A)(*strict*)
   apply(subgoal_tac "{} = cfgSTD_first_symbol_of_derivable_marked_effect G w")
    apply(rename_tac A)(*strict*)
    apply(simp add: F_CFG_FIRST__enforce_Nonblockingness_def)
   apply(rename_tac A)(*strict*)
   apply(rule canNotElimWordWithNotEliminableNonterminal)
       apply(rename_tac A)(*strict*)
       apply(blast)
      apply(rename_tac A)(*strict*)
      apply(blast)
     apply(rename_tac A)(*strict*)
     apply(blast)
    apply(rename_tac A)(*strict*)
    apply(blast)
   apply(rename_tac A)(*strict*)
   apply(blast)
  apply(rename_tac A a)(*strict*)
  apply(rename_tac G')
  apply(rename_tac A G')(*strict*)
  apply(rule_tac
      t="cfgSTD_first_symbol_of_derivable_marked_effect G w"
      and s="cfgSTD_first_symbol_of_derivable_marked_effect (G\<lparr>cfg_initial := A\<rparr>) w"
      in ssubst)
   apply(rename_tac A G')(*strict*)
   prefer 2
   apply(subgoal_tac "F_CFG_FIRST__input_valid G' w = cfgSTD_first_symbol_of_derivable_marked_effect (G\<lparr>cfg_initial := A\<rparr>) w")
    apply(rename_tac A G')(*strict*)
    prefer 2
    apply(rule F_CFG_FIRST__fpF_CFG_EBSound)
       apply(rename_tac A G')(*strict*)
       apply(simp add: valid_cfg_def)
       apply(blast)
      apply(rename_tac A G')(*strict*)
      apply(force)
     apply(rename_tac A G')(*strict*)
     apply(force)
    apply(rename_tac A G')(*strict*)
    apply(force)
   apply(rename_tac A G')(*strict*)
   apply(simp add: F_CFG_FIRST__enforce_Nonblockingness_def)
  apply(rename_tac A G')(*strict*)
  apply(rule cfgSTD_first_symbol_of_derivable_marked_effect_independent_from_Initial)
     apply(rename_tac A G')(*strict*)
     apply(blast)+
  done

lemma cfgSTD_first_to_F_CFG_FIRST_1: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD_first G (Suc 0) w = F_CFG_FIRST G (Suc 0) w"
  apply(rule_tac
      t="F_CFG_FIRST G (Suc 0) w"
      and s="(\<lambda>x. case x of None \<Rightarrow> [] | Some a \<Rightarrow> [a]) ` (F_CFG_FIRST__enforce_Nonblockingness G w)"
      in ssubst)
   apply(simp add: F_CFG_FIRST_def)
  apply(rule_tac
      t="F_CFG_FIRST__enforce_Nonblockingness G w"
      and s="cfgSTD_first_symbol_of_derivable_marked_effect G w"
      in ssubst)
   apply(rule F_CFG_FIRST__enforce_NonblockingnessSound)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: cfgSTD_first_def cfgSTD_first_symbol_of_derivable_marked_effect_def)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(rule inMap)
   apply(case_tac xa)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e1 n)(*strict*)
    apply(rule_tac
      x="None"
      in bexI)
     apply(rename_tac d e1 n)(*strict*)
     apply(clarsimp)
    apply(rename_tac d e1 n)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="d"
      in exI)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(rule_tac
      x="n"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "maximum_of_domain d n")
     apply(rename_tac d e1 n)(*strict*)
     prefer 2
     apply(rule CFG_nonterm_free_conf_at_maximum_of_domain)
        apply(rename_tac d e1 n)(*strict*)
        apply(force)
       apply(rename_tac d e1 n)(*strict*)
       apply(force)
      apply(rename_tac d e1 n)(*strict*)
      apply(force)
     apply(rename_tac d e1 n)(*strict*)
     apply(force)
    apply(rename_tac d e1 n)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac xa d e1 n a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e1 n a list)(*strict*)
   apply(rule_tac
      x="Some a"
      in bexI)
    apply(rename_tac d e1 n a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e1 n a list)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d e1 n a list)(*strict*)
    apply(rule_tac
      A="setB ([teB a] @ liftB list)"
      in set_mp)
     apply(rename_tac d e1 n a list)(*strict*)
     apply(rule_tac
      w="w"
      and w'="[teB a] @ liftB list"
      and i="0"
      and j="n"
      in staysInSigma2)
          apply(rename_tac d e1 n a list)(*strict*)
          apply(force)
         apply(rename_tac d e1 n a list)(*strict*)
         apply(force)
        apply(rename_tac d e1 n a list)(*strict*)
        apply(force)
       apply(rename_tac d e1 n a list)(*strict*)
       apply(force)
      apply(rename_tac d e1 n a list)(*strict*)
      apply(force)
     apply(rename_tac d e1 n a list)(*strict*)
     apply(force)
    apply(rename_tac d e1 n a list)(*strict*)
    apply(force)
   apply(rename_tac d e1 n a list)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule_tac
      x="liftB list"
      in exI)
   apply(rule conjI)
    apply(rename_tac d e1 n a list)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(rule_tac
      x="n"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "maximum_of_domain d n")
     apply(rename_tac d e1 n a list)(*strict*)
     prefer 2
     apply(rule CFG_nonterm_free_conf_at_maximum_of_domain)
        apply(rename_tac d e1 n a list)(*strict*)
        apply(force)
       apply(rename_tac d e1 n a list)(*strict*)
       apply(force)
      apply(rename_tac d e1 n a list)(*strict*)
      apply(force)
     apply(rename_tac d e1 n a list)(*strict*)
     apply(clarsimp)
     apply(rule setA_liftB_empty)
    apply(rename_tac d e1 n a list)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d e1 n a list)(*strict*)
   apply(rule setA_liftB_empty)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(rule inMap)
   apply(rule_tac
      x="[]"
      in bexI)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule conjI)
    apply(rename_tac d)(*strict*)
    apply(rule cfgSTD.from_to_is_der)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac d n x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d n x)(*strict*)
    apply(rule CFG_nonterm_free_conf_at_maximum_of_domain)
       apply(rename_tac d n x)(*strict*)
       apply(force)
      apply(rename_tac d n x)(*strict*)
      apply(force)
     apply(rename_tac d n x)(*strict*)
     apply(force)
    apply(rename_tac d n x)(*strict*)
    apply(force)
   apply(rename_tac d n x)(*strict*)
   apply(subgoal_tac "maximum_of_domain d n")
    apply(rename_tac d n x)(*strict*)
    prefer 2
    apply(rule CFG_nonterm_free_conf_at_maximum_of_domain)
       apply(rename_tac d n x)(*strict*)
       apply(force)
      apply(rename_tac d n x)(*strict*)
      apply(force)
     apply(rename_tac d n x)(*strict*)
     apply(force)
    apply(rename_tac d n x)(*strict*)
    apply(force)
   apply(rename_tac d n x)(*strict*)
   apply(rule cfgSTD.fromAtZero)
    apply(rename_tac d n x)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(force)
   apply(rename_tac d n x)(*strict*)
   apply(force)
  apply(rename_tac xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a d w')(*strict*)
  apply(rule inMap)
  apply(rule_tac
      x="[a]@filterB w'"
      in bexI)
   apply(rename_tac a d w')(*strict*)
   apply(clarsimp)
  apply(rename_tac a d w')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
   apply(rename_tac a d w')(*strict*)
   apply(rule cfgSTD.from_to_is_der)
   apply(force)
  apply(rename_tac a d w')(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac a d w' n x)(*strict*)
  apply(rule_tac
      x="x"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac a d w' n x)(*strict*)
   apply(rule CFG_nonterm_free_conf_at_maximum_of_domain)
      apply(rename_tac a d w' n x)(*strict*)
      apply(force)
     apply(rename_tac a d w' n x)(*strict*)
     apply(force)
    apply(rename_tac a d w' n x)(*strict*)
    apply(force)
   apply(rename_tac a d w' n x)(*strict*)
   apply(force)
  apply(rename_tac a d w' n x)(*strict*)
  apply(subgoal_tac "maximum_of_domain d n")
   apply(rename_tac a d w' n x)(*strict*)
   prefer 2
   apply(rule CFG_nonterm_free_conf_at_maximum_of_domain)
      apply(rename_tac a d w' n x)(*strict*)
      apply(force)
     apply(rename_tac a d w' n x)(*strict*)
     apply(force)
    apply(rename_tac a d w' n x)(*strict*)
    apply(force)
   apply(rename_tac a d w' n x)(*strict*)
   apply(force)
  apply(rename_tac a d w' n x)(*strict*)
  apply(rule conjI)
   apply(rename_tac a d w' n x)(*strict*)
   apply(rule cfgSTD.fromAtZero)
    apply(rename_tac a d w' n x)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(force)
   apply(rename_tac a d w' n x)(*strict*)
   apply(force)
  apply(rename_tac a d w' n x)(*strict*)
  apply(rule sym)
  apply(rule liftBDeConv2)
  apply(force)
  done

lemma cfgSTD_first_to_F_CFG_FIRST_0: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD_first G 0 w = F_CFG_FIRST G 0 w"
  apply(rule_tac
      t="F_CFG_FIRST G 0 w"
      and s="(if F_CFG_FIRST__enforce_Nonblockingness G w\<noteq>{} then {[]} else {})"
      in ssubst)
   apply(simp add: F_CFG_FIRST_def)
  apply(rule_tac
      t="F_CFG_FIRST__enforce_Nonblockingness G w"
      and s="cfgSTD_first_symbol_of_derivable_marked_effect G w"
      in ssubst)
   apply(rule F_CFG_FIRST__enforce_NonblockingnessSound)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: cfgSTD_first_def cfgSTD_first_symbol_of_derivable_marked_effect_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac v d w')(*strict*)
   apply(rule order_antisym)
    apply(rename_tac v d w')(*strict*)
    apply(clarsimp)
   apply(rename_tac v d w')(*strict*)
   apply(clarsimp)
   apply(rule inMap)
   apply(clarsimp)
   apply(rule_tac
      x="filterB (teB v # w')"
      in exI)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac v d w')(*strict*)
    apply(rule cfgSTD.from_to_is_der)
    apply(force)
   apply(rename_tac v d w')(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac v d w' n x)(*strict*)
   apply(subgoal_tac "maximum_of_domain d n")
    apply(rename_tac v d w' n x)(*strict*)
    prefer 2
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac v d w' n x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(rename_tac v d w' n x)(*strict*)
    apply(clarsimp)
   apply(rename_tac v d w' n x a)(*strict*)
   apply(clarsimp)
   apply(rename_tac v d w' n x)(*strict*)
   apply(rule sym)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(clarsimp)
   apply(rule inMap)
   apply(clarsimp)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac d)(*strict*)
    apply(rule cfgSTD.from_to_is_der)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac d n x)(*strict*)
   apply(subgoal_tac "maximum_of_domain d n")
    apply(rename_tac d n x)(*strict*)
    prefer 2
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d n x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(rename_tac d n x)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n x a)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x d e1 n)(*strict*)
  apply(case_tac x)
   apply(rename_tac x d e1 n)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e1 n)(*strict*)
   apply(erule_tac
      x="d"
      in allE)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(subgoal_tac "maximum_of_domain d n")
    apply(rename_tac d e1 n)(*strict*)
    prefer 2
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d e1 n)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac d e1 n)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e1 n y)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d e1 n)(*strict*)
   apply(erule_tac
      x="pair e1 \<lparr>cfg_conf = []\<rparr>"
      in allE)
   apply(clarsimp)
  apply(rename_tac x d e1 n a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 n a list)(*strict*)
  apply(erule_tac
      x="a"
      in allE)
  apply(erule impE)
   apply(rename_tac d e1 n a list)(*strict*)
   apply(rule_tac
      A="setB (teB a # liftB list)"
      in set_mp)
    apply(rename_tac d e1 n a list)(*strict*)
    apply(rule_tac
      d="d"
      and w'="teB a # liftB list"
      and w="w"
      and i="0"
      and j="n"
      in staysInSigma2)
         apply(rename_tac d e1 n a list)(*strict*)
         apply(blast)
        apply(rename_tac d e1 n a list)(*strict*)
        apply(force)
       apply(rename_tac d e1 n a list)(*strict*)
       apply(force)
      apply(rename_tac d e1 n a list)(*strict*)
      apply(force)
     apply(rename_tac d e1 n a list)(*strict*)
     apply(force)
    apply(rename_tac d e1 n a list)(*strict*)
    apply(force)
   apply(rename_tac d e1 n a list)(*strict*)
   apply(force)
  apply(rename_tac d e1 n a list)(*strict*)
  apply(erule_tac
      x="d"
      and P="\<lambda>d. \<forall>w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = teB a # w'\<rparr>} \<longrightarrow> setA w' \<noteq> {}"
      in allE)
  apply(rename_tac d e1 n a list)(*strict*)
  apply(erule_tac
      x="liftB list"
      in allE)
  apply(erule impE)
   apply(rename_tac d e1 n a list)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac d e1 n a list)(*strict*)
  apply(subgoal_tac "setA (liftB list)={}")
   apply(rename_tac d e1 n a list)(*strict*)
   apply(force)
  apply(rename_tac d e1 n a list)(*strict*)
  apply(rule setA_liftB)
  done

theorem F_CFG_FIRST__SOUND: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> k \<le> 1
  \<Longrightarrow> cfgSTD_first G k w = F_CFG_FIRST G k w"
  apply(case_tac k)
   apply(clarsimp)
   apply(rule cfgSTD_first_to_F_CFG_FIRST_0)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rule cfgSTD_first_to_F_CFG_FIRST_1)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac nat nata)(*strict*)
  apply(force)
  done

definition F_CFG_FIRST__SpecInput :: "
  ('nonterminal, 'event) cfg
    \<times> ('nonterminal, 'event) DT_two_elements list
    \<times> nat
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__SpecInput X \<equiv>
  case X of 
  (G, w, k) \<Rightarrow>
    valid_cfg G
    \<and> setA w \<subseteq> cfg_nonterminals G
    \<and> setB w \<subseteq> cfg_events G
    \<and> k \<le> 1"

definition F_CFG_FIRST__SpecOutput :: "
  (('nonterminal, 'event) cfg
    \<times> ('nonterminal, 'event) DT_two_elements list
    \<times> nat)
  \<Rightarrow> 'event list set
  \<Rightarrow> bool"
  where
    "F_CFG_FIRST__SpecOutput X R \<equiv>
  case X of 
  (G, w, k) \<Rightarrow>
    cfgSTD_first G k w = F_CFG_FIRST G k w"

theorem F_CFG_FIRST__SOUND2: "
  F_CFG_FIRST__SpecInput (G,w,k)
  \<Longrightarrow> F_CFG_FIRST__SpecOutput (G,w,k) (F_CFG_FIRST G k w)"
  apply(simp add: F_CFG_FIRST__SpecInput_def F_CFG_FIRST__SpecOutput_def)
  apply(rule F_CFG_FIRST__SOUND)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

end
