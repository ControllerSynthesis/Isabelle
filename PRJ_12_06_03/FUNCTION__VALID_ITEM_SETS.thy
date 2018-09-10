section {*FUNCTION\_\_VALID\_ITEM\_SETS*}
theory
  FUNCTION__VALID_ITEM_SETS

imports
  PRJ_12_06_03__ENTRY

begin

definition cfgSTD_first_compatible :: "
  ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "cfgSTD_first_compatible F k \<equiv>
  \<forall>G w k'.
  k' \<le> k
  \<longrightarrow> valid_cfg G
  \<longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<longrightarrow> setB w \<subseteq> cfg_events G
  \<longrightarrow> F G k' w = cfgSTD_first G k' w"

fun valid_item_set__recursive :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "valid_item_set__recursive G F k w =
  (case w of
    [] \<Rightarrow> F_VALID_ITEM_SET_INITIAL G F k
    | y # w' \<Rightarrow> F_VALID_ITEM_SET_GOTO G F k (last w) (valid_item_set__recursive G F k (butlast w)))"

definition viable_prefix :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> bool"
  where
    "viable_prefix G \<gamma> \<equiv>
  \<exists>d n \<alpha> \<beta> y A \<delta> e1 e2.
    cfgRM.derivation G d
    \<and> maximum_of_domain d (Suc n)
    \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>)
    \<and> d n = Some (pair e1 \<lparr>cfg_conf = \<delta> @ [teA A] @ y\<rparr>)
    \<and> d (Suc n) = Some (pair (Some e2) \<lparr>cfg_conf = \<delta> @ \<alpha> @ \<beta> @ y\<rparr>)
    \<and> \<gamma> = \<delta> @ \<alpha>
    \<and> setA y = {}"

definition viable_prefix_ALT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> bool"
  where
    "viable_prefix_ALT G \<gamma> \<equiv>
  \<exists>d n \<alpha> \<beta> y A \<delta> e e'.
    cfgRM.derivation_initial G d
    \<and> d n = Some (pair e \<lparr>cfg_conf = \<delta> @ [teA A] @ liftB y\<rparr>)
    \<and> d (Suc n) = Some (pair e' \<lparr>cfg_conf = \<delta> @ \<alpha> @ \<beta> @ liftB y\<rparr>)
    \<and> \<gamma> = \<delta> @ \<alpha>"

lemma viable_prefix_vs_viable_prefix_ALT: "
  valid_cfg G
  \<Longrightarrow> viable_prefix G \<gamma> = viable_prefix_ALT G \<gamma>"
  apply(simp add: viable_prefix_def viable_prefix_ALT_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rule_tac x="d" in exI)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule conjI)
    apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
   apply(rule_tac x="n" in exI)
   apply(clarsimp)
   apply(rule_tac x="\<alpha>" in exI)
   apply(rule_tac x="\<beta>" in exI)
   apply(rule_tac x="filterB y" in exI)
   apply(rule_tac x="A" in exI)
   apply(rule_tac x="\<delta>" in exI)
   apply(clarsimp)
   apply (metis liftBDeConv2)
  apply(clarsimp)
  apply(rule_tac x="derivation_take d (Suc n)" in exI)
  apply(simp add: cfgRM.derivation_initial_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule cfgRM.derivation_take_preserves_derivation)
   apply(force)
  apply(rule_tac x="n" in exI)
  apply(rule conjI)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rule conjI)
   apply(simp add: derivation_take_def)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(clarsimp)
   apply(case_tac a)
   apply(clarsimp)
   apply(simp add: cfg_initial_configurations_def)
  apply(rule_tac x="\<alpha>" in exI)
  apply(rule_tac x="\<beta>" in exI)
  apply(rule_tac x="liftB y" in exI)
  apply(rule_tac x="A" in exI)
  apply(rule_tac x="\<delta>" in exI)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="Suc n" and
      m="Suc n"
      in cfgRM.pre_some_position_is_some_position_prime)
      apply(blast)
     apply(blast)
    apply(force)
   apply(clarsimp)
  apply(clarsimp)
  apply (metis setA_liftB_empty)
  done

definition complete_viable_prefix :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> bool"
  where
    "complete_viable_prefix G \<gamma> \<equiv>
  \<exists>d n \<alpha> \<beta> y A \<delta> e1 e2.
    cfgRM.derivation G d
    \<and> maximum_of_domain d (Suc n)
    \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>)
    \<and> d n = Some (pair e1 \<lparr>cfg_conf = \<delta> @ [teA A] @ y\<rparr>)
    \<and> d (Suc n) = Some (pair (Some e2) \<lparr>cfg_conf = \<delta> @ \<alpha> @ \<beta> @ y\<rparr>)
    \<and> \<gamma> = \<delta> @ \<alpha>
    \<and> setA y = {}
    \<and> \<beta> = []"

definition valid_item :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item
  \<Rightarrow> bool"
  where
    "valid_item G k I \<equiv>
  length (cfg_item_look_ahead I) \<le> k
  \<and> set (cfg_item_look_ahead I) \<subseteq> cfg_events G
  \<and> (\<exists>p \<in> cfg_productions G.
      prod_lhs p = cfg_item_lhs I
      \<and> prod_rhs p = cfg_item_rhs1 I @ cfg_item_rhs2 I)"

definition F_VALID_ITEM_SET_GOTO__descent__fp_valid_input :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> bool"
  where
    "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S \<equiv>
  valid_cfg G
  \<and> (\<forall>I \<in> S. valid_item G k I)
  \<and> cfgSTD_first_compatible F k"

definition essential_items :: "
  ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "essential_items X \<equiv>
  {I \<in> X. \<exists>A \<alpha> \<beta> y.
    I = \<lparr>cfg_item_lhs = A,
        cfg_item_rhs1 = \<alpha>,
        cfg_item_rhs2 = \<beta>,
        cfg_item_look_ahead = y\<rparr>
  \<and> length \<alpha> > 0}"

definition valid_item_set_n :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "valid_item_set_n G k n \<gamma> \<equiv>
  {I. \<exists>A \<alpha> \<beta> y.
    I = \<lparr>cfg_item_lhs = A,
        cfg_item_rhs1 = \<alpha>,
        cfg_item_rhs2 = \<beta>,
        cfg_item_look_ahead = y\<rparr>
  \<and> (\<exists>d \<delta> e1 e2 z.
        cfgRM.derivation G d
        \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>)
        \<and> d n = Some (pair e1 \<lparr>cfg_conf = \<delta> @ [teA A] @ z\<rparr>)
        \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf = \<delta> @ \<alpha> @ \<beta> @ z\<rparr>)
        \<and> take k z = liftB y
        \<and> \<gamma> = \<delta> @ \<alpha>
        \<and> maximum_of_domain d (Suc n)
        \<and> setA z = {})}"

definition valid_item_set :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "valid_item_set G k \<gamma> \<equiv>
  {I. \<exists>n. I \<in> valid_item_set_n G k n \<gamma>}"

definition valid_item_set_ALT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set"
  where
    "valid_item_set_ALT G k \<gamma> \<equiv>
  {I. \<exists>A \<alpha> \<beta> z.
    I = \<lparr>cfg_item_lhs = A,
        cfg_item_rhs1 = \<alpha>,
        cfg_item_rhs2 = \<beta>,
        cfg_item_look_ahead = z\<rparr>
  \<and> (\<exists>d n \<delta> e1 e2 y.
        cfgRM.derivation_initial G d
        \<and> d n = Some (pair e1 \<lparr>cfg_conf = \<delta> @ [teA A] @ liftB y\<rparr>)
        \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf = \<delta> @ \<alpha> @ \<beta> @ liftB y\<rparr>)
        \<and> take k y = z
        \<and> \<gamma> = \<delta> @ \<alpha>)}"

lemma valid_item_set_vs_valid_item_set_ALT: "
  valid_cfg G
  \<Longrightarrow> valid_item_set G k \<gamma> = valid_item_set_ALT G k \<gamma>"
  apply(simp add: valid_item_set_def valid_item_set_ALT_def valid_item_set_n_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rule_tac x="d" in exI)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule conjI)
    apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
   apply(rule_tac x="n" in exI)
   apply(clarsimp)
   apply(rule_tac x="filterB z" in exI)
   apply(rule context_conjI)
    apply (metis liftBDeConv2)
   apply (metis take_liftB_co)
  apply(clarsimp)
  apply(rule_tac x="n" in exI)
  apply(rule_tac x="derivation_take d (Suc n)" in exI)
  apply(rule conjI)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(clarsimp)
   apply(rule cfgRM.derivation_take_preserves_derivation)
   apply(force)
  apply(rule conjI)
   apply(simp add: derivation_take_def)
   apply(case_tac "d 0")
    apply(clarsimp)
    apply(simp add: cfgRM.derivation_initial_def)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(case_tac a)
   apply(clarsimp)
   apply(simp add: cfg_initial_configurations_def)
  apply(rule_tac x="e1" in exI)
  apply(rule_tac x="e2" in exI)
  apply(rule_tac x="liftB y" in exI)
  apply(rule conjI)
   apply(simp add: derivation_take_def)
  apply(rule conjI)
   apply(simp add: derivation_take_def)
  apply(rule conjI)
   apply (metis take_liftB)
  apply(rule conjI)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply (metis setA_liftB_empty)
  done

definition F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_01 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> bool"
  where
    "F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_01 G F k N \<equiv>
  \<forall>J \<in> N. \<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k J.
    I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N"

definition F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> bool"
  where
    "F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02 G k N \<equiv>
  Ball N (valid_item G k)"

definition F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_first_function
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) DT_cfg_item set
  \<Rightarrow> bool"
  where
    "F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<equiv>
  F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_01 G F k N
  \<and> F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02 G k N
  \<and> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N"

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1__with_cfgSTD_first_compatible: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_item G k I
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k I = F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G cfgSTD_first k I"
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def cfgSTD_first_compatible_def)
  apply(erule_tac x="G" in allE)
  apply(clarsimp)
  apply(rule antisym)
   apply(clarsimp)
   apply(simp add: valid_cfg_def valid_item_def simpY)
   apply(clarsimp)
   apply(erule_tac x="p" in ballE)
    prefer 2
    apply(force)
   apply(erule_tac x="(\<beta> @ liftB (cfg_item_look_ahead I))" in allE)
   apply(simp add: valid_cfg_def valid_item_def simpY)
  apply(clarsimp)
  apply(simp add: valid_cfg_def valid_item_def simpY)
  apply(clarsimp)
  apply(erule_tac x="p" in ballE)
   prefer 2
   apply(force)
  apply(erule_tac x="(\<beta> @ liftB (cfg_item_look_ahead I))" in allE)
  apply(simp add: valid_cfg_def valid_item_def simpY)
  done

lemma in_cfgSTD_first__implies__in_cfgSTD_first: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> x \<in> cfgSTD_first G k w
  \<Longrightarrow> x \<in> F G k w"
  apply(simp add: cfgSTD_first_compatible_def)
  done

lemma in_F__implies__in_cfgSTD_first: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> x \<in> F G k w
  \<Longrightarrow> x \<in> cfgSTD_first G k w"
  apply(simp add: cfgSTD_first_compatible_def)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1_adds_valid_item: "
  valid_cfg G
  \<Longrightarrow> x \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k xa
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_item G k xa
  \<Longrightarrow> valid_item G k x"
  apply(subgoal_tac "x \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G (cfgSTD_first) k xa")
   prefer 2
   apply(metis F_VALID_ITEM_SET_GOTO__descent__fp_one_1__with_cfgSTD_first_compatible)
  apply(thin_tac "cfgSTD_first_compatible F k")
  apply(thin_tac "x \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k xa")
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def cfgSTD_first_compatible_def)
  apply(erule disjE)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac B w z \<beta>)(*strict*)
  apply(simp add: valid_item_def)
  apply(clarsimp)
  apply(rename_tac B w z \<beta> p)(*strict*)
  apply(case_tac p)
  apply(rename_tac B w z \<beta> p prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac B w z \<beta>)(*strict*)
  apply(case_tac xa)
  apply(rename_tac B w z \<beta> cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
  apply(clarsimp)
  apply(rename_tac B w z \<beta> cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead)(*strict*)
  apply(rename_tac A w1 y)
  apply(rename_tac B w z \<beta> A w1 y)(*strict*)
  apply(rule conjI)
   apply(rename_tac B w z \<beta> A w1 y)(*strict*)
   apply(rule cfgSTD_firstk_shorter_than_k)
   apply(blast)
  apply(rename_tac B w z \<beta> A w1 y)(*strict*)
  apply(rule conjI)
   apply(rename_tac B w z \<beta> A w1 y)(*strict*)
   apply(rule_tac
      k="k"
      and v="(\<beta> @ liftB y)"
      in cfgSTD_firstk_in_cfg_events)
      apply(rename_tac B w z \<beta> A w1 y)(*strict*)
      apply(blast)
     apply(rename_tac B w z \<beta> A w1 y)(*strict*)
     apply(simp (no_asm) only: setAConcat concat_asso)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac B w z \<beta> A w1 y)(*strict*)
      apply(simp add: valid_cfg_def)
      apply(clarsimp del: subsetI)
      apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w1 @ teA B # \<beta>\<rparr>"
      in ballE)
       apply(rename_tac B w z \<beta> A w1 y)(*strict*)
       apply(clarsimp del: subsetI)
       apply(simp only: setAConcat concat_asso)
       apply(clarsimp)
      apply(rename_tac B w z \<beta> A w1 y)(*strict*)
      apply(blast)
     apply(rename_tac B w z \<beta> A w1 y)(*strict*)
     apply(rule_tac
      s="{}"
      and t="setA (liftB y)"
      in ssubst)
      apply(rename_tac B w z \<beta> A w1 y)(*strict*)
      apply(rule setA_liftB_empty)
     apply(rename_tac B w z \<beta> A w1 y)(*strict*)
     apply(blast)
    apply(rename_tac B w z \<beta> A w1 y)(*strict*)
    apply(simp (no_asm) only: setBConcat concat_asso)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac B w z \<beta> A w1 y)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(clarsimp del: subsetI)
     apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w1 @ teA B # \<beta>\<rparr>"
      in ballE)
      apply(rename_tac B w z \<beta> A w1 y)(*strict*)
      apply(clarsimp del: subsetI)
      apply(simp only: setBConcat concat_asso)
      apply(clarsimp)
     apply(rename_tac B w z \<beta> A w1 y)(*strict*)
     apply(blast)
    apply(rename_tac B w z \<beta> A w1 y)(*strict*)
    apply(rule_tac
      s="set y"
      and t="setB (liftB y)"
      in ssubst)
     apply(rename_tac B w z \<beta> A w1 y)(*strict*)
     apply(rule sym)
     apply(rule set_setB_liftB)
    apply(rename_tac B w z \<beta> A w1 y)(*strict*)
    apply(blast)
   apply(rename_tac B w z \<beta> A w1 y)(*strict*)
   apply(blast)
  apply(rename_tac B w z \<beta> A w1 y)(*strict*)
  apply(rule_tac
      x="\<lparr>prod_lhs = B, prod_rhs = w\<rparr>"
      in bexI)
   apply(rename_tac B w z \<beta> A w1 y)(*strict*)
   apply(clarsimp)
  apply(rename_tac B w z \<beta> A w1 y)(*strict*)
  apply(clarsimp)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_termLem: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)"
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(erule_tac
      x="xa"
      in ballE)
   apply(rename_tac x xa)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1_adds_valid_item)
      apply(rename_tac x xa)(*strict*)
      apply(blast)+
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_mono: "
  S \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S"
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      x="x"
      in bexI)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  done

lemma finite_ItemSet: "
  valid_cfg G
  \<Longrightarrow> finite (Collect (valid_item G k))"
  apply(rule_tac
      s=" \<Union>{(\<lambda>(p::('a,'b)cfg_step_label). \<Union>{(\<lambda>n. \<Union>{(\<lambda>w. {\<lparr>cfg_item_lhs=prod_lhs p,cfg_item_rhs1=take n (prod_rhs p),cfg_item_rhs2=drop n (prod_rhs p),cfg_item_look_ahead=w\<rparr>} ) w |w. w \<in> {w. length w\<le>k \<and> set w \<subseteq> cfg_events G}} ) n |n. n \<in> {n. n\<le>length (prod_rhs x)}} ) x |x. x \<in> (cfg_productions G)} "
      and t="Collect (valid_item G k)"
      in ssubst)
   prefer 2
   apply(rule finite_big_union)
    prefer 2
    apply(rule ballI)
    apply(rename_tac x)(*strict*)
    apply(rule finite_big_union)
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(rule ballI)
     apply(rename_tac x n)(*strict*)
     apply(rule finite_big_union)
      apply(rename_tac x n)(*strict*)
      prefer 2
      apply(rule ballI)
      apply(rename_tac x n w)(*strict*)
      apply(force)
     apply(rename_tac x n)(*strict*)
     prefer 4
     apply(rule order_antisym)
      apply(rule subsetI)
      apply(rename_tac x)(*strict*)
      apply(rule InBigUnion)
      apply(rule_tac
      x="\<lparr>prod_lhs=cfg_item_lhs x,prod_rhs=(cfg_item_rhs1 x)@(cfg_item_rhs2 x)\<rparr>"
      in bexI)
       apply(rename_tac x)(*strict*)
       apply(rule InBigUnion)
       apply(rule_tac
      x="length (cfg_item_rhs1 x)"
      in bexI)
        apply(rename_tac x)(*strict*)
        apply(rule InBigUnion)
        apply(rule_tac
      x="cfg_item_look_ahead x"
      in bexI)
         apply(rename_tac x)(*strict*)
         apply(simp)
        apply(rename_tac x)(*strict*)
        apply(simp)
        apply(simp add: valid_item_def)
       apply(rename_tac x)(*strict*)
       apply(simp)
      apply(rename_tac x)(*strict*)
      apply(simp add: valid_item_def)
      apply(clarsimp)
      apply(rename_tac x p)(*strict*)
      apply(subgoal_tac "p=\<lparr>prod_lhs = cfg_item_lhs x, prod_rhs = cfg_item_rhs1 x @ cfg_item_rhs2 x\<rparr>")
       apply(rename_tac x p)(*strict*)
       apply(simp)
      apply(rename_tac x p)(*strict*)
      apply(simp)
     apply(rule subsetI)
     apply(rename_tac x)(*strict*)
     apply(drule InBigUnion2)
     apply(erule bexE)
     apply(rename_tac x xa)(*strict*)
     apply(drule InBigUnion2)
     apply(erule bexE)
     apply(rename_tac x xa n)(*strict*)
     apply(drule InBigUnion2)
     apply(erule bexE)
     apply(rename_tac x xa n w)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa n w)(*strict*)
     apply(simp add: valid_item_def)
     apply(rule_tac
      x="xa"
      in bexI)
      apply(rename_tac xa n w)(*strict*)
      apply(clarsimp)
     apply(rename_tac xa n w)(*strict*)
     apply(clarsimp)
    apply(rename_tac x n)(*strict*)
    apply(rule_tac
      s="{w. w \<in> kleene_star (cfg_events G) \<and> length w\<le>k}"
      and t="{w. length w \<le> k \<and> set w \<subseteq> cfg_events G}"
      in ssubst)
     apply(rename_tac x n)(*strict*)
     apply(clarsimp)
     apply(simp add: kleene_star_def)
     apply(rule order_antisym)
      apply(rename_tac x n)(*strict*)
      apply(force)
     apply(rename_tac x n)(*strict*)
     apply(force)
    apply(rename_tac x n)(*strict*)
    apply(rule wordsUpToLengthFinite)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_cfg_def)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_cfg_def)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_termLem2: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S \<noteq> S
  \<Longrightarrow> card (Collect (valid_item G k) - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S) < card (Collect (valid_item G k) - S)"
  apply(rule Finite_Set.psubset_card_mono)
   prefer 2
   apply(rule rev_subset)
    prefer 3
    apply(rule_tac
      B = "Collect (valid_item G k)"
      in Finite_Set.finite_subset)
     apply(force)
    prefer 2
    apply(subgoal_tac "S\<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S")
     apply(blast)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_mono)
   prefer 2
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)")
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem)
    apply(blast)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(clarsimp)
  apply(rule finite_ItemSet)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_cfg_def)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_termination: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_dom (G, F, k, S)"
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,F,k,S). F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S"
      and RECURSIVE_COND = "\<lambda>(G,F,k,S). F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S\<noteq>S"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,F,k,S). (G,F,k,F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)"
      and MEASURE = "\<lambda>(G,F,k,S). card (((Collect (\<lambda>x. valid_item G k x)))-S)"
      in partial_termination_wf)
      apply(auto)
       apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
       apply(rename_tac G F k S x)
       apply(thin_tac "x \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S")
       apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)")
        apply(rename_tac G F k S x)(*strict*)
        apply(blast)
       apply(rename_tac G F k S x)(*strict*)
       apply(thin_tac "\<not> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)")
       apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem)
       apply(blast)
      apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
      apply(rename_tac G F k S x)
      apply(thin_tac "x \<in> S")
      apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)")
       apply(blast)
      apply(thin_tac "\<not> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)")
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem)
      apply(blast)
     apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
     apply(rename_tac G F k S x)
     apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S = S")
      apply(force)
     apply(thin_tac "x \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S")
     apply(subgoal_tac "card (Collect (valid_item G k) - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S) < card (Collect (valid_item G k) - S)")
      apply(blast)
     apply(rename_tac G F k S x)(*strict*)
     apply(thin_tac "\<not> card (Collect (valid_item G k) - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S) < card (Collect (valid_item G k) - S)")
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem2)
      apply(rename_tac G F k S x)(*strict*)
      apply(blast)
     apply(rename_tac G F k S x)(*strict*)
     apply(force)
    apply(rename_tac a aa b x)(*strict*)
    apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
    apply(rename_tac G F k S x)
    apply(rename_tac G F k S x)(*strict*)
    apply(subgoal_tac "S \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S")
     apply(rename_tac G F k S x)(*strict*)
     prefer 2
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_mono)
    apply(rename_tac G F k S x)(*strict*)
    apply(blast)
   apply(rename_tac a aa b)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.domintros)
    apply(rename_tac a aa b x)(*strict*)
    apply(force,force)
  apply(rename_tac a aa b)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.domintros)
   apply(rename_tac a aa b x)(*strict*)
   apply(force,force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> N \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
  apply(rule_tac
      P = "\<lambda>G F k N. N \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in F_VALID_ITEM_SET_GOTO__descent__fp.pinduct)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(rename_tac Ga Fa ka S)(*strict*)
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s Ga Fa ka S \<noteq> S")
   apply(rename_tac Ga Fa ka S)(*strict*)
   apply(clarsimp del: subsetI)
   apply(rule_tac
      B="F_VALID_ITEM_SET_GOTO__descent__fp_one_1s Ga Fa ka S"
      in subset_trans)
    apply(rename_tac Ga Fa ka S)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_mono)
   apply(rename_tac Ga Fa ka S)(*strict*)
   apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp Ga Fa ka S"
      and s = "F_VALID_ITEM_SET_GOTO__descent__fp Ga Fa ka (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s Ga Fa ka S)"
      in ssubst)
    apply(rename_tac Ga Fa ka S)(*strict*)
    apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
    apply(rename_tac G F k S)(*strict*)
    apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S = S then S else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S))"
      in ssubst)
     apply(rename_tac G F k S)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(blast)
    apply(rename_tac G F k S)(*strict*)
    apply(force)
   apply(rename_tac Ga Fa ka S)(*strict*)
   apply(force)
  apply(rename_tac Ga Fa ka S)(*strict*)
  apply(clarsimp del: subsetI)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
  apply(rename_tac G F k S)(*strict*)
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S = S then S else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S))"
      in ssubst)
   apply(rename_tac G F k S)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(blast)
  apply(rename_tac G F k S)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_mono: "
  valid_cfg G
  \<Longrightarrow> S \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> S \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(auto)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_adds_valid_item: "
  valid_cfg G
  \<Longrightarrow> Ball S (valid_item G k)
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S \<subseteq> Collect (valid_item G k)"
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  apply(auto)
  apply(rename_tac x xa)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1_adds_valid_item)
     apply(rename_tac x xa)(*strict*)
     apply(blast)+
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER_AT_START: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N"
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER_def)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_01_def F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02_def )
  apply(auto)
  apply(rename_tac J I)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  apply(auto)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_preserves_F_VALID_ITEM_SET_GOTO__descent__fp_valid_input: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N")
   apply(clarsimp)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem)
  apply(auto)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_TRANSFER_TRANSFERS_ALL: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER_AT_START)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> (\<And>G F k N. F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<Longrightarrow> P G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)) \<Longrightarrow> P G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))
  \<Longrightarrow> (\<And>G F k N. F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<Longrightarrow> P G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))
  \<Longrightarrow> P G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N)"
  apply(subgoal_tac "(\<lambda>G F k N. F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<longrightarrow> (P G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))) G F k N")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER_AT_START)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<longrightarrow> (P G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))) (G,F,k,N)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N"
      and RECURSIVE_COND = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,F,k,N). (G,F,k,F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and MEASURE = "\<lambda>(G,F,k,S). card (((Collect (\<lambda>x. valid_item G k x)))-S)"
      and TERM_FUN = "(\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<longrightarrow> (P G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N)))"
      and y = "(G,F,k,N)"
      in partial_termination_wf)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
      apply(rename_tac G F k N)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_preserves_F_VALID_ITEM_SET_GOTO__descent__fp_valid_input)
      apply(blast)
     apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rename_tac G F k N)
     apply(rename_tac G F k N)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem2)
      apply(rename_tac G F k N)(*strict*)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rename_tac G F k N)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   prefer 2
   apply(clarsimp)
  apply(clarsimp)
  apply(erule impE)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_TRANSFER_TRANSFERS_ALL)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_idemp2: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(blast)
  apply(clarsimp)
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(blast)
  apply(clarsimp)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift_prime: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> (\<And>G F k N. F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<Longrightarrow> P G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) (F_VALID_ITEM_SET_GOTO__descent__fp G F k N) \<Longrightarrow> P G F k N (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))
  \<Longrightarrow> (\<And>G F k N. F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N \<Longrightarrow> valid_cfg G \<Longrightarrow> \<forall>x \<in> N. valid_item G k x \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<Longrightarrow> P G F k N (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))
  \<Longrightarrow> P G F k N (F_VALID_ITEM_SET_GOTO__descent__fp G F k N)"
  apply(subgoal_tac "(\<lambda>G F k N. F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<longrightarrow> (P G F k N (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))) G F k N")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER_AT_START)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<longrightarrow> (P G F k N (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))) (G,F,k,N)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N"
      and RECURSIVE_COND = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,F,k,N). (G,F,k,F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and MEASURE = "\<lambda>(G,F,k,S). card (((Collect (\<lambda>x. valid_item G k x)))-S)"
      and TERM_FUN = "(\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER G F k N \<longrightarrow> (P G F k N (F_VALID_ITEM_SET_GOTO__descent__fp G F k N)))"
      and y = "(G,F,k,N)"
      in partial_termination_wf)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a aa b)(*strict*)
      apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
      apply(rename_tac G F k N)
      apply(rename_tac G F k N)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_preserves_F_VALID_ITEM_SET_GOTO__descent__fp_valid_input)
      apply(blast)
     apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rename_tac G F k N)
     apply(rename_tac G F k N)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem2)
      apply(rename_tac G F k N)(*strict*)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rename_tac G F k N)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   prefer 2
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
  apply(rename_tac G F k N)
  apply(rename_tac G F k N)(*strict*)
  apply(erule impE)
   apply(rename_tac G F k N)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_TRANSFER_TRANSFERS_ALL)
     apply(rename_tac G F k N)(*strict*)
     apply(blast)
    apply(rename_tac G F k N)(*strict*)
    apply(blast)
   apply(rename_tac G F k N)(*strict*)
   apply(blast)
  apply(rename_tac G F k N)(*strict*)
  apply(subgoal_tac "P G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) (F_VALID_ITEM_SET_GOTO__descent__fp G F k N)")
   apply(rename_tac G F k N)(*strict*)
   apply(thin_tac "P G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) (F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))")
   prefer 2
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      in ssubst)
    apply(rename_tac G F k N)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_idemp2)
    apply(force)
   apply(rename_tac G F k N)(*strict*)
   apply(force)
  apply(rename_tac G F k N)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_has_reason: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> S \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k S
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S
  \<Longrightarrow> cfg_item_rhs1 I = []
  \<Longrightarrow> \<exists>I2 \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. cfg_item_rhs1 I2 = [] \<and> (\<exists>I3 \<in> S. \<exists>w. cfg_item_rhs2 I3 = teA (cfg_item_lhs I2) # w)"
  apply(subgoal_tac " (S\<noteq>F_VALID_ITEM_SET_GOTO__descent__fp G F k S) \<longrightarrow> (\<forall>I1 \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. cfg_item_rhs1 I1 = [] \<longrightarrow> (\<exists>I2 \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. cfg_item_rhs1 I2 = [] \<and> (\<exists>I3 \<in> S. \<exists>w. (cfg_item_rhs2 I3)=teA (cfg_item_lhs I2)#w )))")
   apply(force)
  apply(thin_tac "S \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
  apply(thin_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
  apply(thin_tac "cfg_item_rhs1 I = []")
  apply(rule_tac
      G="G"
      and k="k"
      and N="S"
      in F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift_prime)
    apply(force)
   apply(rename_tac Ga Fa ka N)(*strict*)
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I1)(*strict*)
   apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
    apply(rename_tac G F k N I1)(*strict*)
    apply(erule impE)
     apply(rename_tac G F k N I1)(*strict*)
     apply(force)
    apply(rename_tac G F k N I1)(*strict*)
    apply(erule impE)
     apply(rename_tac G F k N I1)(*strict*)
     apply(rule_tac
      x="I1"
      in bexI)
      apply(rename_tac G F k N I1)(*strict*)
      apply(force)
     apply(rename_tac G F k N I1)(*strict*)
     apply(force)
    apply(rename_tac G F k N I1)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
    apply(case_tac "I3 \<in> N")
     apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
     apply(force)
    apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
    apply(rule_tac
      x="I3"
      in bexI)
     apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
     apply(clarsimp)
     apply(rename_tac G F k N I1 I2 I3 w x)(*strict*)
     apply(erule disjE)
      apply(rename_tac G F k N I1 I2 I3 w x)(*strict*)
      apply(force)
     apply(rename_tac G F k N I1 I2 I3 w x)(*strict*)
     apply(clarsimp)
     apply(rename_tac G F k N I1 I2 w x B z \<beta>)(*strict*)
     apply(rule_tac
      x="x"
      in bexI)
      apply(rename_tac G F k N I1 I2 w x B z \<beta>)(*strict*)
      apply(force)
     apply(rename_tac G F k N I1 I2 w x B z \<beta>)(*strict*)
     apply(force)
    apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
    apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N"
      in set_mp)
     apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
     apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      in ssubst)
      apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_idemp2)
      apply(force)
     apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
     apply(force)
    apply(rename_tac G F k N I1 I2 I3 w)(*strict*)
    apply(force)
   apply(rename_tac G F k N I1)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "I1 \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
    apply(rename_tac G F k N I1)(*strict*)
    apply(subgoal_tac "N \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
     apply(rename_tac G F k N I1)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G F k N I1)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k N I1)(*strict*)
   apply(thin_tac "I1 \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(thin_tac "N \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N"
      in ssubst)
    apply(rename_tac G F k N I1)(*strict*)
    apply(force)
   apply(rename_tac G F k N I1)(*strict*)
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(subgoal_tac "\<exists>x. x \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N \<and> x\<notin>N")
    apply(rename_tac G F k N I1)(*strict*)
    prefer 2
    apply(subgoal_tac "N \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
     apply(rename_tac G F k N I1)(*strict*)
     apply(force)
    apply(rename_tac G F k N I1)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_mono)
   apply(rename_tac G F k N I1)(*strict*)
   apply(thin_tac "N \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
   apply(clarsimp)
   apply(rename_tac G F k N I1 x)(*strict*)
   apply(rule_tac
      x="x"
      in bexI)
    apply(rename_tac G F k N I1 x)(*strict*)
    apply(rule conjI)
     apply(rename_tac G F k N I1 x)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
     apply(clarsimp)
     apply(rename_tac G F k N I1 x xa xb)(*strict*)
     apply(erule_tac
      P="I1 = xa"
      in disjE)
      apply(rename_tac G F k N I1 x xa xb)(*strict*)
      apply(clarsimp)
      apply(rename_tac G F k N x xa xb)(*strict*)
      apply(erule disjE)
       apply(rename_tac G F k N x xa xb)(*strict*)
       apply(clarsimp)
      apply(rename_tac G F k N x xa xb)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N I1 x xa xb)(*strict*)
     apply(erule disjE)
      apply(rename_tac G F k N I1 x xa xb)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N I1 x xa xb)(*strict*)
     apply(clarsimp)
    apply(rename_tac G F k N I1 x)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
    apply(clarsimp)
    apply(rename_tac G F k N I1 x xa xb)(*strict*)
    apply(erule_tac
      P="I1 = xa"
      in disjE)
     apply(rename_tac G F k N I1 x xa xb)(*strict*)
     apply(clarsimp)
     apply(rename_tac G F k N x xa xb)(*strict*)
     apply(erule disjE)
      apply(rename_tac G F k N x xa xb)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N x xa xb)(*strict*)
     apply(clarsimp)
     apply(rename_tac G F k N xa xb B w z \<beta>)(*strict*)
     apply(rule_tac
      x="xb"
      in bexI)
      apply(rename_tac G F k N xa xb B w z \<beta>)(*strict*)
      apply(force)
     apply(rename_tac G F k N xa xb B w z \<beta>)(*strict*)
     apply(force)
    apply(rename_tac G F k N I1 x xa xb)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N x xa xb B w z \<beta>)(*strict*)
    apply(erule disjE)
     apply(rename_tac G F k N x xa xb B w z \<beta>)(*strict*)
     apply(clarsimp)
    apply(rename_tac G F k N x xa xb B w z \<beta>)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N xa xb B w z \<beta> Ba wa za \<beta>')(*strict*)
    apply(rule_tac
      x="xb"
      in bexI)
     apply(rename_tac G F k N xa xb B w z \<beta> Ba wa za \<beta>')(*strict*)
     apply(force)
    apply(rename_tac G F k N xa xb B w z \<beta> Ba wa za \<beta>')(*strict*)
    apply(force)
   apply(rename_tac G F k N I1 x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga Fa ka N)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga Fa ka N I1)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
  apply(rename_tac G F k N I1)(*strict*)
  apply(subgoal_tac "N=F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(rename_tac G F k N I1)(*strict*)
   apply(force)
  apply(rename_tac G F k N I1)(*strict*)
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
   apply(rename_tac G F k N I1)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER_def)
  apply(rename_tac G F k N I1)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_has_reason_prime: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> I \<notin> S
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S
  \<Longrightarrow> cfg_item_rhs1 I = []
  \<Longrightarrow> \<exists>J \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. \<exists>w. cfg_item_rhs2 J = teA (cfg_item_lhs I) # w"
  apply(subgoal_tac " (\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. I\<notin>S \<and> cfg_item_rhs1 I = [] \<longrightarrow> (\<exists>J \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. \<exists>w. (cfg_item_rhs2 J)=teA (cfg_item_lhs I)#w))")
   apply(force)
  apply(thin_tac "I\<notin>S")
  apply(thin_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
  apply(thin_tac "cfg_item_rhs1 I = []")
  apply(rule_tac
      G="G"
      and k="k"
      and N="S"
      in F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift_prime)
    apply(force)
   apply(rename_tac Ga Fa ka N)(*strict*)
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I)(*strict*)
   apply(erule_tac
      x="I"
      in ballE)
    apply(rename_tac G F k N I)(*strict*)
    apply(clarsimp)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
    apply(clarsimp)
    apply(rename_tac G F k N I x)(*strict*)
    apply(erule disjE)
     apply(rename_tac G F k N I x)(*strict*)
     apply(clarsimp)
    apply(rename_tac G F k N I x)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N x B w z \<beta>)(*strict*)
    apply(erule_tac
      x="x"
      in ballE)
     apply(rename_tac G F k N x B w z \<beta>)(*strict*)
     apply(clarsimp)
    apply(rename_tac G F k N x B w z \<beta>)(*strict*)
    apply(subgoal_tac "N \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
     apply(rename_tac G F k N x B w z \<beta>)(*strict*)
     apply(force)
    apply(rename_tac G F k N x B w z \<beta>)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(force)
  apply(rename_tac Ga Fa ka N)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga Fa ka N I)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
  apply(rename_tac G F k N I)(*strict*)
  apply(subgoal_tac "N=F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(rename_tac G F k N I)(*strict*)
   apply(force)
  apply(rename_tac G F k N I)(*strict*)
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
   apply(rename_tac G F k N I)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER_def)
  apply(rename_tac G F k N I)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_fresh: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> \<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. I \<in> S \<or> (cfg_item_rhs1 I = [])"
  apply(rule_tac
      P="\<lambda>G F k S. \<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. I \<in> S \<or> (cfg_item_rhs1 I=[])"
      in F_VALID_ITEM_SET_GOTO__descent__fp.pinduct)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(rename_tac Ga Fa ka Sa)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga Fa ka Sa I)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
  apply(rename_tac G F k S I)(*strict*)
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S \<noteq> S")
   apply(rename_tac G F k S I)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="I"
      in ballE)
    apply(rename_tac G F k S I)(*strict*)
    apply(clarsimp)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
    apply(clarsimp)
    apply(rename_tac G F k S I x)(*strict*)
    apply(erule disjE)
     apply(rename_tac G F k S I x)(*strict*)
     apply(clarsimp)
    apply(rename_tac G F k S I x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k S I)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k S = F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)")
    apply(rename_tac G F k S I)(*strict*)
    prefer 2
    apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S = S then S else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S))"
      in ssubst)
     apply(rename_tac G F k S I)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(blast)
    apply(rename_tac G F k S I)(*strict*)
    apply(force)
   apply(rename_tac G F k S I)(*strict*)
   apply(force)
  apply(rename_tac G F k S I)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k S = F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S")
   apply(rename_tac G F k S I)(*strict*)
   prefer 2
   apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S = S then S else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S))"
      in ssubst)
    apply(rename_tac G F k S I)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(blast)
   apply(rename_tac G F k S I)(*strict*)
   apply(force)
  apply(rename_tac G F k S I)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02_unfold: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> Ball (F_VALID_ITEM_SET_GOTO__descent__fp G F k S) (valid_item G k)"
  apply(rule_tac
      k="k"
      in F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga Fa ka N)(*strict*)
   defer
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
   apply(rename_tac G F k N)(*strict*)
   apply(rename_tac G F k N)
   apply(clarsimp)
   apply(rename_tac G F k N x)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N=N")
    apply(rename_tac G F k N x)(*strict*)
    apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k N = N")
     apply(rename_tac G F k N x)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "x \<in> (Collect (valid_item G k))")
      apply(rename_tac G F k N x)(*strict*)
      apply(blast)
     apply(rename_tac G F k N x)(*strict*)
     apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N"
      in set_mp)
      apply(rename_tac G F k N x)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_adds_valid_item)
        apply(rename_tac G F k N x)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N x)(*strict*)
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_TRANSFER_def F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02_def)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rename_tac G F k N x)(*strict*)
     apply(force)
    apply(rename_tac G F k N x)(*strict*)
    apply(rule_tac
      s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t="F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
     apply(rename_tac G F k N x)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(rename_tac G F k N x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga Fa ka N)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
  apply(rename_tac G F k N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N x)(*strict*)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)")
   apply(rename_tac G F k N x)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac G F k N x)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac G F k N x)(*strict*)
   apply(force)
  apply(rename_tac G F k N x)(*strict*)
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and s = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
   apply(rename_tac G F k N x)(*strict*)
   apply(case_tac "N = F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
    apply(rename_tac G F k N x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k N x)(*strict*)
   apply(rule sym)
   apply(rule_tac
      P = "\<lambda>x. x = F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
    apply(rename_tac G F k N x)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(blast)
   apply(rename_tac G F k N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k N x)(*strict*)
  apply(clarsimp)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_preserves_valid_item: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> \<forall>I \<in> S. valid_item G k I
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S
  \<Longrightarrow> valid_item G k I"
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  apply(clarsimp)
  apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G (cfgSTD_first) k x")
   prefer 2
   apply(metis F_VALID_ITEM_SET_GOTO__descent__fp_one_1__with_cfgSTD_first_compatible)
  apply(thin_tac "cfgSTD_first_compatible F k")
  apply(thin_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k x")
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  apply(auto)
  apply(rename_tac x B w z \<beta>)(*strict*)
  apply(simp add: valid_item_def)
  apply(auto)
    apply(rename_tac x B w z \<beta>)(*strict*)
    apply(rule cfgSTD_firstk_shorter_than_k)
    apply(force)
   apply(rename_tac x B w z \<beta> xa)(*strict*)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac x B w z \<beta> xa)(*strict*)
    apply(auto)
   apply(rename_tac x B w z \<beta> xa p)(*strict*)
   apply(case_tac x)
   apply(rename_tac x B w z \<beta> xa p cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
   apply(case_tac p)
   apply(rename_tac x B w z \<beta> xa p cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_aheada prod_lhsa prod_rhsa)(*strict*)
   apply(auto)
   apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead)(*strict*)
   apply(rule_tac
      A="set z"
      in set_mp)
    apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead)(*strict*)
    apply(rule_tac
      v="\<beta> @ liftB (cfg_item_look_ahead)"
      in cfgSTD_firstk_in_cfg_events)
       apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead)(*strict*)
       apply(force)
      apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead)(*strict*)
      apply(simp add: valid_cfg_def)
      apply(auto)
    apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs, prod_rhs = cfg_item_rhs1 @ teA B # \<beta>\<rparr>"
      in ballE)
     apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
     apply(auto)
    apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
    apply(simp only: setAConcat concat_asso)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
     apply(force)
    apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
    apply(subgoal_tac "setA (liftB cfg_item_look_ahead)={}")
     apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
     prefer 2
     apply(rule setA_liftB_empty)
    apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
    apply(force)
   apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(auto)
   apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs, prod_rhs = cfg_item_rhs1 @ teA B # \<beta>\<rparr>"
      in ballE)
    apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
    apply(auto)
   apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
   apply(simp only: setBConcat concat_asso)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
    apply(force)
   apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
   apply(subgoal_tac "setB (liftB cfg_item_look_ahead)=set cfg_item_look_ahead")
    apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule set_setBliftB)
   apply(rename_tac B w z \<beta> xa cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead x)(*strict*)
   apply(force)
  apply(rename_tac x B w z \<beta>)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_01_unfold: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> \<forall>J \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. \<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k J. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
  apply(rule_tac
      k="k"
      in F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga Fa ka N)(*strict*)
   defer
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
   apply(rename_tac G F k N)(*strict*)
   apply(rename_tac G F k N)
   apply(clarsimp)
   apply(rename_tac G F k N J I)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N=N")
    apply(rename_tac G F k N J I)(*strict*)
    apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k N = N")
     apply(rename_tac G F k N J I)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N"
      in set_mp)
      apply(rename_tac G F k N J I)(*strict*)
      apply(force)
     apply(rename_tac G F k N J I)(*strict*)
     apply(simp (no_asm) add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
     apply(rule_tac
      x="J"
      in bexI)
      apply(rename_tac G F k N J I)(*strict*)
      apply(force)
     apply(rename_tac G F k N J I)(*strict*)
     apply(force)
    apply(rename_tac G F k N J I)(*strict*)
    apply(rule_tac
      s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t="F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
     apply(rename_tac G F k N J I)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(rename_tac G F k N J I)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k N J I)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga Fa ka N)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
  apply(rename_tac G F k N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N J I)(*strict*)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)")
   apply(rename_tac G F k N J I)(*strict*)
   apply(erule_tac
      x="J"
      in ballE)
    apply(rename_tac G F k N J I)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac G F k N J I)(*strict*)
   apply(force)
  apply(rename_tac G F k N J I)(*strict*)
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and s = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
   apply(rename_tac G F k N J I)(*strict*)
   apply(case_tac "N = F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
    apply(rename_tac G F k N J I)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k N J I)(*strict*)
   apply(rule sym)
   apply(rule_tac
      P = "\<lambda>x. x = F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
    apply(rename_tac G F k N J I)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(blast)
   apply(rename_tac G F k N J I)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k N J I)(*strict*)
  apply(clarsimp)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_preserves_required_production: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> (\<forall>I \<in> S. valid_item G k I) \<and> valid_cfg G \<and> (F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S) \<and> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S \<and> I \<notin> S \<longrightarrow> (\<exists>p \<in> cfg_productions G. teA (cfg_item_lhs I) \<in> set (prod_rhs p))"
  apply(rule_tac
      ?a0.0="G"
      and ?a1.0="F"
      and ?a2.0="k"
      and ?a3.0="S"
      in F_VALID_ITEM_SET_GOTO__descent__fp.pinduct)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(force)
  apply(rename_tac Ga Fa ka Sa)(*strict*)
  apply(clarsimp)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
  apply(rename_tac G F k S)(*strict*)
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S \<noteq> S")
   apply(rename_tac G F k S)(*strict*)
   apply(clarsimp)
   apply(erule impE)
    apply(rename_tac G F k S)(*strict*)
    apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S)"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
      in ssubst)
     apply(rename_tac G F k S)(*strict*)
     apply(rule_tac
      s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S = S then S else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S))"
      and t="F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
      in ssubst)
      apply(rename_tac G F k S)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rename_tac G F k S)(*strict*)
     apply(clarsimp)
    apply(rename_tac G F k S)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k S)(*strict*)
   apply(erule impE)
    apply(rename_tac G F k S)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem)
    apply(force)
   apply(rename_tac G F k S)(*strict*)
   apply(erule disjE)
    apply(rename_tac G F k S)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k S x)(*strict*)
    apply(subgoal_tac "valid_item G k x")
     apply(rename_tac G F k S x)(*strict*)
     prefer 2
     apply(rule_tac
      S="S"
      in F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_preserves_valid_item)
        apply(rename_tac G F k S x)(*strict*)
        apply(force)
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(rename_tac G F k S x)(*strict*)
      apply(force)
     apply(rename_tac G F k S x)(*strict*)
     apply(force)
    apply(rename_tac G F k S x)(*strict*)
    apply(force)
   apply(rename_tac G F k S)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
   apply(clarsimp)
   apply(rename_tac G F k S x)(*strict*)
   apply(erule disjE)
    apply(rename_tac G F k S x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k S x)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k S x B w z \<beta>)(*strict*)
   apply(subgoal_tac "valid_item G k x")
    apply(rename_tac G F k S x B w z \<beta>)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k S x B w z \<beta>)(*strict*)
   apply(simp add: valid_item_def)
   apply(clarsimp)
   apply(rename_tac G F k S x B w z \<beta> p)(*strict*)
   apply(rule_tac
      x="p"
      in bexI)
    apply(rename_tac G F k S x B w z \<beta> p)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k S x B w z \<beta> p)(*strict*)
   apply(force)
  apply(rename_tac G F k S)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k S = S")
   apply(rename_tac G F k S)(*strict*)
   apply(force)
  apply(rename_tac G F k S)(*strict*)
  apply(rule_tac
      s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S = S then S else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k S))"
      and t="F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
      in ssubst)
   apply(rename_tac G F k S)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(rename_tac G F k S)(*strict*)
  apply(clarsimp)
  done

lemma immediate_decendant_also_in_F_VALID_ITEM_SET_GOTO__descent__fp: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k J
  \<Longrightarrow> J \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S
  \<Longrightarrow> Ball S (valid_item G k)
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
  apply(subgoal_tac "\<forall>J \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S. \<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k J. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_01_unfold)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(blast)
  done

lemma F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item: "
  Ball (F_VALID_ITEM_SET_INITIAL__fp_start G) (valid_item G k)"
  apply(simp add: F_VALID_ITEM_SET_INITIAL__fp_start_def)
  apply(auto)
  apply(simp add: valid_item_def)
  apply(auto)
  done

lemma Lemma6__17: "
  valid_cfg G
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teA B # \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k n \<gamma>
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>)
  \<Longrightarrow> d m = Some (pair e \<lparr>cfg_conf = v\<rparr>)
  \<Longrightarrow> setA v = {}
  \<Longrightarrow> \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr> \<in> cfg_productions G
  \<Longrightarrow> la = take k ((filterB v) @ y)
  \<Longrightarrow> \<lparr>cfg_item_lhs = B, cfg_item_rhs1 = [], cfg_item_rhs2 = \<omega>, cfg_item_look_ahead = la\<rparr> \<in> valid_item_set_n G k (Suc (n + m)) \<gamma>"
  apply(subgoal_tac "\<exists>d' e. cfgRM.derivation G d' \<and> maximum_of_domain d' m \<and> d' 0 = Some (pair None \<lparr>cfg_conf=\<beta>\<rparr>) \<and> d' m = Some (pair e \<lparr>cfg_conf=v\<rparr>)")
   prefer 2
   apply(rule cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(blast)
       apply(blast)
      apply(blast)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(thin_tac "cfgSTD.derivation G d")
  apply(thin_tac "maximum_of_domain d m")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf=\<beta>\<rparr>)")
  apply(thin_tac "d m = Some (pair e \<lparr>cfg_conf=v\<rparr>)")
  apply(clarsimp)
  apply(rename_tac d' e)(*strict*)
  apply(simp add: valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(rename_tac d' e d \<delta> e1 e2 z)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_append d (derivation_map (derivation_map d' ((\<lambda>v. \<lparr>cfg_conf=\<delta>@\<alpha>@[teA B]@(cfg_conf v)\<rparr>))) ((\<lambda>v. \<lparr>cfg_conf=(cfg_conf v)@z\<rparr>))) (Suc n)) (der2 \<lparr>cfg_conf = \<delta>@\<alpha>@[teA B]@v@z\<rparr> \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr> \<lparr>cfg_conf = \<delta>@\<alpha>@\<omega>@v@z\<rparr> ) (Suc n+m)"
      in exI)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(rule conjI)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule cfgRM.derivation_concat2)
      apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
      apply(rule cfgRM.derivation_concat2)
         apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
         apply(blast)
        apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
        apply(blast)
       apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
       apply(rule cfgRM.derivation_map_preserves_derivation2)
        apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
        apply(rule cfgRM.derivation_map_preserves_derivation2)
         apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
         apply(blast)
        apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
        apply(clarsimp)
        apply(rename_tac d' e d \<delta> e1 e2 z a ea b)(*strict*)
        apply(simp add: cfgRM_step_relation_def)
        apply(clarsimp)
        apply(rename_tac d' e d \<delta> e1 e2 z a ea b l r)(*strict*)
        apply(rule_tac
      x="\<delta> @ \<alpha> @ teA B # l"
      in exI)
        apply(rule_tac
      x="r"
      in exI)
        apply(clarsimp)
       apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
       apply(simp add: cfgRM_step_relation_def)
       apply(clarsimp)
       apply(rename_tac d' e d \<delta> e1 e2 z a ea b l r)(*strict*)
       apply(rule_tac
      x="l"
      in exI)
       apply(rule_tac
      x="r@z"
      in exI)
       apply(clarsimp)
       apply(simp (no_asm) only: setAConcat concat_asso)
       apply(blast)
      apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
      apply(clarsimp)
      apply(simp add: derivation_map_def)
     apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
     apply(rule concat_has_max_dom)
      apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
      apply(blast)
     apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(blast)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(rule_tac
      x="\<delta>@\<alpha>"
      in exI)
    apply(rule_tac
      x="v@z"
      in exI)
    apply(clarsimp)
    apply(simp (no_asm) only: setAConcat concat_asso)
    apply(blast)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(derivation_append d (derivation_map (derivation_map d' (\<lambda>v. \<lparr>cfg_conf = \<delta> @ \<alpha> @ teA B # cfg_conf v\<rparr>)) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ z\<rparr>)) (Suc n) (Suc (n + m)))= Some (pair (if m=0 then e2 else e) \<lparr>cfg_conf=\<delta> @ \<alpha> @ [teA B] @ v @ z\<rparr>) ")
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def )
   apply(clarsimp)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(rule conjI)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def der2_def)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      x="if m = 0 then e2 else e"
      in exI)
  apply(rule_tac
      x="Some \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr>"
      in exI)
  apply(rule_tac
      x="v@z"
      in exI)
  apply(rule conjI)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
   apply(clarsimp)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(rule conjI)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def der2_def)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(rule conjI)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      s="liftB (take k (filterB v)) @ (liftB (take (k - length (filterB v)) y))"
      and t="liftB (take k (filterB v) @ take (k - length (filterB v)) y)"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      s="take k (liftB (filterB v))"
      and t="liftB (take k (filterB v))"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule sym)
    apply(rule take_liftB)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      t="liftB (filterB v)"
      and s="v"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule liftBDeConv2)
    apply(blast)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="length (filterB v)"
      and s="length v"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule sym)
    apply(rule filterB_reflects_length)
    apply(blast)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      t="liftB (take (k - length v) y)"
      and s="take (k - length v) (liftB y)"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule sym)
    apply(rule take_liftB)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      s="take k z"
      and t="(liftB y)"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(clarsimp)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule sym)
   apply(rule_tac
      s="take (ord_class.min (k - length v) k) z"
      and t="take (k - length v) (take k z)"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule take_take)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      s="k-length v"
      and t="ord_class.min (k - length v) k"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(arith)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(blast)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(rule conjI)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      t="Suc (Suc (n + m))"
      and s="Suc (n+m)+Suc 0"
      in ssubst)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(arith)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule_tac
      t="Suc (n + m)"
      and s="Suc n+m"
      in ssubst)
     apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
     apply(arith)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule_tac concat_has_max_dom)
     apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
     apply(blast)
    apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(blast)
   apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac d' e d \<delta> e1 e2 z)(*strict*)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(blast)
  done

theorem Fact6_12__2: "
  valid_cfg G
  \<Longrightarrow> I \<in> valid_item_set G k \<gamma>
  \<Longrightarrow> valid_item G k I"
  apply(simp add: valid_item_set_def)
  apply(simp add: valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(blast)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
  apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = \<delta> @ teA A # z\<rparr> e \<lparr>cfg_conf = \<delta> @ \<alpha> @ \<beta> @ z\<rparr>")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
   prefer 2
   apply(rule cfgRM.position_change_due_to_step_relation)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
     apply(blast)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
  apply(subgoal_tac "e=\<lparr>prod_lhs=A,prod_rhs=\<alpha>@\<beta>\<rparr>")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
   apply(clarsimp)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
   apply(simp add: valid_item_def)
   apply(subgoal_tac "setB (l @ teA A # r) \<subseteq> cfg_events G")
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
    prefer 2
    apply(rule_tac
      w="[teA (cfg_initial G)]"
      and i="0"
      and j="n"
      in staysInSigma2)
         apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
         apply(blast)
        apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
        apply(simp add: setA_def valid_cfg_def)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
       apply(simp add: setB_def valid_cfg_def)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(blast)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
     apply(blast)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
    apply(clarsimp)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
   apply(subgoal_tac "setB (l @ \<alpha> @ \<beta> @ r) \<subseteq> cfg_events G")
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
    prefer 2
    apply(rule_tac
      w="[teA (cfg_initial G)]"
      and i="0"
      and j="Suc n"
      in staysInSigma2)
         apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
         apply(blast)
        apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
        apply(simp add: setA_def valid_cfg_def)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
       apply(simp add: setB_def valid_cfg_def)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(blast)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
     apply(blast)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
    apply(clarsimp)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = \<alpha> @ \<beta>\<rparr>"
      in ballE)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
    apply(clarsimp)
    apply(simp only: setBConcat setAConcat concat_asso)
    apply(clarsimp)
    apply(subgoal_tac "length y\<le> k")
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
     apply(rule conjI)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
      apply(force)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
     prefer 2
     apply(case_tac y)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
      apply(clarsimp)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac n A \<alpha> \<beta> d \<delta> e1 z l r a list)(*strict*)
     apply(rule_tac
      t="Suc (length list)"
      and s="length (teB a # liftB list)"
      in ssubst)
      apply(rename_tac n A \<alpha> \<beta> d \<delta> e1 z l r a list)(*strict*)
      apply(clarsimp)
      apply(rule liftB_reflects_length)
     apply(rename_tac n A \<alpha> \<beta> d \<delta> e1 z l r a list)(*strict*)
     apply(rule_tac
      s="take k z"
      and t="teB a # liftB list"
      in ssubst)
      apply(rename_tac n A \<alpha> \<beta> d \<delta> e1 z l r a list)(*strict*)
      apply(force)
     apply(rename_tac n A \<alpha> \<beta> d \<delta> e1 z l r a list)(*strict*)
     apply(rule takeShorter)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
    apply(subgoal_tac "z=r")
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
     prefer 2
     apply(rule_tac
      A="A"
      and ?v1.0="\<delta>"
      and ?v2.0="l"
      and B="A"
      in terminalTailEquals1)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
       apply(blast)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
      apply(blast)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
    defer
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
   apply(rule StepPreciseRM)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
     apply(blast)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
   apply(rule cfgRM.position_change_due_to_step_relation)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
     apply(blast)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
    apply(clarsimp)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z e)(*strict*)
   apply(force)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 z l r)(*strict*)
  apply(clarsimp del: subsetI)
  apply(rename_tac n A \<alpha> \<beta> y d e1 l r)(*strict*)
  apply(subgoal_tac "\<exists>v. r=(liftB y)@v")
   apply(rename_tac n A \<alpha> \<beta> y d e1 l r)(*strict*)
   apply(clarsimp del: subsetI)
   apply(rename_tac n A \<alpha> \<beta> y d e1 l v)(*strict*)
   apply(rule_tac
      s="setB (liftB y)"
      and t="set y"
      in ssubst)
    apply(rename_tac n A \<alpha> \<beta> y d e1 l v)(*strict*)
    apply(rule liftB_BiElem)
   apply(rename_tac n A \<alpha> \<beta> y d e1 l v)(*strict*)
   apply(rule conjI)
    apply(rename_tac n A \<alpha> \<beta> y d e1 l v)(*strict*)
    apply(simp only: setBConcat concat_asso)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> y d e1 l v)(*strict*)
   prefer 2
   apply(rename_tac n A \<alpha> \<beta> y d e1 l r)(*strict*)
   apply(rule takePrefix)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d e1 l v)(*strict*)
  apply(rule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = \<alpha> @ \<beta>\<rparr>"
      in bexI)
   apply(rename_tac n A \<alpha> \<beta> y d e1 l v)(*strict*)
   apply(auto)
  done

lemma valid_item_set_n_subset_valid_item_set: "
  I \<in> valid_item_set_n G k n w
  \<Longrightarrow> I \<in> valid_item_set G k w"
  apply(simp add: valid_item_set_def)
  apply(auto)
  done

lemma valid_item_set_n_contains_items: "
  valid_cfg G
  \<Longrightarrow> I \<in> valid_item_set_n G k n \<gamma>
  \<Longrightarrow> valid_item G k I"
  apply(metis Fact6_12__2 valid_item_set_n_subset_valid_item_set)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_idemp_on_valid_item_set: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (valid_item_set G k \<gamma>) = valid_item_set G k \<gamma>"
  apply(rule order_antisym)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_mono)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def valid_item_set_def)
  apply(clarsimp)
  apply(subgoal_tac "valid_item G k xa")
   prefer 2
   apply(metis valid_item_set_n_contains_items)
  apply(subgoal_tac "x \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G (cfgSTD_first) k xa")
   prefer 2
   apply(metis F_VALID_ITEM_SET_GOTO__descent__fp_one_1__with_cfgSTD_first_compatible)
  apply(thin_tac "cfgSTD_first_compatible F k")
  apply(thin_tac "x \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k xa")
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def valid_item_set_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  apply(rename_tac x xa n)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa n)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa n)(*strict*)
   apply(force)
  apply(rename_tac x xa n)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa n B w z \<beta>)(*strict*)
  apply(case_tac xa)
  apply(rename_tac xa n B w z \<beta> cfg_item_lhs cfg_item_rhs1 cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
  apply(clarsimp)
  apply(rename_tac n B w z \<beta> cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead)(*strict*)
  apply(rename_tac A w y)
  apply(rename_tac n B wa z \<beta> A w y)(*strict*)
  apply(simp add: cfgSTD_first_def)
  apply(auto)
  apply(rename_tac n B wa \<beta> A w y x d e1 na)(*strict*)
  apply(rule_tac
      x="Suc (n+na)"
      in exI)
  apply(subgoal_tac "\<exists>d x'. cfgSTD.derivation G d \<and> maximum_of_domain d na \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>) \<and> d na = Some (pair e1 \<lparr>cfg_conf = x'\<rparr>) \<and> x'@liftB y=liftB x")
   apply(rename_tac n B wa \<beta> A w y x d e1 na)(*strict*)
   prefer 2
   apply(rule TailTerminal_can_be_removed_from_derivation)
       apply(rename_tac n B wa \<beta> A w y x d e1 na)(*strict*)
       apply(blast)+
  apply(rename_tac n B wa \<beta> A w y x d e1 na)(*strict*)
  apply(thin_tac "cfgSTD.derivation G d")
  apply(thin_tac "maximum_of_domain d na")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB y\<rparr>)")
  apply(thin_tac "d na = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
  apply(clarsimp)
  apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
  apply(rule_tac Lemma6__17)
          apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
          apply(blast)
         apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
         apply(blast)
        apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
        apply(blast)
       apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
       apply(blast)
      apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
      apply(blast)
     apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
     apply(blast)
    apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
    apply(rule prefix_also_no_nonterms)
    apply(blast)
   apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
   apply(blast)
  apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
  apply(rule liftB_inj)
  apply(rule_tac
      s="take k (liftB x)"
      and t="liftB (take k x)"
      in ssubst)
   apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
   apply(rule sym)
   apply(rule take_liftB)
  apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
  apply(rule_tac
      s="x' @ liftB y"
      and t="liftB x"
      in ssubst)
   apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
   apply(force)
  apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
  apply(rule_tac
      s="take k (liftB (filterB x' @ y))"
      and t="liftB (take k (filterB x' @ y))"
      in ssubst)
   apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
   apply(rule sym)
   apply(rule take_liftB)
  apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
  apply(rule_tac
      s="liftB (filterB x') @ liftB y"
      and t="liftB (filterB x' @ y)"
      in ssubst)
   apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
   apply(rule liftB_commutes_over_concat)
  apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
  apply(rule_tac
      s="x'"
      and t="(liftB (filterB x'))"
      in ssubst)
   apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
   apply(rule liftBDeConv2)
   apply(rule prefix_also_no_nonterms)
   apply(blast)
  apply(rename_tac n B wa \<beta> A w y x e1 na d x')(*strict*)
  apply(blast)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_idemp: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k S) = F_VALID_ITEM_SET_GOTO__descent__fp G F k S"
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga Fa ka N)(*strict*)
   defer
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
   apply(rename_tac G F k N)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k N = N")
    apply(rename_tac G F k N)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k N)(*strict*)
   apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
    apply(rename_tac G F k N)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(blast)
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga Fa ka N)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k S")
  apply(rename_tac G F k N)(*strict*)
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      in ssubst)
   apply(rename_tac G F k N)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_idemp2)
   apply(blast)
  apply(rename_tac G F k N)(*strict*)
  apply(clarsimp)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_mono2: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k B
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k A
  \<Longrightarrow> A \<subseteq> B
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k A \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k B"
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  apply(auto)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_Comm: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) = F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N)"
  apply(subgoal_tac "(\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) = F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))(G,F,k,N)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N"
      and RECURSIVE_COND = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,F,k,N). (G,F,k,F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and MEASURE = "\<lambda>(G,F,k,S). card (((Collect (\<lambda>x. valid_item G k x)))-S)"
      and y = "(G,F,k,N)"
      in partial_termination_wf)
      apply(clarsimp)
      apply(rename_tac a aa b)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem)
      apply(blast)
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem2)
      apply(rename_tac a aa b)(*strict*)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rename_tac a aa b)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(clarsimp)
    apply(rename_tac a aa b)(*strict*)
    apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
    apply(rename_tac G F k N)
    apply(rename_tac G F k N)(*strict*)
    apply(rule_tac
      s = "N"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
     apply(rename_tac G F k N)(*strict*)
     apply(rule_tac
      s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
      apply(rename_tac G F k N)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
      apply(blast)
     apply(rename_tac G F k N)(*strict*)
     apply(clarsimp)
    apply(rename_tac G F k N)(*strict*)
    apply(clarsimp)
   prefer 2
   apply(blast)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
  apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(rename_tac G F k N)
  apply(rename_tac G F k N)(*strict*)
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N")
   apply(rename_tac G F k N)(*strict*)
   apply(rule_tac
      s = "N"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
    apply(rename_tac G F k N)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
     apply(rename_tac G F k N)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
     apply(blast)
    apply(rename_tac G F k N)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
    apply(rename_tac G F k N)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(blast)
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k N)(*strict*)
  apply(rule_tac
      s = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      in ssubst)
   apply(rename_tac G F k N)(*strict*)
   defer
   apply(rule_tac
      s = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
    apply(rename_tac G F k N)(*strict*)
    defer
    apply(clarsimp)
   apply(rename_tac G F k N)(*strict*)
   apply(rule_tac
      s = "(if (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)) = (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) then (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      in ssubst)
    apply(rename_tac G F k N)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(blast)
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      s = "(if (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)) = (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) then (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N) else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      in ssubst)
    apply(rename_tac G F k N)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(blast)
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k N)(*strict*)
  apply(rule_tac
      s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
   apply(rename_tac G F k N)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(blast)
  apply(rename_tac G F k N)(*strict*)
  apply(clarsimp)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_idemp: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N) = F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N")
   apply(rule_tac
      s = "N"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
    apply(rule_tac
      s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      in ssubst)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
     apply(blast)
    apply(clarsimp)
   apply(clarsimp)
  apply(rule_tac
      s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      and t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and P = "\<lambda>X. F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N) = X"
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(blast)
  apply(clarsimp)
  apply(rule sym)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_Comm)
  apply(blast)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_preserves_termination: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N)"
  apply(subgoal_tac "(\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k N))(G,F,k,N)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N"
      and RECURSIVE_COND = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,F,k,N). (G,F,k,F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and MEASURE = "\<lambda>(G,F,k,S). card (((Collect (\<lambda>x. valid_item G k x)))-S)"
      and y = "(G,F,k,N)"
      in partial_termination_wf)
      prefer 5
      apply(force)
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem)
     apply(blast)
    apply(clarsimp)
    apply(rename_tac a aa b)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem2)
     apply(rename_tac a aa b)(*strict*)
     apply(blast)
    apply(rename_tac a aa b)(*strict*)
    apply(blast)
   apply(clarsimp)
   apply(rename_tac a aa b)(*strict*)
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
   apply(rename_tac G F k N)
   apply(rename_tac G F k N)(*strict*)
   apply(subgoal_tac "N=F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
    apply(rename_tac G F k N)(*strict*)
    apply(force)
   apply(rename_tac G F k N)(*strict*)
   apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
    apply(rename_tac G F k N)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(blast)
   apply(rename_tac G F k N)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N")
  apply(rename_tac G F k N)
  apply(rename_tac G F k N)(*strict*)
  apply(case_tac "N=F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
   apply(rename_tac G F k N)(*strict*)
   apply(force)
  apply(rename_tac G F k N)(*strict*)
  apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = N then N else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N))"
      in ssubst)
   apply(rename_tac G F k N)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(blast)
  apply(rename_tac G F k N)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_mono2: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k A
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k B
  \<Longrightarrow> A \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k B
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp G F k A \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k B"
  apply(subgoal_tac " (\<lambda>(G,F,k,A). F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k B \<and> A\<subseteq> (F_VALID_ITEM_SET_GOTO__descent__fp G F k B) \<longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp G F k A \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k B)(G,F,k,A)")
   apply(clarsimp)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k N"
      and RECURSIVE_COND = "\<lambda>(G,F,k,N). F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,F,k,N). (G,F,k,F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N)"
      and MEASURE = "\<lambda>(G,F,k,S). card (((Collect (\<lambda>x. valid_item G k x)))-S)"
      and y = "(G,F,k,A)"
      in partial_termination_wf)
      prefer 5
      apply(force)
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem)
     apply(blast)
    apply(clarsimp)
    apply(rename_tac a aa b)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termLem2)
     apply(rename_tac a aa b)(*strict*)
     apply(blast)
    apply(rename_tac a aa b)(*strict*)
    apply(blast)
   apply(clarsimp)
   apply(rename_tac a aa b x)(*strict*)
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k A")
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k B")
   apply(thin_tac "A\<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k B")
   apply(rename_tac G F k A x)
   apply(rename_tac G F k A x)(*strict*)
   apply(rule_tac
      A="A"
      in set_mp)
    apply(rename_tac G F k A x)(*strict*)
    apply(rule_tac
      B="F_VALID_ITEM_SET_GOTO__descent__fp G F k B"
      in subset_trans)
     apply(rename_tac G F k A x)(*strict*)
     apply(blast)
    apply(rename_tac G F k A x)(*strict*)
    apply(blast)
   apply(rename_tac G F k A x)(*strict*)
   apply(subgoal_tac "A=F_VALID_ITEM_SET_GOTO__descent__fp G F k A")
    apply(rename_tac G F k A x)(*strict*)
    apply(blast)
   apply(rename_tac G F k A x)(*strict*)
   apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k A"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k A = A then A else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k A))"
      in ssubst)
    apply(rename_tac G F k A x)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(blast)
   apply(rename_tac G F k A x)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac a aa b x)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k A")
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G F k B")
  apply(thin_tac "A\<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k B")
  apply(rename_tac G F k A x)
  apply(rename_tac G F k A x)(*strict*)
  apply(erule impE)
   apply(rename_tac G F k A x)(*strict*)
   apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k B"
      and s = "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k B)"
      in ssubst)
    apply(rename_tac G F k A x)(*strict*)
    defer
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_mono2)
      apply(rename_tac G F k A x)(*strict*)
      defer
      apply(blast)
     apply(rename_tac G F k A x)(*strict*)
     apply(blast)
    apply(rename_tac G F k A x)(*strict*)
    apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k A)"
      in set_mp)
     apply(rename_tac G F k A x)(*strict*)
     apply(blast)
    apply(rename_tac G F k A x)(*strict*)
    apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp G F k A"
      in set_mp)
     apply(rename_tac G F k A x)(*strict*)
     apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G F k A"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k A = A then A else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k A))"
      in ssubst)
      apply(rename_tac G F k A x)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
      apply(blast)
     apply(rename_tac G F k A x)(*strict*)
     apply(clarsimp del: subsetI)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
     apply(blast)
    apply(rename_tac G F k A x)(*strict*)
    apply(blast)
   apply(rename_tac G F k A x)(*strict*)
   apply(rule sym)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_idemp)
   apply(blast)
  apply(rename_tac G F k A x)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_preserves_termination)
  apply(blast)+
  done

lemma F_VALID_ITEM_SET_INITIAL__fp_start_is_valid_item_set: "
  F_VALID_ITEM_SET_INITIAL__fp_start G \<subseteq> valid_item_set G k []"
  apply(simp add: F_VALID_ITEM_SET_INITIAL__fp_start_def valid_item_set_def)
  apply(clarsimp)
  apply(rename_tac p)(*strict*)
  apply(simp add: valid_item_set_n_def)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule_tac
      x = "der2 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> p \<lparr>cfg_conf = prod_rhs p\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac p)(*strict*)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(force)
  apply(rename_tac p)(*strict*)
  apply(rule conjI)
   apply(rename_tac p)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac p)(*strict*)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="Some p"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac  p)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac  p)(*strict*)
  apply(rule conjI)
   apply(rename_tac  p)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac  p)(*strict*)
  apply(rule der2_maximum_of_domain)
  done

lemma Lemma6_19: "
  valid_cfg G
  \<Longrightarrow> n > 0
  \<Longrightarrow> \<lparr>cfg_item_lhs = B, cfg_item_rhs1 = [], cfg_item_rhs2 = w, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set_n G k n \<gamma>
  \<Longrightarrow> \<exists>p \<in> cfg_productions G . \<exists>A \<alpha> \<beta>. p = \<lparr>prod_lhs = A, prod_rhs = \<alpha> @ [teA B] @ \<beta>\<rparr> \<and> (\<exists>y v. setA v = {} \<and> (\<exists>m < n. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = [teA B] @ \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k m \<gamma> \<and> (\<exists>d e. cfgRM.derivation G d \<and> maximum_of_domain d (n - m - (1::nat)) \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>) \<and> d (n - m - (1::nat)) = Some (pair e \<lparr>cfg_conf = v\<rparr>)) \<and> take k (filterB v @ y) = z))"
  apply(simp add: valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac d e1 e2 za)(*strict*)
  apply(rename_tac u)
  apply(rename_tac d e1 e2 u)(*strict*)
  apply(subgoal_tac "\<exists>n'. Suc n'=n")
   apply(rename_tac d e1 e2 u)(*strict*)
   prefer 2
   apply(case_tac n)
    apply(rename_tac d e1 e2 u)(*strict*)
    apply(force)
   apply(rename_tac d e1 e2 u nat)(*strict*)
   apply(force)
  apply(rename_tac d e1 e2 u)(*strict*)
  apply(erule exE)+
  apply(rename_tac d e1 e2 u n')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc n') = Some (pair (Some e) c)")
   apply(rename_tac d e1 e2 u n')(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac d e1 e2 u n')(*strict*)
     apply(blast)
    apply(rename_tac d e1 e2 u n')(*strict*)
    apply(blast)
   apply(rename_tac d e1 e2 u n')(*strict*)
   apply(arith)
  apply(rename_tac d e1 e2 u n')(*strict*)
  apply(erule exE)+
  apply(rename_tac d e1 e2 u n' e c)(*strict*)
  apply(subgoal_tac "e1=Some e")
   apply(rename_tac d e1 e2 u n' e c)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac d e1 e2 u n' e c)(*strict*)
  apply(thin_tac "d (Suc n') = Some (pair (Some e) c)")
  apply(clarsimp)
  apply(rename_tac d e2 u n' e)(*strict*)
  apply(subgoal_tac "Lemma6__2_Goal G (derivation_take d (Suc n')) n' e (\<gamma>@[teA B]) [] u \<gamma> B")
   apply(rename_tac d e2 u n' e)(*strict*)
   prefer 2
   apply(rule Lemma6__2)
         apply(rename_tac d e2 u n' e)(*strict*)
         apply(blast)
        apply(rename_tac d e2 u n' e)(*strict*)
        apply(blast)
       apply(rename_tac d e2 u n' e)(*strict*)
       apply(rule_tac cfgRM.derivation_take_preserves_derivation)
       apply(blast)
      apply(rename_tac d e2 u n' e)(*strict*)
      apply(rule_tac
      m="Suc 0"
      in cfgRM.derivation_take_preserves_generates_maximum_of_domain)
       apply(rename_tac d e2 u n' e)(*strict*)
       apply(blast)
      apply(rename_tac d e2 u n' e)(*strict*)
      apply(clarsimp)
     apply(rename_tac d e2 u n' e)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac d e2 u n' e)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d e2 u n' e)(*strict*)
   apply(blast)
  apply(rename_tac d e2 u n' e)(*strict*)
  apply(simp only: Lemma6__2_Goal_def)
  apply(clarsimp)
  apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(subgoal_tac "\<exists>\<alpha>''. \<alpha>'=\<alpha>''@[teA B]")
   apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   prefer 2
   apply(rule revTakeSuccessImpliesTailElem)
   apply(blast)
  apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta>' y' A' d'' m \<alpha>'')(*strict*)
  apply(rename_tac \<beta> y' A d'' m \<alpha>)
  apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
  apply(rule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = \<alpha> @ teA B # \<beta>\<rparr>"
      in bexI)
   apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
   apply(rule_tac
      x="A"
      in exI)
   apply(rule_tac
      x="\<alpha>"
      in exI)
   apply(rule_tac
      x="\<beta>"
      in exI)
   apply(rule conjI,blast)
   apply(rule_tac
      x="take k (filterB y')"
      in exI)
   apply(subgoal_tac "\<exists>v. v@y'=u")
    apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
    apply(rule_tac
      x="v"
      in exI)
    apply(rule conjI)
     apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
     apply(simp only: setAConcat concat_asso)
     apply(blast)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
    apply(rule_tac
      x="n'nonterminal"
      in exI)
    apply(rule conjI,arith)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
     prefer 2
     apply(rule conjI)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
      prefer 2
      apply(subgoal_tac "ord_class.min (k - length (filterB v)) k=(k - length (filterB v))")
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "take k (filterB v) = filterB (take k v)")
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(rule setATakeRestricted)
       apply(rule order_antisym)
        apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
        apply(rule_tac
      B="setA (take (k+length v) v)"
      in subset_trans)
         apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
         apply(rule setATakeIndexSubset)
        apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
        apply(rule_tac
      t="setA (take (k + length v) v)"
      and s="setA v"
      in ssubst)
         apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
         apply(rule_tac setATakeEQ)
        apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
        apply(clarsimp)
        apply(simp only: setAConcat concat_asso)
        apply(blast)
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
       apply(force)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
      apply(subgoal_tac " \<exists>z1 z2. take k v=liftB z1 \<and> take (k - length v) y'=liftB z2 \<and> z1@z2=z")
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
       prefer 2
       apply(rule liftBSplit)
       apply(blast)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
      apply(clarsimp)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
      apply(rule_tac
      s="z1"
      and t="filterB (liftB z1)"
      in ssubst)
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
       apply(rule liftBDeConv1)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "length (filterB v) = length v")
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "take (k - length v) (filterB y') = filterB (take (k - length v) y')")
        apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
        apply(clarsimp)
        prefer 2
        apply(rule setATakeRestricted)
        apply(rule order_antisym)
         apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
         apply(rule_tac
      B="setA (take ((k-length v)+length y') y')"
      in subset_trans)
          apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
          apply(rule setATakeIndexSubset)
         apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
         apply(rule_tac
      t="setA (take ((k-length v) + length y') y')"
      and s="setA y'"
      in ssubst)
          apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
          apply(rule_tac setATakeEQ)
         apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
         apply(clarsimp)
        apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
        apply(simp only: setAConcat concat_asso)
        apply(blast)
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
       apply(rule liftBDeConv1)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v z1 z2)(*strict*)
      apply(rule sym)
      apply(rule filterBLength)
      apply(simp only: setAConcat concat_asso)
      apply(blast)
     apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
     prefer 4
     apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
     apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = \<delta>' @ teA A # y'\<rparr> \<lparr>prod_lhs = A, prod_rhs = \<alpha> @ teA B # \<beta>\<rparr> \<lparr>cfg_conf = \<delta>' @ \<alpha> @ teA B # \<beta> @ y'\<rparr>")
      apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
      apply(simp add: cfgRM_step_relation_def)
     apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
     apply(rule_tac
      d="d'"
      in cfgRM.position_change_due_to_step_relation)
       apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
       apply(blast)
      apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
      apply(blast)
     apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
     apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = \<delta>' @ teA A # y'\<rparr> e2a \<lparr>cfg_conf = \<delta>' @ \<alpha> @ teA B # \<beta> @ y'\<rparr>")
      apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
      apply(clarsimp)
      apply(simp add: cfgRM_step_relation_def)
      apply(case_tac e2a)
      apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> prod_lhsa prod_rhsa)(*strict*)
      apply(clarsimp)
      apply(rename_tac d e2 u e d' n'nonterminal e1 e3 \<delta>' \<beta> y' A d'' m \<alpha> prod_lhs prod_rhs l r)(*strict*)
      apply(subgoal_tac "y'=r")
       apply(rename_tac d e2 u e d' n'nonterminal e1 e3 \<delta>' \<beta> y' A d'' m \<alpha> prod_lhs prod_rhs l r)(*strict*)
       apply(clarsimp)
      apply(rename_tac d e2 u e d' n'nonterminal e1 e3 \<delta>' \<beta> y' A d'' m \<alpha> prod_lhs prod_rhs l r)(*strict*)
      apply(rule_tac
      ?v1.0="\<delta>'"
      and ?v2.0="l"
      and A="A"
      and B="prod_lhs"
      in terminalTailEquals1)
        apply(rename_tac d e2 u e d' n'nonterminal e1 e3 \<delta>' \<beta> y' A d'' m \<alpha> prod_lhs prod_rhs l r)(*strict*)
        apply(clarsimp)
       apply(rename_tac d e2 u e d' n'nonterminal e1 e3 \<delta>' \<beta> y' A d'' m \<alpha> prod_lhs prod_rhs l r)(*strict*)
       apply(clarsimp)
      apply(rename_tac d e2 u e d' n'nonterminal e1 e3 \<delta>' \<beta> y' A d'' m \<alpha> prod_lhs prod_rhs l r)(*strict*)
      apply(clarsimp)
     apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
     apply(rule_tac
      d="d'"
      in cfgRM.position_change_due_to_step_relation)
       apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
       apply(blast)
      apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
      apply(blast)
     apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
     apply(blast)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
    prefer 3
    apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
    apply(subgoal_tac "\<exists>v e. d'' (0+m) = Some (pair e \<lparr>cfg_conf=v@y'\<rparr>)")
     apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
     prefer 2
     apply(rule TailTerminalStringsGrow)
        apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
        apply(rule cfgRM_derivations_are_cfg_derivations)
        apply(blast)
       apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
       apply(blast)
      apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
      apply(blast)
     apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
     apply(clarsimp)
    apply(rename_tac d e2 u e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
   apply(rule_tac
      x="derivation_map d'' ((\<lambda>v. \<lparr>cfg_conf=take (length(cfg_conf v)-(length y')) (cfg_conf v)\<rparr>))"
      in exI)
   apply(rule conjI)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
    apply(rule_tac
      P="\<lambda>c. \<exists>v. (cfg_conf c)=v@y'"
      in cfgRM.derivation_map_preserves_derivation)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
      apply(blast)
     apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v i ea c)(*strict*)
     apply(subgoal_tac " \<exists>v e. d'' (0+i) = Some (pair e \<lparr>cfg_conf=v@y'\<rparr>)")
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v c i ea)(*strict*)
      prefer 2
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v i ea c)(*strict*)
      apply(rule_tac
      d="d''"
      in TailTerminalStringsGrow)
         apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v c i ea)(*strict*)
         apply(rule cfgRM_derivations_are_cfg_derivations)
         apply(blast)
        apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v c i ea)(*strict*)
        apply(blast)
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v c i ea)(*strict*)
       apply(blast)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v c i ea)(*strict*)
      apply(clarsimp)
     apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v c i ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b)(*strict*)
    apply(case_tac a)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b cfg_confa)(*strict*)
    apply(case_tac b)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b cfg_confa cfg_confaa)(*strict*)
    apply(rename_tac ca cb)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b ca cb)(*strict*)
    apply(simp)
    apply(case_tac ea)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b ca cb prod_lhs prod_rhs)(*strict*)
    apply(erule exE)+
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b ca cb prod_lhs prod_rhs va vb)(*strict*)
    apply(rule_tac
      s="vb"
      and t="take (length cb - length y') cb"
      in ssubst)
     apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b ca cb prod_lhs prod_rhs va vb)(*strict*)
     prefer 2
     apply(rule_tac
      s="va"
      and t="take (length ca - length y') ca"
      in ssubst)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b ca cb prod_lhs prod_rhs va vb)(*strict*)
      prefer 2
      apply(simp add: cfgRM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v prod_lhs prod_rhs va vb l r)(*strict*)
      apply(rename_tac A' w' va vb l r)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v A' w' va vb l r)(*strict*)
      apply(subgoal_tac "\<exists>r'. r=r'@y'")
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v A' w' va vb l r)(*strict*)
       apply(clarsimp)
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v A' w' l r')(*strict*)
       apply(rule_tac
      x="l"
      in exI)
       apply(rule_tac
      x="r'"
      in exI)
       apply(clarsimp)
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v A' w' r')(*strict*)
       apply(simp only: setAConcat concat_asso)
       apply(blast)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v A' w' va vb l r)(*strict*)
      apply(rule_tac
      ?v1.0="l"
      and A="A'"
      and ?v2.0="va"
      and u="[]"
      in terminalTailEquals2)
        apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v A' w' va vb l r)(*strict*)
        apply(blast)
       apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v A' w' va vb l r)(*strict*)
       apply(blast)
      apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v A' w' va vb l r)(*strict*)
      apply(clarsimp)
     apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b ca cb prod_lhs prod_rhs va vb)(*strict*)
     apply(force)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v a ea b ca cb prod_lhs prod_rhs va vb)(*strict*)
    apply(force)
   apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(blast)
   apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(rule conjI)
   apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
   apply(blast)
  apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="liftB (take k (filterB y'))"
      and s="take k (liftB (filterB y'))"
      in ssubst)
   apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
   apply(rule sym)
   apply(rule take_liftB)
  apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
  apply(rule_tac
      t="liftB (filterB y')"
      and s="y'"
      in ssubst)
   apply(rename_tac d e2 e d' n'nonterminal e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha> v)(*strict*)
   apply(rule liftBDeConv2)
   apply(auto)
  done

lemma Lemma6__21: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> I \<in> valid_item_set_n G k n w
  \<Longrightarrow> valid_item G k I
  \<Longrightarrow> (n = 0 \<and> w = [] \<and> (\<exists>w. I = \<lparr>cfg_item_lhs = cfg_initial G, cfg_item_rhs1 = [], cfg_item_rhs2 = w, cfg_item_look_ahead = []\<rparr>)) \<or> (w \<noteq> [] \<and> I \<in> essential_items {I}) \<or> (n > 0 \<and> (\<exists>m < n. \<exists>I' \<in> valid_item_set_n G k m w . I \<in> (F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k I')))"
  apply(case_tac n)
   apply(clarsimp)
   apply(simp add: valid_item_set_n_def)
   apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
    apply(clarsimp)
    apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
    prefer 2
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
    apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
      apply(blast)+
   apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
   apply(subgoal_tac "\<delta>=[]")
    apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
    apply(subgoal_tac "z=[]")
     apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<alpha> \<beta> y d e)(*strict*)
     apply(simp add: essential_items_def)
     apply(rule liftB_reflects_Nil)
     apply(blast)
    apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
    apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
   apply(case_tac "\<delta>")
    apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
    apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> z e a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rule disjI2)
  apply(case_tac "w \<noteq> [] \<and> I \<in> essential_items {I}")
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(rule disjI2)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac nat)(*strict*)
   defer
   apply(simp add: essential_items_def)
   apply(erule_tac
      x="cfg_item_lhs I"
      in allE)
   apply(erule_tac
      x="cfg_item_rhs1 I"
      in allE)
   apply(erule disjE)
    apply(rename_tac nat)(*strict*)
    apply(erule_tac
      x="cfg_item_rhs2 I"
      in allE)
    apply(erule_tac
      x="cfg_item_look_ahead I"
      in allE)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(case_tac I)
   apply(rename_tac nat cfg_item_lhs cfg_item_rhs1a cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat cfg_item_lhs cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
   apply(rename_tac B w' z)
   apply(rename_tac nat B w' z)(*strict*)
   apply(subgoal_tac "\<exists>p \<in> (cfg_productions G). \<exists>A \<alpha> \<beta>. p=\<lparr>prod_lhs=A,prod_rhs=\<alpha>@[teA B]@\<beta>\<rparr> \<and> (\<exists>y v. setA v={} \<and> (\<exists>m<(Suc nat). \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>,cfg_item_rhs2 = [teA B]@\<beta>,cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k m w \<and> (\<exists>d e. cfgRM.derivation G d \<and> maximum_of_domain d ((Suc nat)-m-(1::nat)) \<and> d 0 = Some (pair None \<lparr>cfg_conf=\<beta>\<rparr>) \<and> d ((Suc nat)-m-(1::nat)) = Some (pair e \<lparr>cfg_conf=v\<rparr>) ) \<and> take k ((filterB v)@y) = z ))")
    apply(rename_tac nat B w' z)(*strict*)
    prefer 2
    apply(rule Lemma6_19)
      apply(rename_tac nat B w' z)(*strict*)
      apply(blast)
     apply(rename_tac nat B w' z)(*strict*)
     apply(blast)
    apply(rename_tac nat B w' z)(*strict*)
    apply(blast)
   apply(rename_tac nat B w' z)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule_tac
      x="m"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teA B # \<beta>, cfg_item_look_ahead = y\<rparr>"
      in bexI)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
    apply(rule disjI2)
    apply(rule conjI)
     apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
     apply(simp add: valid_item_def)
     apply(clarsimp)
     apply(rename_tac nat A \<alpha> \<beta> y v m d e p)(*strict*)
     apply(case_tac p)
     apply(rename_tac nat A \<alpha> \<beta> y v m d e p prod_lhsa prod_rhsa)(*strict*)
     apply(force)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    prefer 2
    apply(blast)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule_tac
      t="length (filterB v)"
      and s="length v"
      in ssubst)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule sym)
    apply(rule filterBLength)
    apply(blast)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule_tac
      t="liftB (take k (filterB v) @ take (k - length v) y)"
      and s="liftB (take k (filterB v)) @ (liftB (take (k - length v) y))"
      in ssubst)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule_tac
      t="liftB (take k (filterB v))"
      and s=" (take k (liftB (filterB v)))"
      in ssubst)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule sym)
    apply(rule take_liftB)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule_tac
      s="v"
      and t=" ((liftB (filterB v)))"
      in ssubst)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule liftBDeConv2)
    apply(blast)
   apply(rule in_cfgSTD_first__implies__in_cfgSTD_first)
       apply(force)
      apply(force)
     apply(subgoal_tac "valid_item G k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>,
          cfg_item_rhs2 = teA B # \<beta>, cfg_item_look_ahead = y\<rparr>")
      prefer 2
      apply(rule valid_item_set_n_contains_items)
       apply(force)
      apply(force)
     apply(simp add: valid_item_def simpY valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac x="p" in ballE)
      prefer 2
      apply(force)
     apply(simp add: valid_item_def simpY valid_cfg_def)
     apply(force)
    apply(subgoal_tac "valid_item G k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>,
          cfg_item_rhs2 = teA B # \<beta>, cfg_item_look_ahead = y\<rparr>")
     prefer 2
     apply(rule valid_item_set_n_contains_items)
      apply(force)
     apply(force)
    apply(simp add: valid_item_def simpY valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="p" in ballE)
     prefer 2
     apply(force)
    apply(simp add: valid_item_def simpY valid_cfg_def)
    apply(force)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(simp add: cfgSTD_first_def)
   apply(rule inMap)
   apply(clarsimp)
   apply(rule_tac
      x="filterB v@y"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rule_tac
      s="length v"
      and t="length (filterB v)"
      in ssubst)
     apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
     apply(rule sym)
     apply(rule filterB_reflects_length)
     apply(blast)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(blast)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule_tac
      x="derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ (liftB y)\<rparr>)"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule cfgSTD.derivation_map_preserves_derivation2)
     apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(blast)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule cfgSTD_step_relation_closed_under_post_context)
     apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
     apply(clarsimp)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(blast)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="nat-m"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(blast)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(simp add: derivation_map_def)
   apply(rule_tac
      t="liftB (filterB v @ y)"
      and s="liftB (filterB v)@(liftB y)"
      in ssubst)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule_tac
      t="liftB (filterB v)"
      and s="v"
      in ssubst)
    apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule liftBDeConv2)
    apply(blast)
   apply(rename_tac nat B w' A \<alpha> \<beta> y v m d e)(*strict*)
   apply(blast)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "cfg_item_rhs1 I=[]")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(simp add: valid_item_set_n_def)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac I)
  apply(rename_tac nat cfg_item_lhs cfg_item_rhs1a cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat cfg_item_lhs cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
  apply(rename_tac n B w z)
  apply(rename_tac n B w z)(*strict*)
  apply(subgoal_tac "\<exists>p \<in> (cfg_productions G). \<exists>A \<alpha> \<beta>. p=\<lparr>prod_lhs=A,prod_rhs=\<alpha>@[teA B]@\<beta>\<rparr> \<and> (\<exists>y v. setA v={} \<and> (\<exists>m<(Suc n). \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>,cfg_item_rhs2 = [teA B]@\<beta>,cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k m [] \<and> (\<exists>d e. cfgRM.derivation G d \<and> maximum_of_domain d ((Suc n)-m-(1::nat)) \<and> d 0 = Some (pair None \<lparr>cfg_conf=\<beta>\<rparr>) \<and> d ((Suc n)-m-(1::nat)) = Some (pair e \<lparr>cfg_conf=v\<rparr>) ) \<and> take k ((filterB v)@y) = z ))")
   apply(rename_tac n B w z)(*strict*)
   prefer 2
   apply(rule Lemma6_19)
     apply(rename_tac n B w z)(*strict*)
     apply(blast)
    apply(rename_tac n B w z)(*strict*)
    apply(blast)
   apply(rename_tac n B w z)(*strict*)
   apply(force)
  apply(rename_tac n B w z)(*strict*)
  apply(clarsimp)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule_tac
      x="m"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x=" \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teA B # \<beta>, cfg_item_look_ahead = y\<rparr>"
      in bexI)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
   apply(rule disjI2)
   apply(rule conjI)
    apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
    apply(simp add: valid_item_def)
    apply(clarsimp)
    apply(rename_tac n A \<alpha> \<beta> y v m d e p)(*strict*)
    apply(case_tac p)
    apply(rename_tac n A \<alpha> \<beta> y v m d e p prod_lhsa prod_rhsa)(*strict*)
    apply(force)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule_tac
      t="length (filterB v)"
      and s="length v"
      in ssubst)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule sym)
   apply(rule filterBLength)
   apply(blast)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule_tac
      t="liftB (take k (filterB v) @ take (k - length v) y)"
      and s="liftB (take k (filterB v)) @ (liftB (take (k - length v) y))"
      in ssubst)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule liftB_commutes_over_concat)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule_tac
      t="liftB (take k (filterB v))"
      and s=" (take k (liftB (filterB v)))"
      in ssubst)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule sym)
   apply(rule take_liftB)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule_tac
      s="v"
      and t=" ((liftB (filterB v)))"
      in ssubst)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule liftBDeConv2)
   apply(blast)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule in_cfgSTD_first__implies__in_cfgSTD_first)
      apply(force)
     apply(force)
    apply(subgoal_tac "valid_item G k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>,
          cfg_item_rhs2 = teA B # \<beta>, cfg_item_look_ahead = y\<rparr>")
     prefer 2
     apply(rule valid_item_set_n_contains_items)
      apply(force)
     apply(force)
    apply(simp add: valid_item_def simpY valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="p" in ballE)
     prefer 2
     apply(force)
    apply(simp add: valid_item_def simpY valid_cfg_def)
    apply(force)
   apply(subgoal_tac "valid_item G k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>,
          cfg_item_rhs2 = teA B # \<beta>, cfg_item_look_ahead = y\<rparr>")
    prefer 2
    apply(rule valid_item_set_n_contains_items)
     apply(force)
    apply(force)
   apply(simp add: valid_item_def simpY valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac x="p" in ballE)
    prefer 2
    apply(force)
   apply(simp add: valid_item_def simpY valid_cfg_def)
   apply(force)
  apply(simp add: cfgSTD_first_def)
  apply(rule inMap)
  apply(clarsimp)
  apply(rule_tac
      x="filterB v@y"
      in exI)
  apply(rule conjI)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule_tac
      t="length (filterB v)"
      and s="length v"
      in ssubst)
    apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule sym)
    apply(rule filterBLength)
    apply(blast)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(blast)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule_tac
      x="derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ (liftB y)\<rparr>)"
      in exI)
  apply(rule conjI)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule cfgSTD.derivation_map_preserves_derivation2)
    apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
    apply(rule cfgRM_derivations_are_cfg_derivations)
    apply(blast)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule cfgSTD_step_relation_closed_under_post_context)
    apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
    apply(clarsimp)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(blast)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="n-m"
      in exI)
  apply(rule conjI)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(blast)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule conjI)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rule_tac
      t="liftB (filterB v @ y)"
      and s="liftB (filterB v)@(liftB y)"
      in ssubst)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule liftB_commutes_over_concat)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(rule_tac
      t="liftB (filterB v)"
      and s="v"
      in ssubst)
   apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
   apply(rule liftBDeConv2)
   apply(blast)
  apply(rename_tac n B w A \<alpha> \<beta> y v m d e)(*strict*)
  apply(blast)
  done

lemma Lemma6__22: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> setA \<gamma> \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB \<gamma> \<subseteq> cfg_events G
  \<Longrightarrow> if \<gamma> = [] then valid_item_set_n G k n \<gamma> \<subseteq> F_VALID_ITEM_SET_INITIAL G F k else valid_item_set_n G k n \<gamma> \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k \<gamma>))"
  apply(rule_tac
      n="n"
      in nat_less_induct)
  apply(rename_tac n)(*strict*)
  apply(case_tac n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(case_tac \<gamma>)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rename_tac I)
    apply(rename_tac I)(*strict*)
    apply(subgoal_tac "valid_item G k I")
     apply(rename_tac I)(*strict*)
     apply(subgoal_tac "(0=0 \<and> []=[] \<and> (\<exists>w. I= \<lparr>cfg_item_lhs = cfg_initial G,cfg_item_rhs1 = [],cfg_item_rhs2 = w,cfg_item_look_ahead = []\<rparr>)) \<or> ([]\<noteq>[] \<and> I \<in> essential_items {I}) \<or> (0>0 \<and> (\<exists>m<0. \<exists>I' \<in> (valid_item_set_n G k m []). I \<in> (F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k I')))")
      apply(rename_tac I)(*strict*)
      prefer 2
      apply(rule Lemma6__21)
           apply(rename_tac I)(*strict*)
           apply(force)+
     apply(rename_tac I)(*strict*)
     prefer 2
     apply(rule Fact6_12__2)
      apply(rename_tac I)(*strict*)
      apply(blast)+
     apply(rename_tac I)(*strict*)
     apply(simp add: valid_item_set_def)
     apply(rule_tac
      x="0"
      in exI)
     apply(blast)
    apply(rename_tac I)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
    apply(rule_tac
      A="(F_VALID_ITEM_SET_INITIAL__fp_start G)"
      in set_mp)
     apply(rename_tac w)(*strict*)
     prefer 2
     apply(simp add: F_VALID_ITEM_SET_INITIAL__fp_start_def)
     apply(rule_tac
      x="\<lparr>prod_lhs=cfg_initial G,prod_rhs=w\<rparr>"
      in exI)
     apply(rename_tac w)(*strict*)
     apply(simp add: valid_item_def)
     apply(clarsimp)
     apply(rename_tac p)(*strict*)
     apply(case_tac p)
     apply(rename_tac p prod_lhsa prod_rhsa)(*strict*)
     apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
      apply(rename_tac w)(*strict*)
      apply(blast)
     apply(rename_tac w)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_INITIAL__fp_start_def)
     apply(clarsimp)
     apply(rename_tac w p)(*strict*)
     apply(simp add: valid_item_def)
     apply(clarsimp)
     apply(rename_tac p pa)(*strict*)
     apply(rule_tac
      x="p"
      in bexI)
      apply(rename_tac p pa)(*strict*)
      apply(clarsimp)
     apply(rename_tac p pa)(*strict*)
     apply(blast)
    apply(blast)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a list x)(*strict*)
   apply(rename_tac a w I)
   apply(rename_tac a w I)(*strict*)
   apply(subgoal_tac "valid_item G k I")
    apply(rename_tac a w I)(*strict*)
    apply(subgoal_tac "(0=0 \<and> a#w=[] \<and> (\<exists>w. I= \<lparr>cfg_item_lhs = cfg_initial G,cfg_item_rhs1 = [],cfg_item_rhs2 = w,cfg_item_look_ahead = []\<rparr>)) \<or> (a#w\<noteq>[] \<and> I \<in> essential_items {I}) \<or> (0>0 \<and> (\<exists>m<0. \<exists>I' \<in> (valid_item_set_n G k m (a#w)). I \<in> (F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k I')))")
     apply(rename_tac a w I)(*strict*)
     prefer 2
     apply(rule_tac
      w="a#w"
      and n="0"
      in Lemma6__21)
          apply(rename_tac a w I)(*strict*)
          apply(force)
         apply(force)
        apply(rename_tac a w I)(*strict*)
        apply(simp add: setA_def)
       apply(rename_tac a w I)(*strict*)
       apply(clarsimp)
      apply(rename_tac a w I)(*strict*)
      apply(clarsimp)
     apply(rename_tac a w I)(*strict*)
     apply(blast)
    apply(rename_tac a w I)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "cfg_item_rhs1 I\<noteq>[]")
     apply(rename_tac a w I)(*strict*)
     prefer 2
     apply(simp add: essential_items_def)
     apply(clarsimp)
    apply(rename_tac a w I)(*strict*)
    apply(thin_tac "I \<in> essential_items {I}")
    apply(rule_tac
      A="(essential_items (valid_item_set G k (a # w)))"
      in set_mp)
     apply(rename_tac a w I)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
       apply(rename_tac a w I)(*strict*)
       apply(blast)
      apply(rename_tac a w I)(*strict*)
      apply(rule_tac
      B="valid_item_set G k (a # w)"
      in subset_trans)
       apply(rename_tac a w I)(*strict*)
       apply(simp add: essential_items_def)
       apply(force)
      apply(rename_tac a w I)(*strict*)
      apply(clarsimp)
      apply(rename_tac a w I x)(*strict*)
      apply(rule Fact6_12__2)
       apply(rename_tac a w I x)(*strict*)
       apply(blast)
      apply(rename_tac a w I x)(*strict*)
      apply(blast)
     apply(force)
    apply(rename_tac a w I)(*strict*)
    apply(simp add: essential_items_def)
    apply(rule conjI)
     apply(rename_tac a w I)(*strict*)
     apply(simp add: valid_item_set_def)
     apply(force)
    apply(rename_tac a w I)(*strict*)
    apply(case_tac I)
    apply(rename_tac a w I cfg_item_lhs cfg_item_rhs1a cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
    apply(force)
   apply(rename_tac a w I)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac a w I)(*strict*)
    apply(blast)+
   apply(rename_tac a w I)(*strict*)
   apply(simp add: valid_item_set_def)
   apply(force)
  apply(rename_tac n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "valid_item_set_n G k (Suc n) \<gamma> \<subseteq> (if \<gamma>=[] then (F_VALID_ITEM_SET_INITIAL G F k) else (F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k \<gamma>))))")
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(rule subsetI)
  apply(rename_tac n x)(*strict*)
  apply(rename_tac I)
  apply(rename_tac n I)(*strict*)
  apply(subgoal_tac "valid_item G k I")
   apply(rename_tac n I)(*strict*)
   apply(subgoal_tac "(Suc n=0 \<and> \<gamma>=[] \<and> (\<exists>w. I= \<lparr>cfg_item_lhs = cfg_initial G,cfg_item_rhs1 = [],cfg_item_rhs2 = w,cfg_item_look_ahead = []\<rparr>)) \<or> (\<gamma>\<noteq>[] \<and> I \<in> essential_items {I}) \<or> (Suc n>0 \<and> (\<exists>m<Suc n. \<exists>I' \<in> (valid_item_set_n G k m \<gamma>). I \<in> (F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k I')))")
    apply(rename_tac n I)(*strict*)
    prefer 2
    apply(rule Lemma6__21)
         apply(rename_tac n I)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac n I)(*strict*)
       apply(force)
      apply(rename_tac n I)(*strict*)
      apply(force)
     apply(rename_tac n I)(*strict*)
     apply(force)
    apply(rename_tac n I)(*strict*)
    apply(rule Fact6_12__2)
     apply(rename_tac n I)(*strict*)
     apply(clarsimp)
    apply(rename_tac n I)(*strict*)
    apply(simp add: valid_item_set_def)
    apply(force)
   apply(rename_tac n I)(*strict*)
   prefer 2
   apply(rule Fact6_12__2)
    apply(rename_tac n I)(*strict*)
    apply(blast)+
   apply(rename_tac n I)(*strict*)
   apply(simp add: valid_item_set_def)
   apply(force)
  apply(rename_tac n I)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac n I)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "cfg_item_rhs1 I\<noteq>[]")
    apply(rename_tac n I)(*strict*)
    prefer 2
    apply(simp add: essential_items_def)
    apply(force)
   apply(rename_tac n I)(*strict*)
   apply(thin_tac "I \<in> essential_items {I}")
   apply(rule_tac
      A="(essential_items (valid_item_set G k \<gamma>))"
      in set_mp)
    apply(rename_tac n I)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
      apply(rename_tac n I)(*strict*)
      apply(blast)
     apply(rename_tac n I)(*strict*)
     apply(rule_tac
      B="valid_item_set G k \<gamma>"
      in subset_trans)
      apply(rename_tac n I)(*strict*)
      apply(simp add: essential_items_def)
      apply(force)
     apply(rename_tac n I)(*strict*)
     apply(clarsimp)
     apply(rename_tac n I x)(*strict*)
     apply(rule Fact6_12__2)
      apply(rename_tac n I x)(*strict*)
      apply(blast)
     apply(rename_tac n I x)(*strict*)
     apply(blast)
    apply(force)
   apply(rename_tac n I)(*strict*)
   apply(simp add: essential_items_def)
   apply(rule conjI)
    apply(rename_tac n I)(*strict*)
    apply(simp add: valid_item_set_def)
    apply(force)
   apply(rename_tac n I)(*strict*)
   apply(case_tac I)
   apply(rename_tac n I cfg_item_lhs cfg_item_rhs1a cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
   apply(force)
  apply(rename_tac n I)(*strict*)
  apply(clarsimp)
  apply(rename_tac n I m I')(*strict*)
  apply(rename_tac J)
  apply(rename_tac n I m J)(*strict*)
  apply(erule_tac
      x="m"
      in allE)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac n I m J)(*strict*)
   apply(clarsimp)
   apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
   apply(subgoal_tac "J \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G)")
    apply(rename_tac n I m J)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n I m J)(*strict*)
   apply(thin_tac "J \<in> valid_item_set_n G k m []")
   apply(thin_tac "valid_item_set_n G k m [] \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G)")
   apply(thin_tac " I \<in> valid_item_set_n G k (Suc n) []")
   apply(thin_tac "valid_item G k I")
   apply(thin_tac "m < Suc n")
   apply(rule immediate_decendant_also_in_F_VALID_ITEM_SET_GOTO__descent__fp)
       apply(rename_tac n I m J)(*strict*)
       apply(blast)
      apply(force)
     apply(rename_tac n I m J)(*strict*)
     apply(blast)
    apply(rename_tac n I m J)(*strict*)
    apply(blast)
   apply(rename_tac n I m J)(*strict*)
   apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
  apply(rename_tac n I m J)(*strict*)
  apply(clarsimp)
  apply(rule immediate_decendant_also_in_F_VALID_ITEM_SET_GOTO__descent__fp)
      apply(rename_tac n I m J)(*strict*)
      apply(blast)
     apply(force)
    apply(rename_tac n I m J)(*strict*)
    apply(blast)
   apply(rename_tac n I m J)(*strict*)
   apply(blast)
  apply(rename_tac n I m J)(*strict*)
  apply(subgoal_tac "valid_item_set G k \<gamma> \<subseteq> Collect (valid_item G k)")
   apply(rename_tac n I m J)(*strict*)
   apply(subgoal_tac "essential_items (valid_item_set G k \<gamma>) \<subseteq> valid_item_set G k \<gamma>")
    apply(rename_tac n I m J)(*strict*)
    apply(force)
   apply(rename_tac n I m J)(*strict*)
   apply(simp add: essential_items_def)
   apply(force)
  apply(rename_tac n I m J)(*strict*)
  apply(simp add: valid_item_set_def)
  apply(rule subsetI)
  apply(rename_tac n I m J x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n I m J x na)(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac n I m J x na)(*strict*)
   apply(blast)+
  apply(rename_tac n I m J x na)(*strict*)
  apply(simp add: valid_item_set_def)
  apply(force)
  done

lemma Lemma6__18: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp G F k (valid_item_set G k \<gamma>) = valid_item_set G k \<gamma>"
  apply(rule_tac
      s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (valid_item_set G k \<gamma>) = (valid_item_set G k \<gamma>) then (valid_item_set G k \<gamma>) else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (valid_item_set G k \<gamma>)))"
      and t="F_VALID_ITEM_SET_GOTO__descent__fp G F k (valid_item_set G k \<gamma>)"
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(clarsimp)
   apply(rule Fact6_12__2)
    apply(rename_tac x)(*strict*)
    apply(blast,blast)
  apply(clarsimp)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k (valid_item_set G k \<gamma>) = valid_item_set G k \<gamma>")
   apply(blast)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_idemp_on_valid_item_set)
   apply(blast)
  apply(blast)
  done

lemma Lemma6__23: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> setA \<gamma> \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB \<gamma> \<subseteq> cfg_events G
  \<Longrightarrow> valid_item_set G k \<gamma> = (if \<gamma> = [] then F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL G F k) else F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k \<gamma>)))"
  apply(case_tac "\<gamma>=[]")
   apply(clarsimp)
   defer
   apply(clarsimp)
   defer
   apply(rule order_antisym)
    apply(simp add: valid_item_set_def)
    apply(clarsimp)
    apply(rename_tac x n)(*strict*)
    apply(rule_tac
      A="valid_item_set_n G k n []"
      in set_mp)
     apply(rename_tac x n)(*strict*)
     apply(rule_tac
      B="F_VALID_ITEM_SET_INITIAL G F k"
      in subset_trans)
      apply(rename_tac x n)(*strict*)
      apply(subgoal_tac "if []=[] then (valid_item_set_n G k n [] \<subseteq> F_VALID_ITEM_SET_INITIAL G F k) else (valid_item_set_n G k n [] \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k [])))")
       apply(rename_tac x n)(*strict*)
       prefer 2
       apply(rule Lemma6__22)
          apply(rename_tac x n)(*strict*)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(rename_tac x n)(*strict*)
      apply(clarsimp)
     apply(rename_tac x n)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
       apply(rename_tac x n)(*strict*)
       apply(blast)
      apply(rename_tac x n)(*strict*)
      apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
      apply(subgoal_tac "Ball (F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G)) (valid_item G k)")
       apply(rename_tac x n)(*strict*)
       apply(blast)
      apply(rename_tac x n)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02_unfold)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
     apply(rename_tac x n)(*strict*)
     apply(blast)
    apply(force)
   apply(rule_tac
      B="F_VALID_ITEM_SET_INITIAL G F k"
      in subset_trans)
    apply(simp only: F_VALID_ITEM_SET_INITIAL_def)
    apply(rule equalityD1)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_idemp)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
   apply(simp only: F_VALID_ITEM_SET_INITIAL_def)
   apply(rule_tac
      t = "valid_item_set G k []"
      and s = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (valid_item_set G k [])"
      in ssubst)
    apply(rule sym)
    apply(rule Lemma6__18)
     apply(blast)
    apply(force)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono2)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: valid_item_set_def)
    apply(clarsimp)
    apply(rename_tac x n)(*strict*)
    apply(rule Fact6_12__2)
     apply(rename_tac x n)(*strict*)
     apply(blast)
    apply(rename_tac x n)(*strict*)
    apply(simp add: valid_item_set_def)
    apply(force)
   apply(rule_tac
      B="valid_item_set G k []"
      in subset_trans)
    apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_is_valid_item_set)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
     apply(blast)
    apply(clarsimp)
    apply(rule Fact6_12__2)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(rule order_antisym)
   apply(simp add: valid_item_set_def)
   apply(clarsimp)
   apply(rename_tac x n)(*strict*)
   apply(rule_tac
      A="valid_item_set_n G k n \<gamma>"
      in set_mp)
    apply(rename_tac x n)(*strict*)
    apply(subgoal_tac "if \<gamma>=[] then (valid_item_set_n G k n \<gamma> \<subseteq> F_VALID_ITEM_SET_INITIAL G F k) else (valid_item_set_n G k n \<gamma> \<subseteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k \<gamma>)))")
     apply(rename_tac x n)(*strict*)
     prefer 2
     apply(rule Lemma6__22)
        apply(rename_tac x n)(*strict*)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(rename_tac x n)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n xa)(*strict*)
    apply(simp add: valid_item_set_def)
    apply(force)
   apply(rename_tac x n)(*strict*)
   apply(blast)
  apply(rule_tac
      P="\<lambda>x. F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k \<gamma>)) \<subseteq> x"
      and t = "valid_item_set G k \<gamma>"
      and s = "F_VALID_ITEM_SET_GOTO__descent__fp G F k (valid_item_set G k \<gamma>)"
      in ssubst)
   apply(rule sym)
   apply(rule Lemma6__18)
    apply(blast)
   apply(force)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono2)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: valid_item_set_def)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule Fact6_12__2)
     apply(rename_tac x)(*strict*)
     apply(blast)
    apply(rename_tac x)(*strict*)
    apply(simp add: valid_item_set_def essential_items_def)
    apply(force)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(simp add: valid_item_set_def)
   apply(clarsimp)
   apply(rename_tac x n)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac x n)(*strict*)
    apply(blast)
   apply(rename_tac x n)(*strict*)
   apply(simp add: valid_item_set_def essential_items_def)
   apply(force)
  apply(rule_tac
      B="valid_item_set G k \<gamma>"
      in subset_trans)
   apply(simp add: essential_items_def)
   apply(blast)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
    apply(blast)
   prefer 2
   apply(force)
  apply(simp add: valid_item_set_def)
  apply(clarsimp)
  apply(rename_tac x n)(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac x n)(*strict*)
   apply(blast)
  apply(rename_tac x n)(*strict*)
  apply(simp add: valid_item_set_def)
  apply(force)
  done

lemma Lemma6__23_1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_item_set G k [] = F_VALID_ITEM_SET_INITIAL G F k"
  apply(rule_tac
      t="valid_item_set G k []"
      and s="(if SSrenGAMMA = [] then F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk (F_VALID_ITEM_SET_INITIAL SSG SSF SSk) else F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk (essential_items (valid_item_set SSG SSk SSrenGAMMA)))" for SSG SSk SSrenGAMMA SSF
      in ssubst)
   apply(rule Lemma6__23)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
  apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_idemp)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
  done

lemma Lemma6__24_3: "
  \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha> @ \<omega>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k n \<delta>
  \<Longrightarrow> \<exists>\<gamma>. viable_prefix G \<gamma> \<and> \<delta> = \<gamma> @ \<omega> \<and> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<omega> @ \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k n \<gamma>"
  apply(simp add: valid_item_set_n_def)
  apply(auto)
   apply(rename_tac d \<delta> e1 e2 z)(*strict*)
   apply(simp add: viable_prefix_def)
   apply(auto)
  apply(rename_tac d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(auto)
  apply(rule_tac
      x="n"
      in exI)
  apply(auto)
  apply(rule_tac
      x="\<alpha>"
      in exI)
  apply(rule_tac
      x="\<omega>@\<beta>"
      in exI)
  apply(rule_tac
      x="z"
      in exI)
  apply(rule_tac
      x="A"
      in exI)
  apply(rule_tac
      x="\<delta>"
      in exI)
  apply(auto)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac d \<delta> e1 e2 z)(*strict*)
     apply(blast)
    apply(rename_tac d \<delta> e1 e2 z)(*strict*)
    apply(blast)
   apply(rename_tac d \<delta> e1 e2 z)(*strict*)
   apply(arith)
  apply(rename_tac d \<delta> e1 e2 z)(*strict*)
  apply(force)
  done

lemma Lemma6__24_2: "
  \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<omega> @ \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k n \<gamma>
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha> @ \<omega>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k n (\<gamma> @ \<omega>)"
  apply(simp add: valid_item_set_n_def)
  done

lemma Lemma6__25: "
  valid_cfg G
  \<Longrightarrow> setA (\<gamma> @ [X]) \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB (\<gamma> @ [X]) \<subseteq> cfg_events G
  \<Longrightarrow> essential_items (valid_item_set G k (\<gamma> @ [X])) = F_VALID_ITEM_SET_GOTO__basis X (valid_item_set G k \<gamma>)"
  apply(rule order_antisym)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(rename_tac I)
   apply(rename_tac I)(*strict*)
   apply(simp add: essential_items_def)
   apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> y)(*strict*)
   apply(simp add: valid_item_set_def)
   apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> y n)(*strict*)
   apply(subgoal_tac "\<exists>\<alpha>' X. \<alpha>=\<alpha>'@[X]")
    apply(rename_tac A \<alpha> \<beta> y n)(*strict*)
    apply(erule exE)+
    apply(rename_tac A \<alpha> \<beta> y n \<alpha>' Xa)(*strict*)
    apply(subgoal_tac "\<exists>\<gamma>'. viable_prefix G \<gamma>' \<and> (\<gamma>@[X]=\<gamma>'@[Xa]) \<and> \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>',cfg_item_rhs2 = [Xa]@\<beta>,cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k n \<gamma>'")
     apply(rename_tac A \<alpha> \<beta> y n \<alpha>' Xa)(*strict*)
     prefer 2
     apply(rule Lemma6__24_3)
     apply(force)
    apply(rename_tac A \<alpha> \<beta> y n \<alpha>' Xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac A \<beta> y n \<alpha>')(*strict*)
    apply(simp only: F_VALID_ITEM_SET_GOTO__basis_def)
    apply(clarsimp)
    apply(rule_tac
      x="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>', cfg_item_rhs2 = X # \<beta>, cfg_item_look_ahead = y\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac A \<beta> y n \<alpha>')(*strict*)
     apply(force)
    apply(rename_tac A \<beta> y n \<alpha>')(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
   apply(rename_tac A \<alpha> \<beta> y n)(*strict*)
   apply(rule emptyString)
   apply(blast)
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(case_tac x)
  apply(rename_tac x cfg_item_lhs cfg_item_rhs1 cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
  apply(rename_tac A \<alpha> \<beta> y)
  apply(rename_tac x A \<alpha> \<beta> y)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(clarsimp)
  apply(rename_tac \<beta> I1)(*strict*)
  apply(simp add: valid_item_set_def)
  apply(clarsimp)
  apply(rename_tac \<beta> I1 n)(*strict*)
  apply(case_tac I1)
  apply(rename_tac \<beta> I1 n cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<beta> n cfg_item_lhs cfg_item_rhs1 cfg_item_look_ahead)(*strict*)
  apply(rename_tac \<beta> n A \<alpha> y)
  apply(rename_tac \<beta> n A \<alpha> y)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>@[X],cfg_item_rhs2 = \<beta>,cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k n (\<gamma>@[X])")
   apply(rename_tac \<beta> n A \<alpha> y)(*strict*)
   prefer 2
   apply(rule Lemma6__24_2)
   apply(force)
  apply(rename_tac \<beta> n A \<alpha> y)(*strict*)
  apply(simp add: essential_items_def)
  apply(force)
  done

theorem Lemma6__26: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> setA (\<gamma> @ [X]) \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB (\<gamma> @ [X]) \<subseteq> cfg_events G
  \<Longrightarrow> valid_item_set G k (\<gamma> @ [X]) = F_VALID_ITEM_SET_GOTO G F k X (valid_item_set G k \<gamma>)"
  apply(simp only: F_VALID_ITEM_SET_GOTO_def)
  apply(rule_tac
      s="essential_items (valid_item_set G k (\<gamma>@[X]))"
      and t="F_VALID_ITEM_SET_GOTO__basis X (valid_item_set G k \<gamma>)"
      in ssubst)
   apply(rule sym)
   apply(rule Lemma6__25)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(rule_tac
      P="\<lambda>x. x=F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k (\<gamma> @ [X])))"
      and s="(if (\<gamma>@[X])=[] then F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL G F k) else F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k (\<gamma>@[X]))) )"
      and t="valid_item_set G k (\<gamma>@[X])"
      in ssubst)
   apply(rule Lemma6__23)
      apply(blast)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(clarsimp)
  done

lemma Fact6_20: "
  valid_cfg G
  \<Longrightarrow> valid_item_set_n G k 0 \<gamma> = {I. \<exists>p \<in> cfg_productions G. \<exists>w. prod_lhs p = cfg_initial G \<and> cfg_item_lhs I = cfg_initial G \<and> cfg_item_rhs1 I = \<gamma> \<and> cfg_item_rhs2 I = w \<and> cfg_item_look_ahead I = [] \<and> prod_rhs p = \<gamma> @ w}"
  apply(simp add: valid_item_set_n_def)
  apply(auto)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
    apply(clarsimp)
    apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
    prefer 2
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
    apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
      apply(blast)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
     apply(blast)
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
    apply(arith)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
   apply(subgoal_tac "\<delta>=[]")
    apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
    apply(subgoal_tac "z=[]")
     apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<alpha> \<beta> y d e)(*strict*)
     apply(subgoal_tac "y=[]")prefer 2
      apply(rename_tac \<alpha> \<beta> y d e)(*strict*)
      apply(rule liftB_reflects_Nil)
      apply(blast)
     apply(rename_tac \<alpha> \<beta> y d e)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<alpha> \<beta> d e)(*strict*)
     apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> e \<lparr>cfg_conf = \<alpha>@\<beta>\<rparr>")
      apply(rename_tac \<alpha> \<beta> d e)(*strict*)
      prefer 2
      apply(rule cfgRM.position_change_due_to_step_relation)
        apply(rename_tac \<alpha> \<beta> d e)(*strict*)
        apply(blast)+
     apply(rename_tac \<alpha> \<beta> d e)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(rule_tac
      x="e"
      in bexI)
      apply(rename_tac \<alpha> \<beta> d e)(*strict*)
      apply(clarsimp)
      apply(rename_tac \<alpha> \<beta> d e l r)(*strict*)
      apply(subgoal_tac "l=[]")
       apply(rename_tac \<alpha> \<beta> d e l r)(*strict*)
       apply(subgoal_tac "r=[]")
        apply(rename_tac \<alpha> \<beta> d e l r)(*strict*)
        apply(clarsimp)
       apply(rename_tac \<alpha> \<beta> d e l r)(*strict*)
       apply(clarsimp)
      apply(rename_tac \<alpha> \<beta> d e l r)(*strict*)
      apply(case_tac l)
       apply(rename_tac \<alpha> \<beta> d e l r)(*strict*)
       apply(clarsimp)
      apply(rename_tac \<alpha> \<beta> d e l r a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac \<alpha> \<beta> d e)(*strict*)
     apply(force)
    apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
    apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
   apply(case_tac "\<delta>")
    apply(rename_tac A \<alpha> \<beta> y d \<delta> z e)(*strict*)
    apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> z e a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x p)(*strict*)
  apply(case_tac x)
  apply(rename_tac x p cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
  apply(clarsimp)
  apply(rename_tac p cfg_item_rhs1 cfg_item_rhs2)(*strict*)
  apply(rename_tac w1 w2)
  apply(rename_tac p w1 w2)(*strict*)
  apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> p \<lparr>cfg_conf = w1 @ w2\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac p w1 w2)(*strict*)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(force)
  apply(rename_tac p w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac p w1 w2)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac p w1 w2)(*strict*)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="Some p"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac p w1 w2)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac p w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac p w1 w2)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac p w1 w2)(*strict*)
  apply(rule der2_maximum_of_domain)
  done

lemma Fact6_1: "
  valid_cfg G
  \<Longrightarrow> viable_prefix G w
  \<Longrightarrow> \<exists>v. complete_viable_prefix G (w @ v)"
  apply(simp add: viable_prefix_def complete_viable_prefix_def)
  apply(auto)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule_tac
      x="\<beta>"
      in exI)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="\<alpha>@\<beta>"
      in exI)
  apply(rule_tac
      x="y"
      in exI)
  apply(rule_tac
      x="A"
      in exI)
  apply(rule_tac
      x="\<delta>"
      in exI)
  apply(clarsimp)
  done

theorem Fact6_12__1: "
  I \<in> valid_item_set G k \<gamma>
  \<Longrightarrow> viable_prefix G \<gamma>"
  apply(simp add: valid_item_set_def)
  apply(simp add: valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(simp add: viable_prefix_def)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="\<alpha>"
      in exI)
  apply(rule_tac
      x="\<beta>"
      in exI)
  apply(rule_tac
      x="z"
      in exI)
  apply(rule_tac
      x="A"
      in exI)
  apply(rule_tac
      x="\<delta>"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(blast)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(clarsimp)
  done

lemma Fact6_12__3: "
  I \<in> valid_item_set G k \<gamma>
  \<Longrightarrow> \<exists>w. w @ cfg_item_rhs1 I = \<gamma>"
  apply(simp add: valid_item_set_def)
  apply(simp add: valid_item_set_n_def)
  apply(clarsimp)
  done

lemma Fact6_12__4: "
  I \<in> valid_item_set G k \<gamma>
  \<Longrightarrow> cfg_item_look_ahead I \<in> FOLLOW G k [teA (cfg_item_lhs I)]"
  apply(simp add: valid_item_set_def)
  apply(simp add: valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(simp add: FOLLOW_def)
  apply(rule_tac
      x="derivation_take d n"
      in exI)
  apply(rule conjI)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac cfgRM.derivation_take_preserves_derivation)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule conjI)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      m="Suc 0"
      in cfgRM.derivation_take_preserves_generates_maximum_of_domain)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(rule conjI)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      x="\<delta>"
      in exI)
  apply(rule_tac
      x="z"
      in exI)
  apply(rule conjI)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      x="e1"
      in exI)
   apply(simp add: derivation_take_def)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(simp add: cfgSTD_first_def)
  apply(rule inMap)
  apply(auto)
  apply(rule_tac
      x="filterB z"
      in exI)
  apply(auto)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = z\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(rule cfgSTD.der1_is_derivation)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(simp add: der1_def)
   apply(rule sym)
   apply(rule liftBDeConv2)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(rule take_liftB_co)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(blast)+
  done

lemma Fact6_12__5: "
  I \<in> valid_item_set G k \<gamma>
  \<Longrightarrow> cfg_item_look_ahead I \<in> FOLLOW G k (\<gamma> @ (cfg_item_rhs2 I))"
  apply(simp add: valid_item_set_def)
  apply(simp add: valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(simp add: FOLLOW_def)
  apply(rule_tac
      x="d"
      in exI)
  apply(auto)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(auto)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule_tac
      x="z"
      in exI)
  apply(auto)
  apply(simp add: cfgSTD_first_def)
  apply(rule inMap)
  apply(auto)
  apply(rule_tac
      x="filterB z"
      in exI)
  apply(auto)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = z\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(rule cfgSTD.der1_is_derivation)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(simp add: der1_def)
   apply(rule sym)
   apply(rule liftBDeConv2)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(rule take_liftB_co)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(blast)+
  done

lemma Fact6_12__6: "
  viable_prefix G \<gamma>
  \<Longrightarrow> \<exists>I. I \<in> valid_item_set G k \<gamma>"
  apply(simp add: valid_item_set_def)
  apply(simp add: valid_item_set_n_def)
  apply(simp add: viable_prefix_def)
  apply(auto)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule_tac
      x="A"
      in exI)
  apply(rule_tac
      x="\<alpha>"
      in exI)
  apply(rule_tac
      x="\<beta>"
      in exI)
  apply(auto)
  apply(rule_tac
      x="take k (filterB y)"
      in exI)
  apply(rule_tac
      x="d"
      in exI)
  apply(auto)
  apply(rule sym)
  apply(rule_tac
      s="take k (liftB ((filterB y)))"
      and t="liftB (take k (filterB y))"
      in ssubst)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   defer
   apply(rule_tac
      t="liftB (filterB y)"
      and s="y"
      in ssubst)
    apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
    apply(rule liftBDeConv2)
    apply(blast)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(blast)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule_tac
      t="liftB"
      and s="map (\<lambda>x. teB x)"
      in ssubst)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(rule ext)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2 x)(*strict*)
   apply(rule liftBMap)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule sym)
  apply(rule List.take_map)
  done

lemma Lemma6__24_1: "
  \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<omega> @ \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set_n G k n \<gamma>
  \<Longrightarrow> viable_prefix G (\<gamma> @ \<omega>)"
  apply(simp add: viable_prefix_def)
  apply(simp add: valid_item_set_n_def)
  apply(auto)
  apply(rename_tac d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(auto)
  apply(rule_tac
      x="n"
      in exI)
  apply(auto)
  apply(rule_tac
      x="\<alpha>@\<omega>"
      in exI)
  apply(rule_tac
      x="\<beta>"
      in exI)
  apply(rule_tac
      x="z"
      in exI)
  apply(rule_tac
      x="A"
      in exI)
  apply(rule_tac
      x="\<delta>"
      in exI)
  apply(auto)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac d \<delta> e1 e2 z)(*strict*)
     apply(blast)
    apply(rename_tac d \<delta> e1 e2 z)(*strict*)
    apply(blast)
   apply(rename_tac d \<delta> e1 e2 z)(*strict*)
   apply(arith)
  apply(rename_tac d \<delta> e1 e2 z)(*strict*)
  apply(force)
  done

lemma valid_item_set_nonempty_only_on_Sigma_Strings: "
  valid_cfg G
  \<Longrightarrow> valid_item_set G k w \<noteq> {}
  \<Longrightarrow> setB w \<subseteq> cfg_events G \<and> setA w \<subseteq> cfg_nonterminals G"
  apply(simp add: valid_item_set_def)
  apply(simp add: valid_item_set_n_def)
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "setB (\<delta>@\<alpha>@\<beta>@z) \<subseteq> cfg_events G \<and> setA (\<delta>@\<alpha>@\<beta>@z) \<subseteq> cfg_nonterminals G")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(rule conjI)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(simp only: setBConcat concat_asso)
    apply(blast)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      w="[teA (cfg_initial G)]"
      in staysInAlpha2)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(simp add: valid_cfg_def)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(rule cfgRM_derivations_are_cfg_derivations)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(force)
  done

lemma valid_item_set_LookAhead_in_cfg_events: "
  valid_cfg G'
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = w1, cfg_item_rhs2 = w2, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set G' k x
  \<Longrightarrow> set y \<subseteq> cfg_events G'"
  apply(simp add: valid_item_set_def)
  apply(simp add: valid_item_set_n_def)
  apply(erule exE)+
  apply(rename_tac n d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      t="set y"
      and s="setB (liftB y)"
      in ssubst)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(rule set_setBliftB)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      t="liftB y"
      and s="take k z"
      in ssubst)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      B="setB z"
      in subset_trans)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(rule setBTakeIndexSubset2)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      B="setB (\<delta> @ (teA A) # z)"
      in subset_trans)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      t="setB z"
      and s="setB (drop (length (\<delta>@[teA A])) (\<delta>@(teA A) # z))"
      in ssubst)
    apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(rule setBDropIndexSubset2)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(rule_tac
      d="d"
      and i="0"
      and j="n"
      in staysInSigma2)
       apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
     apply(simp add: valid_cfg_def)
    apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
    apply(simp add: valid_cfg_def)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__basis_preserves_item_set: "
  S \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__basis X S \<subseteq> Collect (valid_item G k)"
  apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def valid_item_def F_VALID_ITEM_SET_GOTO__passes_def)
  apply(auto)
  apply(rename_tac x I1)(*strict*)
  apply(subgoal_tac "valid_item G k I1")
   apply(rename_tac x I1)(*strict*)
   apply(simp add: valid_item_def)
  apply(rename_tac x I1)(*strict*)
  apply(auto)
  done

lemma F_VALID_ITEM_SET_INITIAL_consists_of_items: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> F_VALID_ITEM_SET_INITIAL G F k \<subseteq> Collect (valid_item G k)"
  apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G F k"
      and s="valid_item_set G k []"
      in ssubst)
   apply(rule_tac
      t="valid_item_set G k []"
      and s="(if []=[] then F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL G F k) else F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k [])) )"
      in ssubst)
    apply(rule Lemma6__23)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
   apply(rule sym)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_idemp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule Fact6_12__2)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma Item_rhs2_in_CFG: "
  valid_cfg G
  \<Longrightarrow> valid_item G k I
  \<Longrightarrow> x = cfg_item_rhs2 I
  \<Longrightarrow> set x \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
  apply(simp add: valid_item_def valid_cfg_def)
  apply(erule conjE)+
  apply(erule bexE)+
  apply(rename_tac p)(*strict*)
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac p)(*strict*)
   apply(erule conjE)+
   apply(rule_tac
      B="set (prod_rhs p)"
      in subset_trans)
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(force)
  apply(rename_tac p)(*strict*)
  apply(rule_tac
      B="set (prod_rhs p)"
      in subset_trans)
   apply(rename_tac p)(*strict*)
   apply(force)
  apply(rename_tac p)(*strict*)
  apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
   apply(rename_tac p)(*strict*)
   apply(force)
  apply(rename_tac p)(*strict*)
  apply(force)
  done

lemma Item_la_in_CFG: "
  valid_cfg G
  \<Longrightarrow> valid_item G k I
  \<Longrightarrow> x = cfg_item_look_ahead I
  \<Longrightarrow> set x \<subseteq> cfg_events G"
  apply(simp add: valid_item_def valid_cfg_def)
  done

lemma Item_lhs_in_CFG: "
  valid_cfg G
  \<Longrightarrow> valid_item G k I
  \<Longrightarrow> x = cfg_item_lhs I
  \<Longrightarrow> x \<in> cfg_nonterminals G"
  apply(simp add: valid_item_def valid_cfg_def)
  apply(clarsimp)
  apply(rename_tac p)(*strict*)
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac p)(*strict*)
   apply(erule conjE)+
   apply(clarsimp)
  apply(rename_tac p)(*strict*)
  apply(force)
  done

lemma valid_item_set_n_subset_valid_item_set_rev: "
  I \<in> valid_item_set G k w
  \<Longrightarrow> \<exists>n. I \<in> valid_item_set_n G k n w"
  apply(simp add: valid_item_set_def)
  done

lemma valid_item_insert_symbol: "
  valid_item G k I
  \<Longrightarrow> valid_item (G\<lparr>cfg_events := cfg_events G \<union> {a}\<rparr>) k I"
  apply(simp add: valid_item_def)
  apply(auto)
  done

lemma F_VALID_ITEM_SET_GOTO_preserves_item_set: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> \<forall>I \<in> S. valid_item G k I
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO G F k X S
  \<Longrightarrow> valid_item G k I"
  apply(simp add: F_VALID_ITEM_SET_GOTO_def)
  apply(subgoal_tac "Ball (F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis X S)) (valid_item G k)")
   apply(force)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02_unfold)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__basis SSX SSS \<subseteq> Collect (valid_item SSG SSk)" for SSX SSS SSG SSk)
   apply(force)
  apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
  apply(auto)
  done

lemma F_VALID_ITEM_SET_GOTO_unique_entry_for_nonempty_sets: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G F k X q = F_VALID_ITEM_SET_GOTO G F k Y p
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G F k X q \<noteq> {}
  \<Longrightarrow> p \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> q \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> X = Y"
  apply(simp add: F_VALID_ITEM_SET_GOTO_def)
  apply(case_tac "F_VALID_ITEM_SET_GOTO__basis X q={}")
   apply(clarsimp)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k {}={}")
    apply(clarsimp)
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk SSS"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS))" for SSG SSF SSk SSS
      in ssubst)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(clarsimp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  apply(subgoal_tac "\<exists>I w. I \<in> F_VALID_ITEM_SET_GOTO__basis X q \<and> cfg_item_rhs1 I = w@[X]")
   prefer 2
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
   apply(clarsimp)
   apply(rename_tac x I1)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(rule conjI)
    apply(rename_tac x I1)(*strict*)
    apply(rule_tac
      x="I1"
      in bexI)
     apply(rename_tac x I1)(*strict*)
     apply(clarsimp)
    apply(rename_tac x I1)(*strict*)
    apply(force)
   apply(rename_tac x I1)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(clarsimp)
  apply(rename_tac I w)(*strict*)
  apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis X q)")
   apply(rename_tac I w)(*strict*)
   apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis Y p)")
    apply(rename_tac I w)(*strict*)
    apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__basis Y p")
     apply(rename_tac I w)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
     apply(clarsimp)
     apply(rename_tac I w I1 I1a x I1b)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
    apply(rename_tac I w)(*strict*)
    apply(subgoal_tac "\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis Y p). I \<in> (F_VALID_ITEM_SET_GOTO__basis Y p) \<or> (cfg_item_rhs1 I=[])")
     apply(rename_tac I w)(*strict*)
     prefer 2
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_fresh)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(clarsimp)
     apply(rename_tac I w x)(*strict*)
     apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__basis SSX SSS \<subseteq> Collect (valid_item SSG SSk)" for SSX SSS SSG SSk)
      apply(rename_tac I w x)(*strict*)
      apply(force)
     apply(rename_tac I w x)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
     apply(force)
    apply(rename_tac I w)(*strict*)
    apply(erule_tac
      x="I"
      in ballE)
     apply(rename_tac I w)(*strict*)
     apply(force)
    apply(rename_tac I w)(*strict*)
    apply(force)
   apply(rename_tac I w)(*strict*)
   apply(force)
  apply(rename_tac I w)(*strict*)
  apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__basis X q"
      in set_mp)
   apply(rename_tac I w)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
     apply(rename_tac I w)(*strict*)
     apply(force)
    apply(rename_tac I w)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
    apply(force)
   apply(rename_tac I w)(*strict*)
   apply(force)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_insertion_implies_existence_of_production: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S
  \<Longrightarrow> \<forall>I \<in> S. valid_item G k I
  \<Longrightarrow> I \<notin> S
  \<Longrightarrow> \<exists>p \<in> cfg_productions G. teA (cfg_item_lhs I) \<in> set (prod_rhs p)"
  apply(subgoal_tac "(\<forall>I \<in> S. valid_item SSG SSk I) \<and> valid_cfg SSG \<and> F_VALID_ITEM_SET_GOTO__descent__fp_valid_input SSG SSF SSk S \<and> SSI \<in> F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk S \<and> SSI \<notin> S \<longrightarrow> (\<exists>p \<in> cfg_productions SSG. teA (cfg_item_lhs SSI) \<in> set (prod_rhs p))" for SSF SSk SSG SSI)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_preserves_required_production)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(erule impE)
   apply(clarsimp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__basis_makes_nonempty_rhs1: "
  I \<in> F_VALID_ITEM_SET_GOTO__basis G' X
  \<Longrightarrow> cfg_item_rhs1 I = []
  \<Longrightarrow> P"
  apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(clarsimp)
  apply(rename_tac I1)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  done

lemma valid_item_set_F_VALID_ITEM_SET_GOTO__passes: "
  valid_cfg G
  \<Longrightarrow> I \<in> valid_item_set G k w
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__passes a I J
  \<Longrightarrow> J \<in> valid_item_set G k (w @ [a])"
  apply(simp add: valid_item_set_def valid_item_set_n_def F_VALID_ITEM_SET_GOTO__passes_def)
  apply(clarsimp)
  apply(rename_tac n \<alpha> d \<delta> e1 e2 z)(*strict*)
  apply(case_tac J)
  apply(rename_tac n \<alpha> d \<delta> e1 e2 z cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
  apply(rename_tac A w1 w2 y)
  apply(rename_tac n \<alpha> d \<delta> e1 e2 z A w1 w2 y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n \<alpha> d \<delta> e1 e2 z A w2 y)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  done

lemma viable_prefix_in_CFG: "
  valid_cfg G
  \<Longrightarrow> viable_prefix G w
  \<Longrightarrow> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
  apply(simp add: viable_prefix_def)
  apply(erule exE)+
  apply(rename_tac d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac d n)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac d n \<alpha> \<beta> y A \<delta>)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(subgoal_tac "setB (\<delta> @ \<alpha> @ \<beta> @ y) \<subseteq> cfg_events SSG \<and> setA (\<delta> @ \<alpha> @ \<beta> @ y) \<subseteq> cfg_nonterminals SSG" for SSG)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(subgoal_tac "setB (\<delta> @ \<alpha>) \<subseteq> cfg_events SSG \<and> setA (\<delta> @ \<alpha>) \<subseteq> cfg_nonterminals SSG" for SSG)
    apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
     apply(force)
    apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
    apply(force)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(simp only: setBConcat setAConcat concat_asso)
   apply(force)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule_tac
      w="[teA (cfg_initial G)]"
      and i="0"
      in staysInAlpha2)
       apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
       apply(force)
      apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
     apply(clarsimp)
    apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
    apply(rule cfgRM_derivations_are_cfg_derivations)
    apply(force)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(force)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(force)
  done

theorem valid_item_set_eq_preserved_under_post_extension: "
  valid_cfg (G:: ('nonterminal, 'event) cfg)
  \<Longrightarrow> cfgSTD_first_compatible (F:: ('nonterminal, 'event) DT_first_function) k
  \<Longrightarrow> valid_item_set G k w = valid_item_set G k v
  \<Longrightarrow> set (w @ v @ [a]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> valid_item_set G k (w @ [a]) = valid_item_set G k (v @ [a])"
  apply(rule_tac
      t="valid_item_set G k (w@[a])"
      and s="F_VALID_ITEM_SET_GOTO G F k a (valid_item_set G k w)"
      in ssubst)
   apply(rule Lemma6__26)
      apply(force)
     apply(force)
    apply(rule two_elements_construct_domain_setA)
    apply(force)
   apply(rule two_elements_construct_domain_setB)
   apply(force)
  apply(rule_tac
      t="valid_item_set G k (v@[a])"
      and s="F_VALID_ITEM_SET_GOTO G F k a (valid_item_set G k v)"
      in ssubst)
   apply(rule Lemma6__26)
      apply(force)
     apply(force)
    apply(rule two_elements_construct_domain_setA)
    apply(force)
   apply(rule two_elements_construct_domain_setB)
   apply(force)
  apply(rule_tac
      t="valid_item_set G k w"
      and s="valid_item_set G k v"
      in ssubst)
   apply(force)
  apply(force)
  done

lemma Lemma6__24_2_items: "
  valid_item G k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<omega> @ \<beta>, cfg_item_look_ahead = y\<rparr>
  \<Longrightarrow> valid_item G k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha> @ \<omega>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr>"
  apply(simp add: valid_item_def)
  done

lemma Lemma6__24_2_items_rev: "
  valid_item G k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha> @ \<omega>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr>
  \<Longrightarrow> valid_item G k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<omega> @ \<beta>, cfg_item_look_ahead = y\<rparr>"
  apply(simp add: valid_item_def)
  done

lemma valid_item_set_shift_symbol_back: "
  \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha> @ [teB x], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = [teB x] @ \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB xs)"
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(auto)
  apply(rename_tac n d \<delta> e1 e2 za)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="\<delta>"
      in exI)
  apply(rule_tac
      x="za"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<gamma>@liftB (xs@[x]) = \<gamma>@liftB xs @ [teB x]")
   apply(rename_tac n d \<delta> e1 e2 za)(*strict*)
   apply(force)
  apply(rename_tac n d \<delta> e1 e2 za)(*strict*)
  apply(rule_tac
      t="liftB (xs @ [x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
   apply(rename_tac n d \<delta> e1 e2 za)(*strict*)
   apply(rule liftB_commute_one_elem_app)
  apply(rename_tac n d \<delta> e1 e2 za)(*strict*)
  apply(blast)
  done

lemma Lemma6__24_2_prime: "
  \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<omega> @ \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set G k \<gamma>
  \<Longrightarrow> \<eta> = \<gamma> @ \<omega>
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha> @ \<omega>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr> \<in> valid_item_set G k \<eta>"
  apply(simp add: valid_item_set_def)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule Lemma6__24_2)
  apply(force)
  done

lemma valid_item_set_shift_symbol_back_prime: "
  \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha> @ [x], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (w @ [x])
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = [x] @ \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k w"
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  done

lemma valid_item_set_shift_symbol_back_mult: "
  \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha> @ v, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (w @ v)
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = v @ \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k w"
  apply(induct v arbitrary: \<beta> rule: rev_induct)
   apply(rename_tac \<beta>)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs \<beta>)(*strict*)
  apply(erule_tac
      x="[x]@\<beta>"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs \<beta>)(*strict*)
   apply(rule valid_item_set_shift_symbol_back_prime)
   apply(force)
  apply(rename_tac x xs \<beta>)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO_empty_on_empty: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> S = {}
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G F k x S = {}"
  apply(clarsimp)
  apply(simp add: F_VALID_ITEM_SET_GOTO_def)
  apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k {}"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG F SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS))" for SSG SSk SSS
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  done

lemma valid_item_set_nonempty_on_every_prefix: "
  valid_cfg (G:: ('nonterminal, 'event) cfg)
  \<Longrightarrow> cfgSTD_first_compatible (F:: ('nonterminal, 'event) DT_first_function) k
  \<Longrightarrow> I \<in> valid_item_set G k w
  \<Longrightarrow> w = v @ x
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> \<exists>J. J \<in> valid_item_set G k v"
  apply(induct x arbitrary: w v I rule: rev_induct)
   apply(rename_tac w v I)(*strict*)
   apply(clarsimp)
   apply(rename_tac v I)(*strict*)
   apply(rule_tac
      x="I"
      in exI)
   apply(clarsimp)
  apply(rename_tac x xs w v I)(*strict*)
  apply(subgoal_tac "\<exists>w'. w=w'@[x]")
   apply(rename_tac x xs w v I)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs v I)(*strict*)
   apply(erule_tac
      x="v@xs"
      in meta_allE)
   apply(erule_tac
      x="v"
      in meta_allE)
   apply(subgoal_tac "\<exists>I. I \<in> valid_item_set G k (v@xs)")
    apply(rename_tac x xs v I)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs v I Ia)(*strict*)
    apply(erule_tac
      x="Ia"
      in meta_allE)
    apply(erule meta_impE)
     apply(rename_tac x xs v I Ia)(*strict*)
     apply(force)
    apply(rename_tac x xs v I Ia)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x xs v I Ia)(*strict*)
     apply(simp only: setAConcat concat_asso)
     apply(force)
    apply(rename_tac x xs v I Ia)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x xs v I Ia)(*strict*)
     apply(simp only: setBConcat concat_asso)
     apply(force)
    apply(rename_tac x xs v I Ia)(*strict*)
    apply(force)
   apply(rename_tac x xs v I)(*strict*)
   prefer 2
   apply(rename_tac x xs w v I)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs v I)(*strict*)
  apply(clarsimp)
  apply(thin_tac "\<And>I. I \<in> valid_item_set G k (v @ xs) \<Longrightarrow> setA (v @ xs) \<subseteq> cfg_nonterminals G \<Longrightarrow> setB (v @ xs) \<subseteq> cfg_events G \<Longrightarrow> \<exists>J. J \<in> valid_item_set G k v ")
  apply(rename_tac x xs v I)(*strict*)
  apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO G F k x (valid_item_set G k (v@xs))")
   apply(rename_tac x xs v I)(*strict*)
   apply(thin_tac "I \<in> valid_item_set G k (v@xs @ [x])")
   apply(case_tac "valid_item_set G k (v@xs) = {}")
    apply(rename_tac x xs v I)(*strict*)
    apply(subgoal_tac "F_VALID_ITEM_SET_GOTO G F k x (valid_item_set G k (v@xs)) = {}")
     apply(rename_tac x xs v I)(*strict*)
     prefer 2
     apply(rule F_VALID_ITEM_SET_GOTO_empty_on_empty)
       apply(rename_tac x xs v I)(*strict*)
       apply(force)
      apply(rename_tac x xs v I)(*strict*)
      apply(force)
     apply(rename_tac x xs v I)(*strict*)
     apply(force)
    apply(rename_tac x xs v I)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac x xs v I)(*strict*)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G F k x (valid_item_set G k (v@xs))"
      and s="valid_item_set G k ((v@xs) @ [x])"
      in subst)
   apply(rename_tac x xs v I)(*strict*)
   apply(rule Lemma6__26)
      apply(rename_tac x xs v I)(*strict*)
      apply(force)
     apply(rename_tac x xs v I)(*strict*)
     apply(force)
    apply(rename_tac x xs v I)(*strict*)
    apply(force)
   apply(rename_tac x xs v I)(*strict*)
   apply(force)
  apply(force)
  done

lemma viable_prefix_nonempty_on_every_prefix: "
  valid_cfg (G:: ('nonterminal, 'event) cfg)
  \<Longrightarrow> cfgSTD_first_compatible (F:: ('nonterminal, 'event) DT_first_function) k
  \<Longrightarrow> viable_prefix G w
  \<Longrightarrow> w = v @ x
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> viable_prefix G v"
  apply(subgoal_tac "\<exists>I. I \<in> valid_item_set G k w")
   prefer 2
   apply(rule Fact6_12__6)
   apply(force)
  apply(clarsimp)
  apply(rename_tac I)(*strict*)
  apply(subgoal_tac "\<exists>J. J \<in> valid_item_set G k v")
   apply(rename_tac I)(*strict*)
   prefer 2
   apply(rule valid_item_set_nonempty_on_every_prefix)
        apply(rename_tac I)(*strict*)
        apply(force)
       apply(rename_tac I)(*strict*)
       apply(force)
      apply(rename_tac I)(*strict*)
      apply(force)
     apply(rename_tac I)(*strict*)
     apply(force)
    apply(rename_tac I)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac I)(*strict*)
  apply(clarsimp)
  apply(rename_tac I J)(*strict*)
  apply(rule Fact6_12__1)
  apply(force)
  done

lemma viable_prefix_of_DoS: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> viable_prefix G' ([teB Do] @ [teA (cfg_initial G)])"
  apply(simp add: viable_prefix_def)
  apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr> \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs= [teB Do,teA (cfg_initial G),teB Do] \<rparr> \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(rule conjI)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rule_tac
      x="0"
      in exI)
  apply(clarsimp)
  apply(simp add: der2_def maximum_of_domain_def)
  apply(rule_tac
      x="[teB (F_FRESH (cfg_events G)),teA (cfg_initial G)]"
      in exI)
  apply(rule_tac
      x="[teB (F_FRESH (cfg_events G))]"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule_tac
      x="(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(force)
  done

lemma cfg_item_valid_item_set_of_DoS: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> \<lparr>cfg_item_lhs = cfg_initial G', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k ([teB Do] @ [teA (cfg_initial G)])"
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr> \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs= [teB Do,teA (cfg_initial G),teB Do] \<rparr> \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(rule conjI)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp add: der2_def maximum_of_domain_def)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="Some \<lparr>prod_lhs = cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))), prod_rhs = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule conjI)
   apply(simp add: der2_def)
  apply(rule conjI)
   apply(simp add: der2_def)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(simp add: der2_def maximum_of_domain_def)
  apply(force)
  done

lemma F_LR_MACHINE_shift_back_in_pre_state: "
  valid_cfg G'
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> I \<in> valid_item_set G' k w
  \<Longrightarrow> set v \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G' F k x (valid_item_set G' k v) = valid_item_set G' k w
  \<Longrightarrow> cfg_item_rhs1 I = w' @ [x]
  \<Longrightarrow> I\<lparr>cfg_item_rhs1 := w', cfg_item_rhs2 := x # cfg_item_rhs2 I\<rparr> \<in> valid_item_set G' k v"
  apply(case_tac I)
  apply(rename_tac cfg_item_lhs cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_ahead)(*strict*)
  apply(clarsimp)
  apply(rename_tac cfg_item_lhs cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
  apply(rename_tac A' w'' y')
  apply(rename_tac A' w'' y')(*strict*)
  apply(subgoal_tac "valid_item_set G' k w = valid_item_set G' k (v@[x])")
   apply(rename_tac A' w'' y')(*strict*)
   apply(clarsimp)
   apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(rename_tac A' w'' y')(*strict*)
  apply(subgoal_tac "valid_item G' k \<lparr>cfg_item_lhs = A', cfg_item_rhs1 = w' @ [x], cfg_item_rhs2 = w'', cfg_item_look_ahead = y'\<rparr>")
   apply(rename_tac A' w'' y')(*strict*)
   apply(rule_tac
      t="valid_item_set G' k (v @ [x])"
      and s="F_VALID_ITEM_SET_GOTO G' F k x (valid_item_set G' k v)"
      in ssubst)
    apply(rename_tac A' w'' y')(*strict*)
    apply(rule Lemma6__26)
       apply(rename_tac A' w'' y')(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac A' w'' y')(*strict*)
     apply(simp only: setAConcat concat_asso)
     apply(rule Set.Un_least)
      apply(rename_tac A' w'' y')(*strict*)
      apply(rule two_elements_construct_domain_setA)
      apply(force)
     apply(rename_tac A' w'' y')(*strict*)
     prefer 2
     apply(simp (no_asm_use) only: setBConcat concat_asso)
     apply(rule Set.Un_least)
      apply(rename_tac A' w'' y')(*strict*)
      apply(rule two_elements_construct_domain_setB)
      apply(force)
     apply(rename_tac A' w'' y')(*strict*)
     apply(simp only: valid_item_def valid_cfg_def)
     apply(erule conjE)+
     apply(erule bexE)
     apply(rename_tac A' w'' y' p)(*strict*)
     apply(erule_tac
      x="p"
      in ballE)
      apply(rename_tac A' w'' y' p)(*strict*)
      apply(simp add: setBConcat concat_asso)
     apply(rename_tac A' w'' y' p)(*strict*)
     apply(force)
    apply(rename_tac A' w'' y')(*strict*)
    apply(simp only: valid_item_def valid_cfg_def)
    apply(erule conjE)+
    apply(erule bexE)
    apply(rename_tac A' w'' y' p)(*strict*)
    apply(erule_tac
      x="p"
      in ballE)
     apply(rename_tac A' w'' y' p)(*strict*)
     apply(simp add: setAConcat concat_asso)
    apply(rename_tac A' w'' y' p)(*strict*)
    apply(force)
   apply(rename_tac A' w'' y')(*strict*)
   apply(force)
  apply(rename_tac A' w'' y')(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac A' w'' y')(*strict*)
   apply(force)
  apply(rename_tac A' w'' y')(*strict*)
  apply(force)
  done

lemma F_CFG_AUGMENT__Empty_viable_prefix: "
  valid_cfg G
  \<Longrightarrow> \<exists>p \<in> cfg_productions G. prod_lhs p = cfg_initial G
  \<Longrightarrow> viable_prefix G []"
  apply(clarsimp)
  apply(rename_tac p)(*strict*)
  apply(simp add: viable_prefix_def)
  apply(rule_tac
      x = "der2 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> p \<lparr>cfg_conf=prod_rhs p\<rparr>"
      in exI)
  apply(rename_tac p)(*strict*)
  apply(rule conjI)
   apply(rename_tac p)(*strict*)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac p)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac p)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac p)(*strict*)
  apply(rule conjI)
   apply(rename_tac p)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac p)(*strict*)
  apply(simp add: der2_def)
  done

lemma F_CFG_AUGMENT__ONE_step_viable_prefix: "
  valid_cfg G
  \<Longrightarrow> prod_lhs p = cfg_initial G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> w = prod_rhs p
  \<Longrightarrow> viable_prefix G w"
  apply(simp add: viable_prefix_def)
  apply(rule_tac
      x = "der2 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> p \<lparr>cfg_conf=prod_rhs p\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: der2_def maximum_of_domain_def)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_empty: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp G F k {} = {}"
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp SSG F SSk SSS"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG F SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS))" for SSG SSk SSS
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(clarsimp)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_single_contain: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_item G k x
  \<Longrightarrow> x \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k {x}"
  apply(rule_tac
      A="{x}"
      in set_mp)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(force)+
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_F_VALID_ITEM_SET_GOTO__descent__fp_one_1_elem: "
  J \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N
  \<Longrightarrow> \<exists>I \<in> N. J \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k I"
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_exists_origin_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S
  \<Longrightarrow> S \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> \<exists>J \<in> S. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k {J}"
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k S = S")
   apply(rule_tac
      x="I"
      in bexI)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_single_contain)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac "I \<in> S")
   apply(rule_tac
      x="I"
      in bexI)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_single_contain)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "cfgSTD_first_compatible F k \<longrightarrow> (S\<noteq>F_VALID_ITEM_SET_GOTO__descent__fp G F k S) \<longrightarrow> (\<forall>I \<in> (F_VALID_ITEM_SET_GOTO__descent__fp G F k S-S). (\<exists>J \<in> S. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k {J}))")
   apply(force)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k S\<noteq>S")
  apply(thin_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
  apply(thin_tac "I\<notin>S")
  apply(rule_tac
      G="G"
      and k="k"
      and N="S"
      in F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift_prime)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(force)
   apply(rename_tac Ga Fa ka N)(*strict*)
   apply(thin_tac "valid_cfg G")
   apply(thin_tac "S \<subseteq> Collect (valid_item G k)")
   apply(thin_tac "cfgSTD_first_compatible F k")
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I)(*strict*)
   apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
    apply(rename_tac G F k N I)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
     apply(rename_tac G F k N I)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G F k N I)(*strict*)
    apply(simp (no_asm_use) add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
    apply(clarsimp)
    apply(rename_tac G F k N I x)(*strict*)
    apply(rule_tac
      x="x"
      in bexI)
     apply(rename_tac G F k N I x)(*strict*)
     apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k {x}"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG F SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS))" for SSG SSk SSS
      in ssubst)
      apply(rename_tac G F k N I x)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rename_tac G F k N I x)(*strict*)
     apply(clarsimp)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
     apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k x = {x}")
      apply(rename_tac G F k N I x)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N I x)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k x"
      in set_mp)
      apply(rename_tac G F k N I x)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(clarsimp)
      apply(rename_tac G F k N I x xa)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1_adds_valid_item)
         apply(rename_tac G F k N I x xa)(*strict*)
         apply(force)
        apply(rename_tac G F k N I x xa)(*strict*)
        apply(force)
       apply(rename_tac G F k N I x xa)(*strict*)
       apply(force)
      apply(rename_tac G F k N I x)(*strict*)
      apply(force)
     apply(rename_tac G F k N I x)(*strict*)
     apply(force)
    apply(rename_tac G F k N I)(*strict*)
    apply(clarsimp)
   apply(case_tac "I\<notin>F_VALID_ITEM_SET_GOTO__descent__fp G F k N - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
    apply(rename_tac G F k N I)(*strict*)
    apply(clarsimp)
    apply(thin_tac "\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k N - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N. \<exists>J \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k {J}")
    apply(rename_tac G F k N I)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
    apply(clarsimp)
    apply(rename_tac G F k N I x)(*strict*)
    apply(rule_tac
      x="x"
      in bexI)
     apply(rename_tac G F k N I x)(*strict*)
     apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k {x}"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG F SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS))" for SSG SSk SSS
      in ssubst)
      apply(rename_tac G F k N I x)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rename_tac G F k N I x)(*strict*)
     apply(clarsimp)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
     apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k x = {x}")
      apply(rename_tac G F k N I x)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N I x)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k x"
      in set_mp)
      apply(rename_tac G F k N I x)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(clarsimp)
      apply(rename_tac G F k N I x xa)(*strict*)
      apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1_adds_valid_item)
         apply(rename_tac G F k N I x xa)(*strict*)
         apply(force)
        apply(rename_tac G F k N I x xa)(*strict*)
        apply(force)
       apply(rename_tac G F k N I x xa)(*strict*)
       apply(force)
      apply(rename_tac G F k N I x)(*strict*)
      apply(force)
     apply(rename_tac G F k N I x)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="I"
      in ballE)
    apply(rename_tac G F k N I)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I J)(*strict*)
   apply(subgoal_tac "J\<noteq>I")
    apply(rename_tac G F k N I J)(*strict*)
    prefer 2
    apply(rule distinct_by_set_membership)
     apply(rename_tac G F k N I J)(*strict*)
     apply(force)
    apply(rename_tac G F k N I J)(*strict*)
    apply(force)
   apply(rename_tac G F k N I J)(*strict*)
   apply(subgoal_tac "\<exists>I \<in> N. J \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k I")
    apply(rename_tac G F k N I J)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_F_VALID_ITEM_SET_GOTO__descent__fp_one_1_elem)
    apply(force)
   apply(rename_tac G F k N I J)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I J Ia)(*strict*)
   apply(rule_tac
      x="Ia"
      in bexI)
    apply(rename_tac G F k N I J Ia)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k N I J Ia)(*strict*)
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k {Ia}"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG F SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS))" for SSG SSk SSS
      in ssubst)
    apply(rename_tac G F k N I J Ia)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(rename_tac G F k N I J Ia)(*strict*)
   apply(clarsimp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
   apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k Ia = {Ia}")
    apply(rename_tac G F k N I J Ia)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N I Ia x)(*strict*)
    apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k {Ia} = {Ia}")
     apply(rename_tac G F k N I Ia x)(*strict*)
     apply(force)
    apply(rename_tac G F k N I Ia x)(*strict*)
    apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k {Ia}"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG F SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG F SSk SSS))" for SSG SSk SSS
      in ssubst)
     apply(rename_tac G F k N I Ia x)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(rename_tac G F k N I Ia x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
   apply(rename_tac G F k N I J Ia)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I J Ia x)(*strict*)
   apply(fold F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
   apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp G F k {J}"
      in set_mp)
    apply(rename_tac G F k N I J Ia x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k N I J Ia x)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono2)
     apply(rename_tac G F k N I J Ia x)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1_adds_valid_item)
        apply(rename_tac G F k N I J Ia x)(*strict*)
        apply(force)
       apply(rename_tac G F k N I J Ia x)(*strict*)
       apply(force)
      apply(rename_tac G F k N I J Ia x)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac G F k N I J Ia x)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(clarsimp)
    apply(rename_tac G F k N I J Ia x xa)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1_adds_valid_item)
       apply(rename_tac G F k N I J Ia x xa)(*strict*)
       apply(force)
      apply(rename_tac G F k N I J Ia x xa)(*strict*)
      apply(force)
     apply(rename_tac G F k N I J Ia x xa)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac G F k N I J Ia x)(*strict*)
   apply(rule_tac
      B="F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k Ia"
      in subset_trans)
    apply(rename_tac G F k N I J Ia x)(*strict*)
    apply(force)
   apply(rename_tac G F k N I J Ia x)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(clarsimp)
   apply(rename_tac G F k N I J Ia x xa)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1_adds_valid_item)
      apply(rename_tac G F k N I J Ia x xa)(*strict*)
      apply(force)
     apply(rename_tac G F k N I J Ia x xa)(*strict*)
     apply(force)
    apply(rename_tac G F k N I J Ia x xa)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac Ga Fa ka N)(*strict*)
  apply(thin_tac "valid_cfg G")
  apply(thin_tac "S \<subseteq> Collect (valid_item G k)")
  apply(rename_tac G F k N)(*strict*)
  apply(clarsimp)
  apply(thin_tac "cfgSTD_first_compatible F k")
  apply(rename_tac G F k N I)(*strict*)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k N = N")
   apply(rename_tac G F k N I)(*strict*)
   apply(force)
  apply(rename_tac G F k N I)(*strict*)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS))" for SSG SSF SSk SSS
      in ssubst)
   apply(rename_tac G F k N I)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(rename_tac G F k N I)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_exists_origin: "
  valid_cfg G
  \<Longrightarrow>  cfgSTD_first_compatible F k
  \<Longrightarrow> S \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> q = F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis x S)
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> \<exists>J \<in> S. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis x {J})"
  apply(subgoal_tac "\<exists>J \<in> (F_VALID_ITEM_SET_GOTO__basis x S). I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k {J}")
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_exists_origin_prime)
      apply(force)
     apply(force)
    apply(force)
   apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
   apply(force)
  apply(clarsimp)
  apply(rename_tac J)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(clarsimp)
  apply(rename_tac J I1)(*strict*)
  apply(rule_tac
      x="I1"
      in bexI)
   apply(rename_tac J I1)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac J I1)(*strict*)
  apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__descent__fp G F k {J}"
      in set_mp)
   apply(rename_tac J I1)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac J I1)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono2)
    apply(rename_tac J I1)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(subgoal_tac "valid_item G k I1")
     apply(rename_tac J I1)(*strict*)
     apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
     apply(clarsimp)
     apply(simp add: valid_item_def)
    apply(rename_tac J I1)(*strict*)
    apply(force)
   apply(rename_tac J I1)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(clarsimp)
   apply(rename_tac J I1 xa)(*strict*)
   apply(subgoal_tac "valid_item G k I1")
    apply(rename_tac J I1 xa)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
    apply(clarsimp)
    apply(simp add: valid_item_def)
   apply(rename_tac J I1 xa)(*strict*)
   apply(force)
  apply(rename_tac J I1)(*strict*)
  apply(rule_tac
      B="{I2. F_VALID_ITEM_SET_GOTO__passes x I1 I2}"
      in subset_trans)
   apply(rename_tac J I1)(*strict*)
   apply(force)
  apply(rename_tac J I1)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono_hlp)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(clarsimp)
  apply(rename_tac J I1 xa)(*strict*)
  apply(subgoal_tac "valid_item G k I1")
   apply(rename_tac J I1 xa)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
   apply(clarsimp)
   apply(simp add: valid_item_def)
  apply(rename_tac J I1 xa)(*strict*)
  apply(force)
  done

lemma Sentential_from_viable_prefix: "
  valid_cfg G
  \<Longrightarrow> viable_prefix G w
  \<Longrightarrow> Sentential G w"
  apply(simp add: viable_prefix_def Sentential_def)
  apply(clarsimp)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
      apply(force)
     apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
     apply(force)
    apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(rule cfg_initial_in_nonterms)
    apply(force)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(force)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(simp add: cfg_initial_configurations_def cfg_configurations_def)
   apply(rule cfg_initial_in_nonterms)
   apply(force)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule_tac
      x="Some e2"
      in exI)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(rule_tac
      x="\<beta>@y"
      in exI)
  apply(force)
  done

lemma SententialRM_from_viable_prefix: "
  valid_cfg G
  \<Longrightarrow> viable_prefix G w
  \<Longrightarrow> SententialRM G w"
  apply(simp add: viable_prefix_def SententialRM_def)
  apply(clarsimp)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(force)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(rule cfgRM.derivation_belongs)
      apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
      apply(force)
     apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
     apply(force)
    apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(rule cfg_initial_in_nonterms)
    apply(force)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(force)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(simp add: cfg_initial_configurations_def cfg_configurations_def)
   apply(rule cfg_initial_in_nonterms)
   apply(force)
  apply(rename_tac d n \<alpha> \<beta> y A \<delta> e1 e2)(*strict*)
  apply(rule_tac
      x="Some e2"
      in exI)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(rule_tac
      x="\<beta>@y"
      in exI)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_origin_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> S \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S - S
  \<Longrightarrow> \<exists>J \<in> S. \<exists>d n w e. maximum_of_domain d n \<and> cfgSTD.derivation G d \<and> cfgSTD.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)"
  apply(case_tac "S=F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
   apply(clarsimp)
  apply(subgoal_tac "cfgSTD_first_compatible F k \<longrightarrow> (S \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k S) \<longrightarrow> (\<forall>I \<in> (F_VALID_ITEM_SET_GOTO__descent__fp G F k S)-S. \<exists>J \<in> S. (\<exists>d n w e e'. maximum_of_domain d n \<and> cfgSTD.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)))")
   apply(force)
  apply(thin_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S - S")
  apply(thin_tac "S \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
  apply(rule_tac
      G="G"
      and k="k"
      and N="S"
      in F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift_prime)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(force)
   apply(rename_tac Ga Fa ka N)(*strict*)
   prefer 2
   apply(rename_tac Ga Fa ka N)(*strict*)
   apply(thin_tac "valid_cfg G")
   apply(thin_tac "cfgSTD_first_compatible F k")
   apply(thin_tac "S \<subseteq> Collect (valid_item G k)")
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k N = N")
    apply(rename_tac G F k N I)(*strict*)
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS))" for SSG SSF SSk SSS
      in ssubst)
    apply(rename_tac G F k N I)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
  apply(thin_tac "cfgSTD_first_compatible F k")
  apply(rename_tac Ga Fa ka N)(*strict*)
  apply(thin_tac "valid_cfg G")
  apply(thin_tac "S \<subseteq> Collect (valid_item G k)")
  apply(rename_tac G F k N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N I)(*strict*)
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
    apply(rename_tac G F k N I)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(subgoal_tac "\<exists>J \<in> N. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k J")
    apply(rename_tac G F k N I)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_F_VALID_ITEM_SET_GOTO__descent__fp_one_1_elem)
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I J)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
   apply(erule disjE)
    apply(rename_tac G F k N I J)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k N I J)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N J B w z \<beta>)(*strict*)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" in in_F__implies__in_cfgSTD_first)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(force)
      prefer 3
      apply(force)
     apply(subgoal_tac "valid_item G k J")
      prefer 2
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac x="p" in ballE)
      prefer 2
      apply(force)
     apply(simp add: valid_item_def simpY valid_cfg_def)
     apply(force)
    apply(subgoal_tac "valid_item G k J")
     prefer 2
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="p" in ballE)
     prefer 2
     apply(force)
    apply(simp add: valid_item_def simpY valid_cfg_def)
    apply(force)
   apply(simp add: cfgSTD_first_def)
   apply(clarsimp)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgSTD.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf = teA B # liftB x\<rparr>) ")
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    prefer 2
    apply(rule_tac
      x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=teA B#(cfg_conf c)\<rparr>)"
      in exI)
    apply(rule conjI)
     apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
     apply(rule cfgSTD.derivation_map_preserves_derivation2)
      apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac G F k N J B w \<beta> x d e1 n a e b l r)(*strict*)
     apply(rule_tac
      x="teA B#l"
      in exI)
     apply(rule_tac
      x="r"
      in exI)
     apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    apply(rule conjI)
     apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(thin_tac "cfgSTD.derivation G d")
   apply(thin_tac "maximum_of_domain d n")
   apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>)")
   apply(thin_tac "d n = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
   apply(clarsimp)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(rule_tac
      x="J"
      in bexI)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = teA B # liftB x\<rparr> \<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<lparr>cfg_conf = w @ liftB x\<rparr>) n"
      in exI)
   apply(rule_tac
      x="Suc n"
      in exI)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(rule_tac
      t="Suc n"
      and s="n+Suc 0"
      in ssubst)
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(rule_tac concat_has_max_dom)
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(simp add: maximum_of_domain_def)
    apply(simp add: der2_def)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(rule cfgSTD.derivation_concat2)
       apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
       apply(force)
      apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     apply(rule cfgSTD.der2_is_derivation)
     apply(simp add: cfgSTD_step_relation_def)
     apply(rule_tac
      x="[]"
      in exI)
     apply(rule_tac
      x="liftB x"
      in exI)
     apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(rule cfgSTD.derivation_belongs)
       apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
      apply(simp add: derivation_append_def)
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: setAConcat setBConcat concat_asso)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(clarsimp)
     apply(erule_tac
      x="J"
      and A="N"
      and P="\<lambda>J. valid_item G k J"
      in ballE)
      apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
      apply(simp add: valid_item_def)
      apply(clarsimp)
      apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(force)
      apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
      apply(simp only: setAConcat setBConcat concat_asso)
      apply(clarsimp)
      apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead J))"
      and s="{}"
      in ssubst)
       apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
      apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead J))"
      and s="set (cfg_item_look_ahead J)"
      in ssubst)
       apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
       apply(rule sym)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(simp add: derivation_append_def)
   apply(rule_tac
      x="liftB (drop k x)"
      in exI)
   apply(rule_tac
      t="liftB (take k x) @ liftB (drop k x)"
      and s="liftB (take k x @ (drop k x))"
      in subst)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac G F k N I)(*strict*)
  apply(clarsimp)
  apply(case_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k N - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="I"
      in ballE)
    apply(rename_tac G F k N I)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N I J d n w e)(*strict*)
    apply(subgoal_tac "\<exists>K \<in> N. J \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k K")
     apply(rename_tac G F k N I J d n w e)(*strict*)
     prefer 2
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_F_VALID_ITEM_SET_GOTO__descent__fp_one_1_elem)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
    apply(rename_tac G F k N I J d n w e)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N I J d n w e K)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
    apply(erule disjE)
     apply(rename_tac G F k N I J d n w e K)(*strict*)
     apply(clarsimp)
     apply(rename_tac G F k N I d n w e K)(*strict*)
     apply(rule_tac
      x="K"
      in bexI)
      apply(rename_tac G F k N I d n w e K)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G F k N I d n w e K)(*strict*)
     apply(rule_tac
      x="d"
      in exI)
     apply(rule_tac
      x="n"
      in exI)
     apply(clarsimp)
    apply(rename_tac G F k N I J d n w e K)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N I d n w e K B wa z \<beta>)(*strict*)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac G="G" in in_F__implies__in_cfgSTD_first)
         apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(force)
       prefer 3
       apply(force)
      apply(subgoal_tac "valid_item G k K")
       prefer 2
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac x="p" in ballE)
       prefer 2
       apply(force)
      apply(simp add: valid_item_def simpY valid_cfg_def)
      apply(force)
     apply(subgoal_tac "valid_item G k K")
      prefer 2
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac x="p" in ballE)
      prefer 2
      apply(force)
     apply(simp add: valid_item_def simpY valid_cfg_def)
     apply(force)
    apply(simp add: cfgSTD_first_def)
    apply(clarsimp)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgSTD.derivation G d \<and> maximum_of_domain d na \<and> d 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>) \<and> d na = Some (pair e1 \<lparr>cfg_conf = teA B # liftB x\<rparr>) ")
     apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_map da (\<lambda>c. \<lparr>cfg_conf=teA B#(cfg_conf c)\<rparr>)"
      in exI)
     apply(rule conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
      apply(rule cfgSTD.derivation_map_preserves_derivation2)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
      apply(simp add: cfgSTD_step_relation_def)
      apply(clarsimp)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na a ea b l r)(*strict*)
      apply(rule_tac
      x="teA B#l"
      in exI)
      apply(rule_tac
      x="r"
      in exI)
      apply(clarsimp)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
     apply(rule conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(force)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
     apply(simp add: derivation_map_def)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
    apply(thin_tac "cfgSTD.derivation G da")
    apply(thin_tac "maximum_of_domain da na")
    apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>)")
    apply(thin_tac "da na = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
    apply(clarsimp)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
    apply(rule_tac
      x="K"
      in bexI)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
    apply(subgoal_tac "cfgSTD.belongs G da")
     apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
     prefer 2
     apply(rule cfgSTD.derivation_belongs)
        apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
       apply(clarsimp)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
      apply(rule_tac
      t="teA B # \<beta> @ liftB (cfg_item_look_ahead K)"
      and s="cfg_item_rhs2 K @ liftB (cfg_item_look_ahead K)"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
      apply(thin_tac "cfg_item_rhs2 K = teA B # \<beta>")
      apply(subgoal_tac "valid_item G k K")
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
       prefer 2
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
      apply(simp add: cfg_configurations_def valid_item_def)
      apply(clarsimp)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da p)(*strict*)
      apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da p)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da p)(*strict*)
      apply(simp only: setAConcat setBConcat concat_asso)
      apply(clarsimp)
      apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead K))"
      and s="{}"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da p)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da p)(*strict*)
      apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead K))"
      and s="set (cfg_item_look_ahead K)"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da p)(*strict*)
       apply(rule sym)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da p)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgSTD.derivation G d \<and> maximum_of_domain d n \<and> cfgSTD.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = wa @ liftB (take k x) @ liftB (drop k x)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w @ liftB (drop k x)\<rparr>) ")
     apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=(cfg_conf c)@(liftB (drop k x))\<rparr>)"
      in exI)
     apply(rule context_conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
      apply(rule cfgSTD.derivation_map_preserves_derivation2)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
      apply(simp add: cfgSTD_step_relation_def)
      apply(clarsimp)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da a ea b l r)(*strict*)
      apply(rule_tac
      x="l"
      in exI)
      apply(rule_tac
      x="r @ liftB (drop k x)"
      in exI)
      apply(clarsimp)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
     apply(rule conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(force)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
     apply(rule conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
      apply(rule cfgSTD.derivation_map_preserves_belongs)
          apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
          apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
         apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
         apply(force)
        apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
        apply(force)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da c)(*strict*)
      apply(simp add: cfgSTD.belongs_def)
      apply(erule_tac
      x="na"
      and P="\<lambda>na. case da na of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> cfg_step_labels G) \<and> c \<in> cfg_configurations G"
      in allE)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da c)(*strict*)
      apply(clarsimp)
      apply(simp add: cfg_configurations_def)
      apply(clarsimp)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
      apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
      apply(clarsimp)
      apply(rule_tac
      t="setA (liftB (drop k x))"
      and s="{}"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
      apply(rule_tac
      t="setB (liftB (drop k x))"
      and s="set (drop k x)"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
       apply(rule sym)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
      apply(rule conjI)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
      apply(rule_tac
      B="set x"
      in subset_trans)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
       apply(rule set_drop_subset)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
      apply(rule_tac
      t="set x"
      and s="setB (liftB x)"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da ca)(*strict*)
      apply(force)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
     apply(simp add: derivation_map_def)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x e1 na da)(*strict*)
    apply(thin_tac "maximum_of_domain d n")
    apply(thin_tac "cfgSTD.derivation G d")
    apply(thin_tac "cfgLM.belongs G d")
    apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = wa @ liftB (take k x)\<rparr>)")
    apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)")
    apply(clarsimp)
    apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
    apply(subgoal_tac "\<exists>d. maximum_of_domain d (Suc na) \<and> cfgSTD.derivation G d \<and> cfgSTD.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>) \<and> d (Suc na) = Some (pair (Some \<lparr>prod_lhs = B, prod_rhs = wa\<rparr>) \<lparr>cfg_conf = wa @ liftB x\<rparr>) ")
     apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_append da (der2 \<lparr>cfg_conf = teA B # liftB x\<rparr> \<lparr>prod_lhs = B, prod_rhs = wa\<rparr> \<lparr>cfg_conf = wa @ liftB x\<rparr>) na"
      in exI)
     apply(rule context_conjI)
      apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
      apply(rule_tac
      t="Suc na"
      and s="na+Suc 0"
      in ssubst)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
      apply(rule_tac concat_has_max_dom)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
      apply(rule der2_maximum_of_domain)
     apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
     apply(rule context_conjI)
      apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
      apply(rule cfgSTD.derivation_concat2)
         apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
         apply(force)
        apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
        apply(force)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(simp add: cfgSTD_step_relation_def)
       apply(rule_tac
      x="[]"
      in exI)
       apply(rule_tac
      x="liftB x"
      in exI)
       apply(clarsimp)
      apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
      apply(clarsimp)
      apply(simp add: der2_def)
     apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
     apply(rule conjI)
      apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
      apply(rule cfgSTD.derivation_belongs)
         apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
         apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
        apply(simp add: derivation_append_def)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
       apply(rule_tac
      t="teA B # \<beta> @ liftB (cfg_item_look_ahead K)"
      and s="cfg_item_rhs2 K @ liftB (cfg_item_look_ahead K)"
      in ssubst)
        apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
        apply(force)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
       apply(thin_tac "cfg_item_rhs2 K = teA B # \<beta>")
       apply(subgoal_tac "valid_item G k K")
        apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
        prefer 2
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
       apply(simp add: cfg_configurations_def valid_item_def)
       apply(clarsimp)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d p)(*strict*)
       apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(simp add: valid_cfg_def)
       apply(clarsimp)
       apply(erule_tac
      x="p"
      in ballE)
        apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d p)(*strict*)
        apply(clarsimp)
        prefer 2
        apply(force)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d p)(*strict*)
       apply(simp only: setAConcat setBConcat concat_asso)
       apply(clarsimp)
       apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead K))"
      and s="{}"
      in ssubst)
        apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d p)(*strict*)
        apply(rule setA_liftB)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d p)(*strict*)
       apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead K))"
      and s="set (cfg_item_look_ahead K)"
      in ssubst)
        apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d p)(*strict*)
        apply(rule sym)
        apply(rule liftB_BiElem)
       apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d p)(*strict*)
       apply(clarsimp)
      apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
      apply(force)
     apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
     apply(simp add: derivation_append_def)
     apply(simp add: der2_def)
    apply(rename_tac G F k N I n w e K B wa \<beta> x e1 na da d)(*strict*)
    apply(thin_tac "cfgSTD.derivation G da")
    apply(thin_tac "maximum_of_domain da na")
    apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>)")
    apply(thin_tac "da na = Some (pair e1 \<lparr>cfg_conf = teA B # liftB x\<rparr>)")
    apply(thin_tac "cfgLM.belongs G da")
    apply(clarsimp)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
    apply(rule_tac
      x="derivation_append da d (Suc na)"
      in exI)
    apply(rule_tac
      x="(Suc na)+n"
      in exI)
    apply(rule conjI)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(rule_tac concat_has_max_dom)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(force)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(rule cfgSTD.derivation_concat2)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
        apply(force)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(force)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="liftB (take k x) @ liftB (drop k x)"
      and s="liftB (take k x @ (drop k x))"
      in subst)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(rule liftB_commutes_over_concat)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
    apply(rule conjI)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(rule cfgSTD.derivation_belongs)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
       apply(simp add: derivation_append_def)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(rule_tac
      t="teA B # \<beta> @ liftB (cfg_item_look_ahead K)"
      and s="cfg_item_rhs2 K @ liftB (cfg_item_look_ahead K)"
      in ssubst)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(thin_tac "cfg_item_rhs2 K = teA B # \<beta>")
      apply(subgoal_tac "valid_item G k K")
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
       prefer 2
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(simp add: cfg_configurations_def valid_item_def)
      apply(clarsimp)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
      apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
      apply(simp only: setAConcat setBConcat concat_asso)
      apply(clarsimp)
      apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead K))"
      and s="{}"
      in ssubst)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
      apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead K))"
      and s="set (cfg_item_look_ahead K)"
      in ssubst)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
       apply(rule sym)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
    apply(simp add: derivation_append_def)
    apply(clarsimp)
    apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
    apply(rule_tac
      x="w@liftB (drop k x)"
      in exI)
    apply(rule_tac
      t="cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w @ liftB (drop k x)"
      and s="wa @ liftB (take k x)@ liftB (drop k x)"
      in ssubst)
     apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
    apply(simp (no_asm))
    apply(rule_tac
      t="liftB (take k x) @ liftB (drop k x)"
      and s="liftB (take k x @ (drop k x))"
      in subst)
     apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
     apply(rule liftB_commutes_over_concat)
    apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(force)
  apply(rename_tac G F k N I)(*strict*)
  apply(thin_tac "\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k N - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N. \<exists>J \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N. \<exists>d n. maximum_of_domain d n \<and> cfgSTD.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> (\<exists>w e. d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>))")
  apply(rename_tac G F k N I)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>J \<in> N. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k J")
   apply(rename_tac G F k N I)(*strict*)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_F_VALID_ITEM_SET_GOTO__descent__fp_one_1_elem)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  apply(rename_tac G F k N I)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N I J)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  apply(erule disjE)
   apply(rename_tac G F k N I J)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k N I J)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N J B w z \<beta>)(*strict*)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in in_F__implies__in_cfgSTD_first)
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(force)
     prefer 3
     apply(force)
    apply(subgoal_tac "valid_item G k J")
     prefer 2
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="p" in ballE)
     prefer 2
     apply(force)
    apply(simp add: valid_item_def simpY valid_cfg_def)
    apply(force)
   apply(subgoal_tac "valid_item G k J")
    prefer 2
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac x="p" in ballE)
    prefer 2
    apply(force)
   apply(simp add: valid_item_def simpY valid_cfg_def)
   apply(force)
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
  apply(rule_tac
      x="J"
      in bexI)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(simp_all)
    (*
  d
  0 : \<beta> . (la J)
  n : x

  B \<rightarrow> w

  d?
  0 : B . \<beta> . (la J)
  n?: w. (k:x) . wa?

  take wa=(x:k) . (la J)
*)
  apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
  apply(subgoal_tac "\<exists>d. maximum_of_domain d n \<and> cfgSTD.derivation G d \<and> cfgSTD.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf = teA B # liftB x\<rparr>) ")
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=teA B#(cfg_conf c)\<rparr>)"
      in exI)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    apply(rule cfgSTD.derivation_map_preserves_derivation2)
     apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x d e1 n a e b l r)(*strict*)
    apply(rule_tac
      x="teA B#l"
      in exI)
    apply(rule_tac
      x="r"
      in exI)
    apply(clarsimp)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    apply(rule cfgSTD.derivation_map_preserves_belongs)
        apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
       apply(rule cfgSTD.derivation_belongs)
          apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
          apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
         apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
         apply(force)
        apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
        apply(simp add: cfg_configurations_def)
        apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
        apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead J))"
      and s="{}"
      in ssubst)
         apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
         apply(rule setA_liftB)
        apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
        apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead J))"
      and s="set (cfg_item_look_ahead J)"
      in ssubst)
         apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
         apply(rule sym)
         apply(rule liftB_BiElem)
        apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
        apply(clarsimp)
        apply(subgoal_tac "valid_item G k J")
         apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
         prefer 2
         apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
        apply(simp add: valid_item_def)
        apply(clarsimp)
        apply(rename_tac G F k N J B w \<beta> x d e1 n p)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(simp add: valid_cfg_def)
        apply(clarsimp)
        apply(erule_tac
      x="p"
      in ballE)
         apply(rename_tac G F k N J B w \<beta> x d e1 n p)(*strict*)
         apply(clarsimp)
         apply(simp add: setAConcat setBConcat concat_asso)
        apply(rename_tac G F k N J B w \<beta> x d e1 n p)(*strict*)
        apply(clarsimp)
       apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
       apply(force)
      apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
     apply(rule cfgSTD.derivation_map_preserves_derivation2)
      apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac G F k N J B w \<beta> x d e1 n a e b l r)(*strict*)
     apply(rule_tac
      x="teA B#l"
      in exI)
     apply(rule_tac
      x="r"
      in exI)
     apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x d e1 n c)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x d e1 n ca)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>prod_lhs = B, prod_rhs = w\<rparr>"
      in ballE)
     apply(rename_tac G F k N J B w \<beta> x d e1 n ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x d e1 n ca)(*strict*)
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
  apply(thin_tac "d n = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>)")
  apply(thin_tac "cfgSTD.derivation G d")
  apply(thin_tac "maximum_of_domain d n")
  apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = teA B # liftB x\<rparr> \<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<lparr>cfg_conf = w @ liftB x\<rparr>) n"
      in exI)
  apply(rule_tac
      x="n+Suc 0"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(rule cfgSTD.derivation_concat2)
      apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(rule cfgSTD.der2_is_derivation)
    apply(simp add: cfgSTD_step_relation_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="liftB x"
      in exI)
    apply(clarsimp)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
  apply(rule conjI)
   apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     apply(simp add: derivation_append_def)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(rule_tac
      t="teA B # \<beta> @ liftB (cfg_item_look_ahead J)"
      and s="cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)"
      in ssubst)
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(thin_tac "cfg_item_rhs2 J = teA B # \<beta>")
    apply(subgoal_tac "valid_item G k J")
     apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
     prefer 2
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
    apply(simp add: cfg_configurations_def valid_item_def)
    apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
    apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="p"
      in ballE)
     apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
     apply(clarsimp)
   prefer 2
   apply(force)
  apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
  apply(simp only: setAConcat setBConcat concat_asso)
  apply(clarsimp)
  apply(rule_tac
    t="setA (liftB (cfg_item_look_ahead J))"
    and s="{}"
    in ssubst)
   apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
   apply(rule setA_liftB)
  apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
  apply(rule_tac
    t="setB (liftB (cfg_item_look_ahead J))"
    and s="set (cfg_item_look_ahead J)"
    in ssubst)
   apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
   apply(rule sym)
   apply(rule liftB_BiElem)
  apply(rename_tac G F k N J B w \<beta> x e1 n d p)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
  apply(force)
  apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rule_tac
    x="liftB(drop k x)"
    in exI)
  apply(rule_tac
    t="liftB (take k x) @ liftB (drop k x)"
    and s="liftB (take k x @ (drop k x))"
    in subst)
  apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
  apply(rule liftB_commutes_over_concat)
  apply(rename_tac G F k N J B w \<beta> x e1 n d)(*strict*)
  apply(simp add: der2_def)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_origin_derivation_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> S \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S - S
  \<Longrightarrow> \<exists>J \<in> S. \<exists>d n w e. maximum_of_domain d n \<and> cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)"
  apply(case_tac "S=F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
   apply(clarsimp)
  apply(subgoal_tac "cfgSTD_first_compatible F k \<longrightarrow> (S \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k S) \<longrightarrow> (\<forall>I \<in> (F_VALID_ITEM_SET_GOTO__descent__fp G F k S)-S. \<exists>J \<in> S. (\<exists>d n w e e'. maximum_of_domain d n \<and> cfgRM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)))")
   apply(force)
  apply(thin_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S - S")
  apply(thin_tac "S \<noteq> F_VALID_ITEM_SET_GOTO__descent__fp G F k S")
  apply(rule_tac
      G="G"
      and k="k"
      and N="S"
      in F_VALID_ITEM_SET_GOTO__descent__fp_Meta_Lift_prime)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(force)
   apply(rename_tac Ga Fa ka N)(*strict*)
   prefer 2
   apply(rename_tac Ga Fa ka N)(*strict*)
   apply(thin_tac "valid_cfg G")
   apply(thin_tac "S \<subseteq> Collect (valid_item G k)")
   apply(thin_tac "cfgSTD_first_compatible F k")
   apply(rename_tac G F k N)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k N = N")
    apply(rename_tac G F k N I)(*strict*)
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k N"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS))" for SSG SSF SSk SSS
      in ssubst)
    apply(rename_tac G F k N I)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga Fa ka N)(*strict*)
  apply(thin_tac "valid_cfg G")
  apply(thin_tac "S \<subseteq> Collect (valid_item G k)")
  apply(thin_tac "cfgSTD_first_compatible F k")
  apply(rename_tac G F k N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N I)(*strict*)
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
    apply(rename_tac G F k N I)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N = F_VALID_ITEM_SET_GOTO__descent__fp G F k N")
   apply(subgoal_tac "\<exists>J \<in> N. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k J")
    apply(rename_tac G F k N I)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_F_VALID_ITEM_SET_GOTO__descent__fp_one_1_elem)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N I J)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
   apply(erule disjE)
    apply(rename_tac G F k N I J)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k N I J)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k N J B w z \<beta>)(*strict*)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G" in in_F__implies__in_cfgSTD_first)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(force)
      prefer 3
      apply(force)
     apply(subgoal_tac "valid_item G k J")
      prefer 2
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac x="p" in ballE)
      prefer 2
      apply(force)
     apply(simp add: valid_item_def simpY valid_cfg_def)
     apply(force)
    apply(subgoal_tac "valid_item G k J")
     prefer 2
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="p" in ballE)
     prefer 2
     apply(force)
    apply(simp add: valid_item_def simpY valid_cfg_def)
    apply(force)
   apply(simp add: cfgSTD_first_def)
   apply(clarsimp)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(subgoal_tac "\<exists>d e. cfgRM.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB x\<rparr>)")
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    prefer 2
    apply(rule cfg_derivation_can_be_translated_to_cfgRM_derivation)
         apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
         apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
        apply(force)
       apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
       apply(force)
      apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(thin_tac "cfgSTD.derivation G d")
   apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>)")
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(thin_tac "d n = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
   apply(thin_tac "maximum_of_domain d n")
   apply(clarsimp)
   apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgRM.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = teA B # liftB x\<rparr>) ")
    apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
    prefer 2
    apply(rule_tac
      x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=teA B#(cfg_conf c)\<rparr>)"
      in exI)
    apply(rule conjI)
     apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
     apply(rule cfgRM.derivation_map_preserves_derivation2)
      apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac G F k N J B w \<beta> x n d e a ea b l r)(*strict*)
     apply(rule_tac
      x="teA B#l"
      in exI)
     apply(rule_tac
      x="r"
      in exI)
     apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
    apply(rule conjI)
     apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
   apply(thin_tac "cfgRM.derivation G d")
   apply(thin_tac "maximum_of_domain d n")
   apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>)")
   apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = liftB x\<rparr>)")
   apply(clarsimp)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(rule_tac
      x="J"
      in bexI)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = teA B # liftB x\<rparr> \<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<lparr>cfg_conf = w @ liftB x\<rparr>) n"
      in exI)
   apply(rule_tac
      x="Suc n"
      in exI)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(rule_tac
      t="Suc n"
      and s="n+Suc 0"
      in ssubst)
     apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(rule_tac concat_has_max_dom)
     apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(simp add: maximum_of_domain_def)
    apply(rule conjI)
     apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(rule cfgRM.derivation_concat2)
       apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
       apply(force)
      apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
     apply(rule cfgRM.der2_is_derivation)
     apply(simp add: cfgRM_step_relation_def)
     apply(rule_tac
      x="[]"
      in exI)
     apply(rule_tac
      x="liftB x"
      in exI)
     apply(clarsimp)
     apply(rule setA_liftB)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(rule cfgRM.derivation_belongs)
       apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
      apply(simp add: derivation_append_def)
     apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: setAConcat setBConcat concat_asso)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(clarsimp)
     apply(erule_tac
      x="J"
      and A="N"
      in ballE)
      apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
      apply(simp add: valid_item_def)
      apply(clarsimp)
      apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(force)
      apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
      apply(simp only: setAConcat setBConcat concat_asso)
      apply(clarsimp)
      apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead J))"
      and s="{}"
      in ssubst)
       apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
      apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead J))"
      and s="set (cfg_item_look_ahead J)"
      in ssubst)
       apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
       apply(rule sym)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(simp add: derivation_append_def)
   apply(rule_tac
      x="liftB (drop k x)"
      in exI)
   apply(rule_tac
      t="liftB (take k x) @ liftB (drop k x)"
      and s="liftB (take k x @ (drop k x))"
      in subst)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac G F k N I)(*strict*)
  apply(clarsimp)
  apply(case_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k N - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N")
   apply(rename_tac G F k N I)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="I"
      in ballE)
    apply(rename_tac G F k N I)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N I J d n w e)(*strict*)
    apply(subgoal_tac "\<exists>K \<in> N. J \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k K")
     apply(rename_tac G F k N I J d n w e)(*strict*)
     prefer 2
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_F_VALID_ITEM_SET_GOTO__descent__fp_one_1_elem)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
    apply(rename_tac G F k N I J d n w e)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N I J d n w e K)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
    apply(erule disjE)
     apply(rename_tac G F k N I J d n w e K)(*strict*)
     apply(clarsimp)
     apply(rename_tac G F k N I d n w e K)(*strict*)
     apply(rule_tac
      x="K"
      in bexI)
      apply(rename_tac G F k N I d n w e K)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G F k N I d n w e K)(*strict*)
     apply(rule_tac
      x="d"
      in exI)
     apply(rule_tac
      x="n"
      in exI)
     apply(clarsimp)
    apply(rename_tac G F k N I J d n w e K)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k N I d n w e K B wa z \<beta>)(*strict*)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac G="G" in in_F__implies__in_cfgSTD_first)
         apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(force)
       prefer 3
       apply(force)
      apply(subgoal_tac "valid_item G k K")
       prefer 2
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac x="p" in ballE)
       prefer 2
       apply(force)
      apply(simp add: valid_item_def simpY valid_cfg_def)
      apply(force)
     apply(subgoal_tac "valid_item G k K")
      prefer 2
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac x="p" in ballE)
      prefer 2
      apply(force)
     apply(simp add: valid_item_def simpY valid_cfg_def)
     apply(force)
    apply(simp add: cfgSTD_first_def)
    apply(clarsimp)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
    apply(subgoal_tac "\<exists>d e. cfgRM.derivation G d \<and> maximum_of_domain d na \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>) \<and> d na = Some (pair e \<lparr>cfg_conf = liftB x\<rparr>)")
     apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
     prefer 2
     apply(rule cfg_derivation_can_be_translated_to_cfgRM_derivation)
          apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
          apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
         apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
         apply(force)
        apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
        apply(force)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
      apply(force)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
     apply(rule setA_liftB)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
    apply(thin_tac "cfgSTD.derivation G da")
    apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>)")
    apply(rename_tac G F k N I d n w e K B wa \<beta> x da e1 na)(*strict*)
    apply(thin_tac "da na = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
    apply(thin_tac "maximum_of_domain da na")
    apply(clarsimp)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgRM.derivation G d \<and> maximum_of_domain d na \<and> d 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>) \<and> d na = Some (pair ea \<lparr>cfg_conf = teA B # liftB x\<rparr>) ")
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_map da (\<lambda>c. \<lparr>cfg_conf=teA B#(cfg_conf c)\<rparr>)"
      in exI)
     apply(rule conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
      apply(rule cfgRM.derivation_map_preserves_derivation2)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
      apply(simp add: cfgRM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea a eb b l r)(*strict*)
      apply(rule_tac
      x="teA B#l"
      in exI)
      apply(rule_tac
      x="r"
      in exI)
      apply(clarsimp)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
     apply(rule conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(force)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
     apply(simp add: derivation_map_def)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x na da ea)(*strict*)
    apply(thin_tac "cfgRM.derivation G da")
    apply(thin_tac "maximum_of_domain da na")
    apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>)")
    apply(thin_tac "da na = Some (pair ea \<lparr>cfg_conf = liftB x\<rparr>)")
    apply(clarsimp)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
    apply(rule_tac
      x="K"
      in bexI)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
    apply(subgoal_tac "cfgRM.belongs G da")
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
     prefer 2
     apply(rule cfgRM.derivation_belongs)
        apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
       apply(clarsimp)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
      apply(rule_tac
      t="teA B # \<beta> @ liftB (cfg_item_look_ahead K)"
      and s="cfg_item_rhs2 K @ liftB (cfg_item_look_ahead K)"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
      apply(thin_tac "cfg_item_rhs2 K = teA B # \<beta>")
      apply(subgoal_tac "valid_item G k K")
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
       prefer 2
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
      apply(simp add: cfg_configurations_def valid_item_def)
      apply(clarsimp)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da p)(*strict*)
      apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da p)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da p)(*strict*)
      apply(simp only: setAConcat setBConcat concat_asso)
      apply(clarsimp)
      apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead K))"
      and s="{}"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da p)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da p)(*strict*)
      apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead K))"
      and s="set (cfg_item_look_ahead K)"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da p)(*strict*)
       apply(rule sym)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da p)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
    apply(subgoal_tac "\<exists>d. cfgRM.derivation G d \<and> maximum_of_domain d n \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = wa @ liftB (take k x) @ liftB (drop k x)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w @ liftB (drop k x)\<rparr>) ")
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=(cfg_conf c)@(liftB (drop k x))\<rparr>)"
      in exI)
     apply(rule context_conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
      apply(rule cfgRM.derivation_map_preserves_derivation2)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
      apply(simp add: cfgRM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da a eb b l r)(*strict*)
      apply(rule_tac
      x="l"
      in exI)
      apply(rule_tac
      x="r @ liftB (drop k x)"
      in exI)
      apply(clarsimp)
      apply(simp (no_asm) only: setAConcat concat_asso)
      apply(clarsimp)
      apply(rule setA_liftB)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
     apply(rule conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(force)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
     apply(rule conjI)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
      apply(rule cfgRM.derivation_map_preserves_belongs)
          apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
          apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
         apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
         apply(force)
        apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
        apply(force)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da c)(*strict*)
      apply(simp add: cfgRM.belongs_def)
      apply(erule_tac
      x="na"
      and P="\<lambda>na. case da na of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> cfg_step_labels G) \<and> c \<in> cfg_configurations G"
      in allE)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da c)(*strict*)
      apply(clarsimp)
      apply(simp add: cfg_configurations_def)
      apply(clarsimp)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
      apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
      apply(clarsimp)
      apply(rule_tac
      t="setA (liftB (drop k x))"
      and s="{}"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
      apply(rule_tac
      t="setB (liftB (drop k x))"
      and s="set (drop k x)"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
       apply(rule sym)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
      apply(rule conjI)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
       apply(force)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
      apply(rule_tac
      B="set x"
      in subset_trans)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
       apply(rule set_drop_subset)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
      apply(rule_tac
      t="set x"
      and s="setB (liftB x)"
      in ssubst)
       apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da ca)(*strict*)
      apply(force)
     apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
     apply(simp add: derivation_map_def)
    apply(rename_tac G F k N I d n w e K B wa \<beta> x na ea da)(*strict*)
    apply(thin_tac "maximum_of_domain d n")
    apply(thin_tac "cfgRM.derivation G d")
    apply(thin_tac "cfgLM.belongs G d")
    apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = wa @ liftB (take k x)\<rparr>)")
    apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)")
    apply(clarsimp)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
    apply(subgoal_tac "\<exists>d. maximum_of_domain d (Suc na) \<and> cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>) \<and> d (Suc na) = Some (pair (Some \<lparr>prod_lhs = B, prod_rhs = wa\<rparr>) \<lparr>cfg_conf = wa @ liftB x\<rparr>) ")
     apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
     prefer 2
     apply(rule_tac
      x="derivation_append da (der2 \<lparr>cfg_conf = teA B # liftB x\<rparr> \<lparr>prod_lhs = B, prod_rhs = wa\<rparr> \<lparr>cfg_conf = wa @ liftB x\<rparr>) na"
      in exI)
     apply(rule context_conjI)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
      apply(rule_tac
      t="Suc na"
      and s="na+Suc 0"
      in ssubst)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
      apply(rule_tac concat_has_max_dom)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
      apply(rule der2_maximum_of_domain)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
     apply(rule context_conjI)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
      apply(rule cfgRM.derivation_concat2)
         apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
         apply(force)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
        apply(force)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
       apply(rule cfgRM.der2_is_derivation)
       apply(simp add: cfgRM_step_relation_def)
       apply(rule_tac
      x="[]"
      in exI)
       apply(rule_tac
      x="liftB x"
      in exI)
       apply(clarsimp)
       apply(rule setA_liftB)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
      apply(simp add: der2_def)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
     apply(rule conjI)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
      apply(rule cfgRM.derivation_belongs)
         apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
         apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
        apply(simp add: derivation_append_def)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
       apply(rule_tac
      t="teA B # \<beta> @ liftB (cfg_item_look_ahead K)"
      and s="cfg_item_rhs2 K @ liftB (cfg_item_look_ahead K)"
      in ssubst)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
        apply(force)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
       apply(thin_tac "cfg_item_rhs2 K = teA B # \<beta>")
       apply(subgoal_tac "valid_item G k K")
        apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
        prefer 2
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
       apply(simp add: cfg_configurations_def valid_item_def)
       apply(clarsimp)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d p)(*strict*)
       apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(simp add: valid_cfg_def)
       apply(clarsimp)
       apply(erule_tac
      x="p"
      in ballE)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d p)(*strict*)
        apply(clarsimp)
        prefer 2
        apply(force)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d p)(*strict*)
       apply(simp only: setAConcat setBConcat concat_asso)
       apply(clarsimp)
       apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead K))"
      and s="{}"
      in ssubst)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d p)(*strict*)
        apply(rule setA_liftB)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d p)(*strict*)
       apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead K))"
      and s="set (cfg_item_look_ahead K)"
      in ssubst)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d p)(*strict*)
        apply(rule sym)
        apply(rule liftB_BiElem)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d p)(*strict*)
       apply(clarsimp)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
      apply(force)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
     apply(simp add: derivation_append_def)
     apply(simp add: der2_def)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na ea da d)(*strict*)
    apply(thin_tac "cfgRM.derivation G da")
    apply(thin_tac "maximum_of_domain da na")
    apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead K)\<rparr>)")
    apply(thin_tac "da na = Some (pair ea \<lparr>cfg_conf = teA B # liftB x\<rparr>)")
    apply(thin_tac "cfgLM.belongs G da")
    apply(clarsimp)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
    apply(rule_tac
      x="derivation_append da d (Suc na)"
      in exI)
    apply(rule_tac
      x="(Suc na)+n"
      in exI)
    apply(rule conjI)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(rule_tac concat_has_max_dom)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(force)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(rule cfgRM.derivation_concat2)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
        apply(force)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(force)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="liftB (take k x) @ liftB (drop k x)"
      and s="liftB (take k x @ (drop k x))"
      in subst)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(rule liftB_commutes_over_concat)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
    apply(rule conjI)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(rule cfgRM.derivation_belongs)
        apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
       apply(simp add: derivation_append_def)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(rule_tac
      t="teA B # \<beta> @ liftB (cfg_item_look_ahead K)"
      and s="cfg_item_rhs2 K @ liftB (cfg_item_look_ahead K)"
      in ssubst)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(thin_tac "cfg_item_rhs2 K = teA B # \<beta>")
      apply(subgoal_tac "valid_item G k K")
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
       prefer 2
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
      apply(simp add: cfg_configurations_def valid_item_def)
      apply(clarsimp)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
      apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
      apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(force)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
      apply(simp only: setAConcat setBConcat concat_asso)
      apply(clarsimp)
      apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead K))"
      and s="{}"
      in ssubst)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
      apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead K))"
      and s="set (cfg_item_look_ahead K)"
      in ssubst)
       apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
       apply(rule sym)
       apply(rule liftB_BiElem)
      apply(rename_tac G F k N I n w e K B wa \<beta> x na d da p)(*strict*)
      apply(clarsimp)
     apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I n w e K B wa \<beta> x na d da)(*strict*)
    apply(simp add: derivation_append_def)
    apply(clarsimp)
    apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
    apply(rule_tac
      x="w@liftB (drop k x)"
      in exI)
    apply(rule_tac
      t="cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w @ liftB (drop k x)"
      and s="wa @ liftB (take k x)@ liftB (drop k x)"
      in ssubst)
     apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
     apply(force)
    apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
    apply(simp (no_asm))
    apply(rule_tac
      t="liftB (take k x) @ liftB (drop k x)"
      and s="liftB (take k x @ (drop k x))"
      in subst)
     apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
     apply(rule liftB_commutes_over_concat)
    apply(rename_tac G F k N I w K B wa \<beta> x na d da)(*strict*)
    apply(force)
   apply(rename_tac G F k N I)(*strict*)
   apply(force)
  apply(rename_tac G F k N I)(*strict*)
  apply(thin_tac "\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k N - F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N. \<exists>J \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k N. \<exists>d n. maximum_of_domain d n \<and> cfgRM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> (\<exists>w e. d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>))")
  apply(rename_tac G F k N I)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>J \<in> N. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp_one_1 G F k J")
   apply(rename_tac G F k N I)(*strict*)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_F_VALID_ITEM_SET_GOTO__descent__fp_one_1_elem)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  apply(rename_tac G F k N I)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N I J)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  apply(erule disjE)
   apply(rename_tac G F k N I J)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k N I J)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N J B w z \<beta>)(*strict*)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G" in in_F__implies__in_cfgSTD_first)
       apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
      apply(force)
     prefer 3
     apply(force)
    apply(subgoal_tac "valid_item G k J")
     prefer 2
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac x="p" in ballE)
     prefer 2
     apply(force)
    apply(simp add: valid_item_def simpY valid_cfg_def)
    apply(force)
   apply(subgoal_tac "valid_item G k J")
    prefer 2
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def valid_item_def simpY valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac x="p" in ballE)
    prefer 2
    apply(force)
   apply(simp add: valid_item_def simpY valid_cfg_def)
   apply(force)
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
  apply(subgoal_tac "\<exists>d e. cfgRM.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB x\<rparr>)")
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   prefer 2
   apply(rule cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
       apply(force)
      apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
   apply(rule setA_liftB)
  apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
  apply(thin_tac "cfgSTD.derivation G d")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>)")
  apply(rename_tac G F k N J B w \<beta> x d e1 n)(*strict*)
  apply(thin_tac "d n = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
  apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
  apply(rule_tac
      x="J"
      in bexI)
   apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
   apply(simp_all)
    (*
  d
  0 : \<beta> . (la J)
  n : x

  B \<rightarrow> w

  d?
  0 : B . \<beta> . (la J)
  n?: w. (k:x) . wa?

  take wa=(x:k) . (la J)
*)
  apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
  apply(subgoal_tac "\<exists>d. maximum_of_domain d n \<and> cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = teA B # \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = teA B # liftB x\<rparr>) ")
   apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=teA B#(cfg_conf c)\<rparr>)"
      in exI)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_derivation2)
     apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
     apply(force)
    apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x n d e a ea b l r)(*strict*)
    apply(rule_tac
      x="teA B#l"
      in exI)
    apply(rule_tac
      x="r"
      in exI)
    apply(clarsimp)
   apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
   apply(rule conjI)
    apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_belongs)
        apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
       apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
       apply(rule cfgRM.derivation_belongs)
          apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
          apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
         apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
         apply(force)
        apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
        apply(simp add: cfg_configurations_def)
        apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
        apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead J))"
      and s="{}"
      in ssubst)
         apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
         apply(rule setA_liftB)
        apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
        apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead J))"
      and s="set (cfg_item_look_ahead J)"
      in ssubst)
         apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
         apply(rule sym)
         apply(rule liftB_BiElem)
        apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
        apply(clarsimp)
        apply(subgoal_tac "valid_item G k J")
         apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
         prefer 2
         apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
        apply(simp add: valid_item_def)
        apply(clarsimp)
        apply(rename_tac G F k N J B w \<beta> x n d e p)(*strict*)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(simp add: valid_cfg_def)
        apply(clarsimp)
        apply(erule_tac
      x="p"
      in ballE)
         apply(rename_tac G F k N J B w \<beta> x n d e p)(*strict*)
         apply(clarsimp)
         apply(simp add: setAConcat setBConcat concat_asso)
        apply(rename_tac G F k N J B w \<beta> x n d e p)(*strict*)
        apply(clarsimp)
       apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
       apply(force)
      apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
     apply(rule cfgRM.derivation_map_preserves_derivation2)
      apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
      apply(force)
     apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac G F k N J B w \<beta> x n d e a ea b l r)(*strict*)
     apply(rule_tac
      x="teA B#l"
      in exI)
     apply(rule_tac
      x="r"
      in exI)
     apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x n d e c)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac G F k N J B w \<beta> x n d e ca)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>prod_lhs = B, prod_rhs = w\<rparr>"
      in ballE)
     apply(rename_tac G F k N J B w \<beta> x n d e ca)(*strict*)
     apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x n d e ca)(*strict*)
  apply(force)
  apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac G F k N J B w \<beta> x n d e)(*strict*)
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = liftB x\<rparr>)")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB (cfg_item_look_ahead J)\<rparr>)")
  apply(thin_tac "cfgRM.derivation G d")
  apply(thin_tac "maximum_of_domain d n")
  apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule_tac
    x="derivation_append d (der2 \<lparr>cfg_conf = teA B # liftB x\<rparr> \<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<lparr>cfg_conf = w @ liftB x\<rparr>) n"
    in exI)
  apply(rule_tac
    x="n+Suc 0"
    in exI)
  apply(rule context_conjI)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule_tac concat_has_max_dom)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(force)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule der2_maximum_of_domain)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule cfgRM.derivation_concat2)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(force)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(force)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule cfgRM.der2_is_derivation)
  apply(simp add: cfgRM_step_relation_def)
  apply(rule_tac
    x="[]"
    in exI)
  apply(rule_tac
    x="liftB x"
    in exI)
  apply(clarsimp)
  apply(rule setA_liftB)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule conjI)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule cfgRM.derivation_belongs)
    apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule_tac
    t="teA B # \<beta> @ liftB (cfg_item_look_ahead J)"
    and s="cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)"
    in ssubst)
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   apply(force)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(thin_tac "cfg_item_rhs2 J = teA B # \<beta>")
  apply(subgoal_tac "valid_item G k J")
   apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
   prefer 2
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(simp add: cfg_configurations_def valid_item_def)
  apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
  apply(simp (no_asm) add: setAConcat setBConcat concat_asso)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
    x="p"
    in ballE)
   apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(force)
  apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
  apply(simp only: setAConcat setBConcat concat_asso)
  apply(clarsimp)
  apply(rule_tac
    t="setA (liftB (cfg_item_look_ahead J))"
    and s="{}"
    in ssubst)
   apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
   apply(rule setA_liftB)
  apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
  apply(rule_tac
    t="setB (liftB (cfg_item_look_ahead J))"
    and s="set (cfg_item_look_ahead J)"
    in ssubst)
   apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
   apply(rule sym)
   apply(rule liftB_BiElem)
  apply(rename_tac G F k N J B w \<beta> x n e d p)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(force)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rule_tac
    x="liftB(drop k x)"
    in exI)
  apply(rule_tac
    t="liftB (take k x) @ liftB (drop k x)"
    and s="liftB (take k x @ (drop k x))"
    in subst)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(rule liftB_commutes_over_concat)
  apply(rename_tac G F k N J B w \<beta> x n e d)(*strict*)
  apply(simp add: der2_def)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_origin_derivation2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> S \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S
  \<Longrightarrow> \<exists>J \<in> S. \<exists>d n w e. maximum_of_domain d n \<and> cfgSTD.derivation G d \<and> cfgSTD.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)"
  apply(case_tac "I \<in> S")
   apply(rule_tac
      x="I"
      in bexI)
    apply(rule_tac
      x = "der1 \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I)\<rparr>"
      in exI)
    apply(rule_tac
      x="0"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="None"
      in exI)
    apply(rule conjI)
     apply(simp add: der1_maximum_of_domain)
    apply(rule conjI)
     apply(rule cfgSTD.der1_is_derivation)
    apply(rule conjI)
     apply(simp add: cfgSTD.belongs_def)
     apply(simp add: der1_def)
     apply(simp add: cfg_configurations_def)
     apply(subgoal_tac "valid_item G k I")
      apply(simp add: valid_item_def)
      apply(clarsimp)
      apply(rename_tac p)(*strict*)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac p)(*strict*)
       apply(clarsimp)
       apply(simp only: setAConcat setBConcat concat_asso)
       apply(clarsimp)
       apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead I))"
      and s="{}"
      in ssubst)
        apply(rename_tac p)(*strict*)
        apply(rule setA_liftB)
       apply(rename_tac p)(*strict*)
       apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead I))"
      and s="set (cfg_item_look_ahead I)"
      in ssubst)
        apply(rename_tac p)(*strict*)
        apply(rule sym)
        apply(rule liftB_BiElem)
       apply(rename_tac p)(*strict*)
       apply(clarsimp)
      apply(rename_tac p)(*strict*)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(simp add: der1_def)
   apply(force)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_origin_derivation)
     apply(force)+
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_origin_derivation2_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> S \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S
  \<Longrightarrow> \<exists>J \<in> S. \<exists>d n w e. maximum_of_domain d n \<and> cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J)\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)"
  apply(case_tac "I \<in> S")
   apply(rule_tac
      x="I"
      in bexI)
    apply(rule_tac
      x = "der1 \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I)\<rparr>"
      in exI)
    apply(rule_tac
      x="0"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="None"
      in exI)
    apply(rule conjI)
     apply(rule der1_maximum_of_domain)
    apply(rule conjI)
     apply(rule cfgRM.der1_is_derivation)
    apply(rule conjI)
     apply(simp add: cfgSTD.belongs_def)
     apply(simp add: der1_def)
     apply(simp add: cfg_configurations_def)
     apply(subgoal_tac "valid_item G k I")
      apply(simp add: valid_item_def)
      apply(clarsimp)
      apply(rename_tac p)(*strict*)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac p)(*strict*)
       apply(clarsimp)
       apply(simp only: setAConcat setBConcat concat_asso)
       apply(clarsimp)
       apply(rule_tac
      t="setA (liftB (cfg_item_look_ahead I))"
      and s="{}"
      in ssubst)
        apply(rename_tac p)(*strict*)
        apply(rule setA_liftB)
       apply(rename_tac p)(*strict*)
       apply(rule_tac
      t="setB (liftB (cfg_item_look_ahead I))"
      and s="set (cfg_item_look_ahead I)"
      in ssubst)
        apply(rename_tac p)(*strict*)
        apply(rule sym)
        apply(rule liftB_BiElem)
       apply(rename_tac p)(*strict*)
       apply(clarsimp)
      apply(rename_tac p)(*strict*)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(simp add: der1_def)
   apply(force)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_origin_derivation_prime)
     apply(force)+
  done

lemma GOTO_preserves_Sentential: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_item G k J
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis x {J})
  \<Longrightarrow> Sentential G (xs @ cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J))
  \<Longrightarrow> Sentential G (xs @ x # cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I))"
  apply(subgoal_tac "\<exists>J'. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k {J'} \<and> J' \<in> F_VALID_ITEM_SET_GOTO__basis x {J}")
   prefer 2
   apply(case_tac "F_VALID_ITEM_SET_GOTO__basis x {J} = {}")
    apply(clarsimp)
    apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k {} = {}")
     apply(force)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_empty)
     apply(force)
    apply(force)
   apply(subgoal_tac "\<exists>J''. J'' \<in> F_VALID_ITEM_SET_GOTO__basis x {J}")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(rename_tac J'')(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
   apply(clarsimp)
   apply(rename_tac J'' xa)(*strict*)
   apply(subgoal_tac "J'' = xa")
    apply(rename_tac J'' xa)(*strict*)
    prefer 2
    apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
   apply(rename_tac J'' xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(clarsimp)
   apply(subgoal_tac "{xa}=Collect (F_VALID_ITEM_SET_GOTO__passes x J)")
    apply(rename_tac xa)(*strict*)
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa xaa)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(clarsimp)
  apply(rename_tac J')(*strict*)
  apply(subgoal_tac "cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J) = x#cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')")
   apply(rename_tac J')(*strict*)
   prefer 2
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(rename_tac J')(*strict*)
  apply(subgoal_tac "\<exists>J' \<in> {J'}. \<exists>d n w e. maximum_of_domain d n \<and> cfgSTD.derivation G d \<and> cfgSTD.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf=cfg_item_rhs2 J'@(liftB(cfg_item_look_ahead J'))\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf=cfg_item_rhs2 I@(liftB(cfg_item_look_ahead I))@w\<rparr>)")
   apply(rename_tac J')(*strict*)
   prefer 2
   apply(rule_tac
      k="k"
      in F_VALID_ITEM_SET_GOTO__descent__fp_origin_derivation2)
      apply(rename_tac J')(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac J')(*strict*)
    apply(rule_tac
      B="F_VALID_ITEM_SET_GOTO__basis x {J}"
      in subset_trans)
     apply(rename_tac J')(*strict*)
     apply(force)
    apply(rename_tac J')(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
    apply(force)
   apply(rename_tac J')(*strict*)
   apply(force)
  apply(rename_tac J')(*strict*)
  apply(clarsimp)
  apply(rename_tac J' d n w e)(*strict*)
  apply(simp add: Sentential_def)
  apply(clarsimp)
    (*
  d / 0:tail-J' \<Longrightarrow> n: tail-I @ w
  da / 0:S \<Longrightarrow> na: xs @ x # tail-J' @ v
  tail-J = x # tail-J'

  d? / 0:S \<Longrightarrow> n?: xs @ x # tail-I @ v?
*)
  apply(rename_tac J' d n w e da ea na v)(*strict*)
  apply(subgoal_tac "\<exists>d'. (cfgSTD.derivation G d' \<and> cfgSTD.belongs G d' \<and> cfgSTD.derivation_initial G d' \<and> d' na = Some (pair ea \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ v\<rparr>)) \<and> maximum_of_domain d' na")
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   prefer 2
   apply(rule_tac
      d="da"
      in derivation_extend_with_maximum_of_domain)
     apply(rename_tac J' d n w e da ea na v)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e da ea na v)(*strict*)
    apply(force)
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e da ea na v)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e da ea na v)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e da ea na v)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac J' d n w e da ea na v)(*strict*)
  apply(thin_tac "cfgSTD.derivation G da")
  apply(thin_tac "cfgLM.belongs G da")
  apply(thin_tac "cfgSTD.derivation_initial G da")
  apply(thin_tac "da na = Some (pair ea \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ v\<rparr>)")
  apply(clarsimp)
    (*
  d / 0:tail-J' \<Longrightarrow> n: tail-I @ w
  da / 0:S \<Longrightarrow> na: xs @ x # tail-J' @ v
  tail-J = x # tail-J'
  thus: da / 0:S \<Longrightarrow> na: xs @ tail-J @ v

  d? / 0:S \<Longrightarrow> n?: xs @ x # tail-I @ v?
*)
  apply(rename_tac J' d n w e ea na v d')(*strict*)
  apply(subgoal_tac "\<exists>d. maximum_of_domain d n \<and> cfgSTD.derivation G d \<and> cfgSTD.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')@v\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w@v\<rparr>)")
   apply(rename_tac J' d n w e ea na v d')(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=(xs@[x])@(cfg_conf c)@v\<rparr>)"
      in exI)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na v d')(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac J' d n w e ea na v d')(*strict*)
   apply(rule context_conjI)
    apply(rename_tac J' d n w e ea na v d')(*strict*)
    apply(rule cfgSTD.derivation_map_preserves_derivation2)
     apply(rename_tac J' d n w e ea na v d')(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d')(*strict*)
    apply(rule cfgSTD_step_relation_both_sides_context)
   apply(rename_tac J' d n w e ea na v d')(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na v d')(*strict*)
    apply(rule cfgSTD.derivation_map_preserves_belongs)
        apply(rename_tac J' d n w e ea na v d')(*strict*)
        apply(force)
       apply(rename_tac J' d n w e ea na v d')(*strict*)
       apply(force)
      apply(rename_tac J' d n w e ea na v d')(*strict*)
      apply(force)
     apply(rename_tac J' d n w e ea na v d')(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' c)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac J' d n w e ea na v d' ca)(*strict*)
    apply(rule_tac
      t="xs @ x # ca @ v"
      and s="xs @ [x] @ ca @ v"
      in ssubst)
     apply(rename_tac J' d n w e ea na v d' ca)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' ca)(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ v\<rparr> \<in> cfg_configurations G")
     apply(rename_tac J' d n w e ea na v d' ca)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp only: setAConcat setBConcat)
     apply(clarsimp)
     apply(simp only: setAConcat setBConcat)
     apply(clarsimp)
    apply(rename_tac J' d n w e ea na v d' ca)(*strict*)
    apply(rule_tac
      d="d'"
      and i="na"
      in cfgSTD.belongs_configurations)
     apply(rename_tac J' d n w e ea na v d' ca)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' ca)(*strict*)
    apply(force)
   apply(rename_tac J' d n w e ea na v d')(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na v d')(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac J' d n w e ea na v d')(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac J' d n w e ea na v d')(*strict*)
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "cfgSTD.derivation G d")
  apply(thin_tac "cfgSTD.belongs G d")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')\<rparr>)")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)")
  apply(clarsimp)
  apply(rename_tac J' n w e ea na v d' d)(*strict*)
  apply(rule_tac
      x="derivation_append d' d na"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac J' n w e ea na v d' d)(*strict*)
   apply(rule cfgSTD.derivation_concat2)
      apply(rename_tac J' n w e ea na v d' d)(*strict*)
      apply(force)
     apply(rename_tac J' n w e ea na v d' d)(*strict*)
     apply(force)
    apply(rename_tac J' n w e ea na v d' d)(*strict*)
    apply(force)
   apply(rename_tac J' n w e ea na v d' d)(*strict*)
   apply(clarsimp)
  apply(rename_tac J' n w e ea na v d' d)(*strict*)
  apply(rule conjI)
   apply(rename_tac J' n w e ea na v d' d)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_belongs)
     apply(rename_tac J' n w e ea na v d' d)(*strict*)
     apply(force)
    apply(rename_tac J' n w e ea na v d' d)(*strict*)
    apply(force)
   apply(rename_tac J' n w e ea na v d' d)(*strict*)
   apply(force)
  apply(rename_tac J' n w e ea na v d' d)(*strict*)
  apply(rule conjI)
   apply(rename_tac J' n w e ea na v d' d)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
     apply(rename_tac J' n w e ea na v d' d)(*strict*)
     apply(force)
    apply(rename_tac J' n w e ea na v d' d)(*strict*)
    apply(force)
   apply(rename_tac J' n w e ea na v d' d)(*strict*)
   apply(force)
  apply(rename_tac J' n w e ea na v d' d)(*strict*)
  apply(rule_tac
      x="if n=0 then ea else e"
      in exI)
  apply(rule_tac
      x="na+n"
      in exI)
  apply(rule_tac
      x="w@v"
      in exI)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  done

lemma GOTO_preserves_SententialRM: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> valid_item G k J
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__basis x {J})
  \<Longrightarrow> SententialRM G (xs @ cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J))
  \<Longrightarrow> SententialRM G (xs @ x # cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I))"
  apply(subgoal_tac "\<exists>J'. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k {J'} \<and> J' \<in> F_VALID_ITEM_SET_GOTO__basis x {J}")
   prefer 2
   apply(case_tac "F_VALID_ITEM_SET_GOTO__basis x {J} = {}")
    apply(clarsimp)
    apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k {} = {}")
     apply(force)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_empty)
     apply(force)
    apply(force)
   apply(subgoal_tac "\<exists>J''. J'' \<in> F_VALID_ITEM_SET_GOTO__basis x {J}")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(rename_tac J'')(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
   apply(clarsimp)
   apply(rename_tac J'' xa)(*strict*)
   apply(subgoal_tac "J'' = xa")
    apply(rename_tac J'' xa)(*strict*)
    prefer 2
    apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
   apply(rename_tac J'' xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(clarsimp)
   apply(subgoal_tac "{xa}=Collect (F_VALID_ITEM_SET_GOTO__passes x J)")
    apply(rename_tac xa)(*strict*)
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(rule order_antisym)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa xaa)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(clarsimp)
  apply(rename_tac J')(*strict*)
  apply(subgoal_tac "cfg_item_rhs2 J @ liftB (cfg_item_look_ahead J) = x#cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')")
   apply(rename_tac J')(*strict*)
   prefer 2
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(rename_tac J')(*strict*)
  apply(subgoal_tac "\<exists>J' \<in> {J'}. \<exists>d n w e. maximum_of_domain d n \<and> cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf=cfg_item_rhs2 J'@(liftB(cfg_item_look_ahead J'))\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf=cfg_item_rhs2 I@(liftB(cfg_item_look_ahead I))@w\<rparr>)")
   apply(rename_tac J')(*strict*)
   prefer 2
   apply(rule_tac k="k" in F_VALID_ITEM_SET_GOTO__descent__fp_origin_derivation2_prime)
      apply(rename_tac J')(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac J')(*strict*)
    apply(rule_tac
      B="F_VALID_ITEM_SET_GOTO__basis x {J}"
      in subset_trans)
     apply(rename_tac J')(*strict*)
     apply(force)
    apply(rename_tac J')(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
    apply(force)
   apply(rename_tac J')(*strict*)
   apply(force)
  apply(rename_tac J')(*strict*)
  apply(clarsimp)
  apply(rename_tac J' d n w e)(*strict*)
  apply(simp add: SententialRM_def)
  apply(clarsimp)
    (*
  d / 0:tail-J' \<Longrightarrow> n: tail-I @ w
  da / 0:S \<Longrightarrow> na: xs @ x # tail-J' @ v
  tail-J = x # tail-J'

  d? / 0:S \<Longrightarrow> n?: xs @ x # tail-I @ v?
*)
  apply(rename_tac J' d n w e da ea na v)(*strict*)
  apply(subgoal_tac "\<exists>d'. (cfgRM.derivation G d' \<and> cfgRM.belongs G d' \<and> cfgRM.derivation_initial G d' \<and> d' na = Some (pair ea \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ v\<rparr>)) \<and> maximum_of_domain d' na")
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   prefer 2
   apply(rule_tac
      d="da"
      in derivation_extend_with_maximum_of_domain)
     apply(rename_tac J' d n w e da ea na v)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e da ea na v)(*strict*)
    apply(force)
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e da ea na v)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e da ea na v)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e da ea na v)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac J' d n w e da ea na v)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac J' d n w e da ea na v)(*strict*)
  apply(thin_tac "cfgRM.derivation G da")
  apply(thin_tac "cfgLM.belongs G da")
  apply(thin_tac "cfgRM.derivation_initial G da")
  apply(thin_tac "da na = Some (pair ea \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ v\<rparr>)")
  apply(clarsimp)
    (*
  d / 0:tail-J' \<Longrightarrow> n: tail-I @ w
  da / 0:S \<Longrightarrow> na: xs @ x # tail-J' @ v
  tail-J = x # tail-J'
  thus: da / 0:S \<Longrightarrow> na: xs @ tail-J @ v

  d? / 0:S \<Longrightarrow> n?: xs @ x # tail-I @ v?
*)
  apply(rename_tac J' d n w e ea na v d')(*strict*)
  apply(subgoal_tac "\<exists>d' n' w e. maximum_of_domain d' n' \<and> cfgRM.derivation G d' \<and> cfgRM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=v\<rparr>) \<and> d' n' = Some (pair e \<lparr>cfg_conf=w\<rparr>) \<and> setA w = {}")
   apply(rename_tac J' d n w e ea na v d')(*strict*)
   prefer 2
   apply(rule_tac
      d="d'"
      and ?w1.0="xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')"
      and ?w3.0="[]"
      in CFGRM_Nonblockingness_to_elimination)
         apply(rename_tac J' d n w e ea na v d')(*strict*)
         apply(force)
        apply(rename_tac J' d n w e ea na v d')(*strict*)
        apply(force)
       apply(rename_tac J' d n w e ea na v d')(*strict*)
       apply(force)
      apply(rename_tac J' d n w e ea na v d')(*strict*)
      apply(force)
     apply(rename_tac J' d n w e ea na v d')(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d')(*strict*)
    apply(force)
   apply(rename_tac J' d n w e ea na v d')(*strict*)
   apply(force)
  apply(rename_tac J' d n w e ea na v d')(*strict*)
  apply(clarsimp)
    (*
  d / 0:tail-J' \<Longrightarrow> n: tail-I @ w
  d' / 0:S \<Longrightarrow> na: xs @ x # tail-J' @ v
  tail-J = x # tail-J'
  thus: d' / 0:S \<Longrightarrow> na: xs @ tail-J @ v
  d'nonterminal /0:v \<Longrightarrow> n': wa
  thus: d'event /0:xs @ tail-J @ v \<Longrightarrow> n': xs @ tail-J @ wa

  d? / 0:S \<Longrightarrow> n?: xs @ x # tail-I @ v?
*)
  apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
  apply(subgoal_tac "\<exists>d. maximum_of_domain d n' \<and> cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')@v\<rparr>) \<and> d n' = Some (pair eb \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')@wa\<rparr>)")
   apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map d'nonterminal (\<lambda>c. \<lparr>cfg_conf=(xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J'))@(cfg_conf c)@[]\<rparr>)"
      in exI)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_derivation2)
     apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
    apply(rule cfgRM_step_relation_both_sides_context)
    apply(force)
   apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_belongs)
        apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
        apply(force)
       apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
       apply(force)
      apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
      apply(force)
     apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb c)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb ca)(*strict*)
    apply(rule_tac
      t="xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ ca"
      and s="xs @ [x] @ cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ ca"
      in ssubst)
     apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb ca)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb ca)(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')@v\<rparr> \<in> cfg_configurations G")
     apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb ca)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp only: setAConcat setBConcat)
     apply(clarsimp)
     apply(simp only: setAConcat setBConcat)
     apply(clarsimp)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb ca)(*strict*)
    apply(rule_tac
      d="d'"
      and i="na"
      in cfgSTD.belongs_configurations)
     apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb ca)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb ca)(*strict*)
    apply(force)
   apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac J' d n w e ea na v d' d'nonterminal n' wa eb)(*strict*)
  apply(thin_tac "maximum_of_domain d'nonterminal n'")
  apply(thin_tac "cfgRM.derivation G d'nonterminal")
  apply(thin_tac "cfgSTD.belongs G d'nonterminal")
  apply(thin_tac "d'nonterminal 0 = Some (pair None \<lparr>cfg_conf = v\<rparr>)")
  apply(thin_tac "d'nonterminal n' = Some (pair eb \<lparr>cfg_conf = wa\<rparr>)")
  apply(clarsimp)
    (*
  d / 0:tail-J' \<Longrightarrow> n: tail-I @ w
  d' / 0:S \<Longrightarrow> na: xs @ x # tail-J' @ v
  tail-J = x # tail-J'
  thus: d' / 0:S \<Longrightarrow> na: xs @ tail-J @ v
  thus: da /0:xs @ tail-J @ v \<Longrightarrow> n': xs @ tail-J @ wa
  thus: d'+da / 0:S \<Longrightarrow> na+n': xs @ tail-J @ wa

  d? / 0:S \<Longrightarrow> n?: xs @ x # tail-I @ v?
*)
  apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
  apply(subgoal_tac "d' 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>)")
   apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
   prefer 2
   apply(rule CFGRM_derivation_initial_pos0)
    apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
    apply(force)
   apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
   apply(force)
  apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
  apply(subgoal_tac "\<exists>d. maximum_of_domain d (na+n') \<and> cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>) \<and> d (na+n') = Some (pair (if n'=0 then ea else eb) \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')@wa\<rparr>)")
   apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
   prefer 2
   apply(case_tac "n'")
    apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
    prefer 2
    apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
    apply(rule_tac
      x="derivation_append d' da na"
      in exI)
    apply(rule conjI)
     apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
     apply(rule_tac concat_has_max_dom)
      apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
      apply(force)
     apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
     apply(rule cfgRM.derivation_concat2)
        apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
        apply(force)
       apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
       apply(force)
      apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
      apply(force)
     apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
    apply(rule conjI)
     apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
     apply(rule cfgRM.derivation_append_preserves_belongs)
       apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
       apply(force)
      apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
      apply(force)
     apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na v d' n' wa eb da nat)(*strict*)
    apply(simp add: derivation_append_def)
   apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
   apply(clarsimp)
   apply(rename_tac J' d n w e ea na d' wa da)(*strict*)
   apply(rule_tac
      x="d'"
      in exI)
   apply(clarsimp)
  apply(rename_tac J' d n w e ea na v d' n' wa eb da)(*strict*)
  apply(thin_tac "cfgRM.derivation G d'")
  apply(thin_tac "cfgLM.belongs G d'")
  apply(thin_tac "cfgRM.derivation_initial G d'")
  apply(thin_tac "d' na = Some (pair ea \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ v\<rparr>)")
  apply(thin_tac "maximum_of_domain d' na")
  apply(thin_tac "maximum_of_domain da n'")
  apply(thin_tac "cfgRM.derivation G da")
  apply(thin_tac "cfgLM.belongs G da")
  apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ v\<rparr>)")
  apply(thin_tac "da n' = Some (pair eb \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ wa\<rparr>)")
  apply(thin_tac "d' 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>)")
  apply(clarsimp)
    (*
  d / 0:tail-J' \<Longrightarrow> n: tail-I @ w
  thus: da / 0:S \<Longrightarrow> na+n': xs @ x # tail-J' @ wa

  d? / 0:S \<Longrightarrow> n?: xs @ x # tail-I @ v?
  v=w@wa
  n=n+na+n'
  d=da+C[d]
*)
  apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
  apply(subgoal_tac "\<exists>d. maximum_of_domain d n \<and> cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J') @ wa\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = xs @ x # cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w @ wa\<rparr>)")
   apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_map d (\<lambda>c. \<lparr>cfg_conf=(xs @ [x])@(cfg_conf c)@wa\<rparr>)"
      in exI)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(force)
   apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_derivation2)
     apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
    apply(rule cfgRM_step_relation_both_sides_context)
    apply(force)
   apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_belongs)
        apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
        apply(force)
       apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
       apply(force)
      apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
      apply(force)
     apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na n' wa eb da c)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac J' d n w e ea na n' wa eb da ca)(*strict*)
    apply(rule_tac
      t="xs @ x # ca @ wa"
      and s="xs @ [x] @ ca @ wa"
      in ssubst)
     apply(rename_tac J' d n w e ea na n' wa eb da ca)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na n' wa eb da ca)(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = xs @ x # cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')@wa\<rparr> \<in> cfg_configurations G")
     apply(rename_tac J' d n w e ea na n' wa eb da ca)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp only: setAConcat setBConcat)
     apply(clarsimp)
     apply(simp only: setAConcat setBConcat)
     apply(clarsimp)
    apply(rename_tac J' d n w e ea na n' wa eb da ca)(*strict*)
    apply(rule_tac
      d="da"
      and i="na+n'"
      in cfgSTD.belongs_configurations)
     apply(rename_tac J' d n w e ea na n' wa eb da ca)(*strict*)
     apply(force)
    apply(rename_tac J' d n w e ea na n' wa eb da ca)(*strict*)
    apply(force)
   apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
   apply(rule conjI)
    apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac J' d n w e ea na n' wa eb da)(*strict*)
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "cfgRM.derivation G d")
  apply(thin_tac "cfgLM.belongs G d")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = cfg_item_rhs2 J' @ liftB (cfg_item_look_ahead J')\<rparr>)")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) @ w\<rparr>)")
  apply(clarsimp)
    (*
  d / 0:xs @ x # tail-J' @ wa \<Longrightarrow> n: xs @ x # tail-I @ w @ wa
  da / 0:S \<Longrightarrow> na+n': xs @ x # tail-J' @ wa

  d? / 0:S \<Longrightarrow> n?: xs @ x # tail-I @ v?
  v=w@wa
  n=n+na+n'
  d=da+d
*)
  apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
  apply(rule_tac
      x="derivation_append da d (na+n')"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
   apply(rule cfgRM.derivation_concat2)
      apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
      apply(force)
     apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
     apply(force)
    apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
    apply(force)
   apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
   apply(clarsimp)
  apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
  apply(rule conjI)
   apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
   apply(rule cfgRM.derivation_append_preserves_belongs)
     apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
     apply(force)
    apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
    apply(force)
   apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
   apply(force)
  apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
  apply(rule conjI)
   apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(simp add: derivation_append_def)
   apply(simp add: cfg_initial_configurations_def)
   apply(simp add: cfg_configurations_def)
   apply(rule cfg_initial_in_nonterms)
   apply(force)
  apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
  apply(rule_tac
      x="if n'=0 then (if n=0 then ea else e) else (if n=0 then eb else e)"
      in exI)
  apply(rule_tac
      x="n+na + n'"
      in exI)
  apply(rule_tac
      x="w@wa"
      in exI)
  apply(simp add: derivation_append_def)
  apply(case_tac n)
   apply(rename_tac J' n w e ea na n' wa eb da d)(*strict*)
   apply(clarsimp)
  apply(rename_tac J' n w e ea na n' wa eb da d nat)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> F_VALID_ITEM_SET_INITIAL G' F k = {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}"
  apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G' F k"
      and s="(if []=[] then F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k) else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (essential_items (valid_item_set G' k [])) )"
      in ssubst)
   apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
   apply(rule sym)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_idemp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
  apply(rule_tac
      t="(if [] = [] then F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k) else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (essential_items (valid_item_set G' k [])))"
      and s="valid_item_set G' k []"
      in ssubst)
   apply(rule sym)
   apply(rule Lemma6__23)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule order_antisym)
   apply(simp add: valid_item_set_def valid_item_set_n_def)
   apply(clarsimp)
   apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
   apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>) \<lparr>cfg_conf=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>)")
    apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
           apply(force)
          apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(force)
     apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
   apply(case_tac n)
    apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
    apply(clarsimp)
    apply(rename_tac y d)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(subgoal_tac "length y = length (liftB y)")
     apply(rename_tac y d)(*strict*)
     prefer 2
     apply(rule liftB_reflects_length)
    apply(rename_tac y d)(*strict*)
    apply(subgoal_tac "length y = length []")
     apply(rename_tac y d)(*strict*)
     prefer 2
     apply(rule_tac
      t="[]"
      and s="liftB y"
      in ssubst)
      apply(rename_tac y d)(*strict*)
      apply(force)
     apply(rename_tac y d)(*strict*)
     apply(blast)
    apply(rename_tac y d)(*strict*)
    apply(force)
   apply(rename_tac n A \<beta> y d e1 e2 z nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
   apply(subgoal_tac "\<exists>e w. d (Suc nat) = Some (pair e \<lparr>cfg_conf = teB (F_FRESH (cfg_events G)) # w\<rparr>)")
    apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc 0"
      in terminal_at_beginning_are_never_modified)
        apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
        apply(rule cfgRM_derivations_are_cfg_derivations)
        apply(force)
       apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
       apply(force)
      apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
      apply(force)
     apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
     apply(force)
    apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
   apply(clarsimp)
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(clarsimp)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr> \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr> \<lparr>cfg_conf = teB (F_FRESH (cfg_events G)) # teA (cfg_initial G) # [teB (F_FRESH (cfg_events G))]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp add: der2_def)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="p" for p
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule conjI)
   apply(simp add: der2_def)
   apply(simp add: F_CFG_AUGMENT_def)
  apply(rule conjI)
   apply(simp add: der2_def)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(rule der2_maximum_of_domain)
  apply(force)
  done

lemma F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL_F_VALID_ITEM_SET_GOTO__descent__fp: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k) = F_VALID_ITEM_SET_INITIAL G' F k"
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k)"
      and s="(if(F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k (F_VALID_ITEM_SET_INITIAL G' F k) = (F_VALID_ITEM_SET_INITIAL G' F k))then (F_VALID_ITEM_SET_INITIAL G' F k) else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k (F_VALID_ITEM_SET_INITIAL G' F k)))"
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G' F k"
      and s="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[],cfg_item_rhs2=[teB Do,teA (cfg_initial G),teB Do],cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
    apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(simp add: valid_item_def)
   apply(simp add: F_CFG_AUGMENT_def)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k (F_VALID_ITEM_SET_INITIAL G' F k) = F_VALID_ITEM_SET_INITIAL G' F k")
   apply(force)
  apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G' F k"
      and s="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[],cfg_item_rhs2=[teB Do,teA (cfg_initial G),teB Do],cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
   apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  done

lemma F_VALID_ITEM_SET_GOTO_uses_every_last_cfg_item_rhs1_symbol: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> w @ [x] = cfg_item_rhs1 I
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> S \<subseteq> Collect (valid_item G' k)
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G' F k X S = q
  \<Longrightarrow> X = x"
  apply(simp add: F_VALID_ITEM_SET_GOTO_def)
  apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__basis X S")
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
   apply(clarsimp)
   apply(rename_tac I1)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(subgoal_tac "\<And>G F k S. cfgSTD_first_compatible F k \<Longrightarrow> valid_cfg G \<Longrightarrow> Ball S (valid_item G k) \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G F k S \<Longrightarrow> I \<in> S \<or> cfg_item_rhs1 I = []")
   apply(erule_tac
      x="(F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))"
      in meta_allE)
   apply(erule_tac
      x="F"
      in meta_allE)
   apply(erule_tac
      x="k"
      in meta_allE)
   apply(erule_tac
      x="F_VALID_ITEM_SET_GOTO__basis X S"
      in meta_allE)
   apply(erule meta_impE)
    apply(force)
   apply(erule meta_impE)
    apply(force)
   apply(erule meta_impE)
    apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__basis X S \<subseteq> Collect(valid_item (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k)")
     prefer 2
     apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac Ga Fa ka Sa)(*strict*)
  apply(subgoal_tac "\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp Ga Fa ka Sa. I \<in> Sa \<or> (cfg_item_rhs1 I=[])")
   apply(rename_tac Ga Fa ka Sa)(*strict*)
   apply(erule_tac
      x="I"
      and P="\<lambda>I. valid_item Ga ka I"
      in ballE)
    apply(rename_tac Ga ka Sa)(*strict*)
    apply(force)
   apply(rename_tac Ga ka Sa)(*strict*)
   apply(force)
  apply(rename_tac Ga ka Sa)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_fresh)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  done

lemma DollarReadItem_OnlyIn_Specific_Valid: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> set v \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')
  \<Longrightarrow> \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = x\<rparr> \<in> valid_item_set G' k v
  \<Longrightarrow> v = [teB Do] \<and> x = []"
  apply(subgoal_tac "\<exists>n. \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = x\<rparr> \<in> valid_item_set_n G' k n v")
   prefer 2
   apply(simp add: valid_item_set_def)
  apply(erule exE)+
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "\<forall>A \<alpha> \<beta> y. \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = x\<rparr> = \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>,cfg_item_rhs2 = \<beta>,cfg_item_look_ahead = y\<rparr> \<longrightarrow> (\<exists>d \<delta> e1 e2 z. cfgRM.derivation G' d \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=\<delta>@[teA A]@z\<rparr>) \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf=\<delta>@\<alpha>@\<beta>@z\<rparr>) \<and> take k z=liftB y \<and> v=\<delta>@\<alpha> \<and> maximum_of_domain d (Suc n) \<and> setA z = {})")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: valid_item_set_n_def)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = x\<rparr> \<in> valid_item_set G' k v")
  apply(rename_tac n)(*strict*)
  apply(thin_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = x\<rparr> \<in> valid_item_set_n G' k n v")
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="S'"
      in allE)
  apply(erule_tac
      x="[teB Do]"
      in allE)
  apply(erule_tac
      x="[teA (cfg_initial G), teB Do]"
      in allE)
  apply(erule_tac
      x="x"
      in allE)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule exE)+
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(subgoal_tac "\<exists>e w. d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>) \<and> (set w) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) ")
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc 0"
      and n="n"
      in cfgRM.property_preseved_under_steps_is_invariant2)
       apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
      apply(rule_tac
      x="Some\<lparr>prod_lhs = cfg_initial G', prod_rhs = [teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in exI)
      apply(rule_tac
      x="[teA (cfg_initial G)]"
      in exI)
      apply(rule conjI)
       apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
       apply(clarsimp)
      apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
      apply(simp add: two_elements_construct_domain_def valid_cfg_def)
     apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(rule allI)
   apply(rename_tac n d \<delta> e1 e2 z i)(*strict*)
   apply(rule impI)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
   apply(erule conjE)+
   apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
    apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
    prefer 2
    apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
      apply(blast)
     apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
     apply(blast)
    apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
    apply(arith)
   apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
   apply(erule exE)+
   apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
   apply(subgoal_tac "cfgRM_step_relation G' \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr> ea c")
    apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
    prefer 2
    apply(rule cfgRM.position_change_due_to_step_relation)
      apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
      apply(blast)
     apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
     apply(blast)
    apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
    apply(blast)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
   apply(case_tac c)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea c cfg_conf)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac n d \<delta> e1 e2 z i e w ea l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
   apply(case_tac "r=[]")
    apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
   apply(subgoal_tac "\<exists>r' a. r=r'@[a]")
    apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
    apply(subgoal_tac "ea \<in> cfg_productions G")
     apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="ea"
      and P="\<lambda>ea. prod_lhs ea \<in> cfg_nonterminals G \<and> setA (prod_rhs ea) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs ea) \<subseteq> cfg_events G"
      in ballE)
      apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      A="set(prod_rhs ea)"
      in set_mp)
       apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
       apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
        apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
        apply(force)
       apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
       apply(force)
      apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
     apply(force)
    apply(rename_tac n d \<delta> e1 e2 z i e ea list r' xa)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac n d \<delta> e1 e2 z i e list r' xa)(*strict*)
    apply(subgoal_tac "teA (F_FRESH (cfg_nonterminals G)) \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
     apply(rename_tac n d \<delta> e1 e2 z i e list r' xa)(*strict*)
     apply(force)
    apply(rename_tac n d \<delta> e1 e2 z i e list r' xa)(*strict*)
    apply(thin_tac "teA (F_FRESH (cfg_nonterminals G)) \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
    apply(simp add: two_elements_construct_domain_def)
    apply(rule conjI)
     apply(rename_tac n d \<delta> e1 e2 z i e list r' xa)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac n d \<delta> e1 e2 z i e list r' xa)(*strict*)
    apply(rule teA_notInMap)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
   apply(rule_tac
      n="length r - 1"
      in NonEmptyListHasTailElem)
   apply(case_tac r)
    apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea r list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(subgoal_tac "\<delta>=[] \<and> z=[]")
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   prefer 2
   apply(rule match_with_border)
    apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in Set.contra_subsetD)
    apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(simp add: two_elements_construct_domain_def)
   apply(rule conjI)
    apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(rule teB_notInMap)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(rule conjI)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(force)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(subgoal_tac "length x=0")
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(blast)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(rule_tac
      t="length x"
      and s="length (liftB x)"
      in ssubst)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(simp add: liftB_reflects_length)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(rule_tac
      t="liftB x"
      and s="take k z"
      in ssubst)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(force)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(rule_tac
      t="z"
      and s="[]"
      in ssubst)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(force)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(force)
  done

lemma DollarInitialReadItem_OnlyIn_Specific_Valid: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> set v \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')
  \<Longrightarrow> \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k v
  \<Longrightarrow> v = [teB Do, teA (cfg_initial G)]"
  apply(subgoal_tac "\<exists>n. \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do,teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set_n G' k n v")
   prefer 2
   apply(simp add: valid_item_set_def)
  apply(erule exE)+
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac "\<forall>A \<alpha> \<beta> y. \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do,teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> = \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>,cfg_item_rhs2 = \<beta>,cfg_item_look_ahead = y\<rparr> \<longrightarrow> (\<exists>d \<delta> e1 e2 z. cfgRM.derivation G' d \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=\<delta>@[teA A]@z\<rparr>) \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf=\<delta>@\<alpha>@\<beta>@z\<rparr>) \<and> take k z=liftB y \<and> v=\<delta>@\<alpha> \<and> maximum_of_domain d (Suc n) \<and> setA z = {})")
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(simp add: valid_item_set_n_def)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k v")
  apply(rename_tac n)(*strict*)
  apply(thin_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set_n G' k n v")
  apply(rename_tac n)(*strict*)
  apply(erule_tac
      x="S'"
      in allE)
  apply(erule_tac
      x="[teB Do,teA (cfg_initial G)]"
      in allE)
  apply(erule_tac
      x="[teB Do]"
      in allE)
  apply(erule_tac
      x="[]"
      in allE)
  apply(erule impE)
   apply(rename_tac n)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(erule exE)+
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(subgoal_tac "\<exists>e w. d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>) \<and> (set w) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) ")
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc 0"
      and n="n"
      in cfgRM.property_preseved_under_steps_is_invariant2)
       apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
      apply(rule_tac
      x="Some\<lparr>prod_lhs = cfg_initial G', prod_rhs = [teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in exI)
      apply(rule_tac
      x="[teA (cfg_initial G)]"
      in exI)
      apply(rule conjI)
       apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
       apply(clarsimp)
      apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
      apply(simp add: two_elements_construct_domain_def valid_cfg_def)
     apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
   apply(rule allI)
   apply(rename_tac n d \<delta> e1 e2 z i)(*strict*)
   apply(rule impI)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
   apply(erule conjE)+
   apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
    apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
    prefer 2
    apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
      apply(blast)
     apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
     apply(blast)
    apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
    apply(arith)
   apply(rename_tac n d \<delta> e1 e2 z i e w)(*strict*)
   apply(erule exE)+
   apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
   apply(subgoal_tac "cfgRM_step_relation G' \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr> ea c")
    apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
    prefer 2
    apply(rule cfgRM.position_change_due_to_step_relation)
      apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
      apply(blast)
     apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
     apply(blast)
    apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
    apply(blast)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea c)(*strict*)
   apply(case_tac c)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea c cfg_conf)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac n d \<delta> e1 e2 z i e w ea l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
   apply(case_tac "r=[]")
    apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
   apply(subgoal_tac "\<exists>r' a. r=r'@[a]")
    apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
    apply(subgoal_tac "ea \<in> cfg_productions G")
     apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="ea"
      and P="\<lambda>ea. prod_lhs ea \<in> cfg_nonterminals G \<and> setA (prod_rhs ea) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs ea) \<subseteq> cfg_events G"
      in ballE)
      apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      A="set(prod_rhs ea)"
      in set_mp)
       apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
       apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
        apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
        apply(force)
       apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
       apply(force)
      apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
      apply(clarsimp)
     apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
     apply(force)
    apply(rename_tac n d \<delta> e1 e2 z i e ea list r' x)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac n d \<delta> e1 e2 z i e list r' x)(*strict*)
    apply(subgoal_tac "teA (F_FRESH (cfg_nonterminals G)) \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
     apply(rename_tac n d \<delta> e1 e2 z i e list r' x)(*strict*)
     apply(force)
    apply(rename_tac n d \<delta> e1 e2 z i e list r' x)(*strict*)
    apply(thin_tac "teA (F_FRESH (cfg_nonterminals G)) \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
    apply(simp add: two_elements_construct_domain_def)
    apply(rule conjI)
     apply(rename_tac n d \<delta> e1 e2 z i e list r' x)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac n d \<delta> e1 e2 z i e list r' x)(*strict*)
    apply(rule teA_notInMap)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
   apply(rule_tac
      n="length r - 1"
      in NonEmptyListHasTailElem)
   apply(case_tac r)
    apply(rename_tac n d \<delta> e1 e2 z i e w ea r list)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z i e w ea r list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d \<delta> e1 e2 z)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(subgoal_tac "\<delta>=[] \<and> z=[]")
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   prefer 2
   apply(rule match_with_border)
    apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in Set.contra_subsetD)
    apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
    apply(force)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(simp add: two_elements_construct_domain_def)
   apply(rule conjI)
    apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
   apply(rule teB_notInMap)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac n d \<delta> e1 e2 z w)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO_does_not_reach_F_LR_MACHINE_initial: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> \<forall>I \<in> q. valid_item G' k I
  \<Longrightarrow> F_VALID_ITEM_SET_INITIAL G' F k \<noteq> F_VALID_ITEM_SET_GOTO G' F k X q"
  apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G' F k"
      and s="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[],cfg_item_rhs2=[teB Do,teA (cfg_initial G),teB Do],cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
   apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<notin> F_VALID_ITEM_SET_GOTO G' F k X q")
   apply(force)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G' F k X q"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis X q)"
      in ssubst)
   apply(simp add: F_VALID_ITEM_SET_GOTO_def)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<notin> F_VALID_ITEM_SET_GOTO__basis X q")
   prefer 2
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(case_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis X q)")
   prefer 2
   apply(force)
  apply(subgoal_tac "\<exists>p \<in> cfg_productions G'. teA (cfg_item_lhs \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>) \<in> set(prod_rhs p)")
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_insertion_implies_existence_of_production)
       apply(force)
      apply(force)
     apply(force)
    apply(rule ballI)
    apply(rename_tac I)(*strict*)
    apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__basis X q \<subseteq> Collect (valid_item G' k)")
     apply(rename_tac I)(*strict*)
     prefer 2
     apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
     apply(clarsimp)
    apply(rename_tac I)(*strict*)
    apply(force)
   apply(force)
  apply(subgoal_tac "False")
   apply(force)
  apply(erule bexE)
  apply(rename_tac p)(*strict*)
  apply(subgoal_tac "teA S' \<in> set(prod_rhs p)")
   apply(rename_tac p)(*strict*)
   apply(case_tac "p \<in> cfg_productions G")
    apply(rename_tac p)(*strict*)
    apply(subgoal_tac "S' \<in> setA (prod_rhs p) \<and> S' \<notin> cfg_nonterminals G")
     apply(rename_tac p)(*strict*)
     prefer 2
     apply(rule conjI)
      apply(rename_tac p)(*strict*)
      apply(rule set_setA)
      apply(force)
     apply(rename_tac p)(*strict*)
     apply(rule_tac
      t="S'"
      and s="F_FRESH (cfg_nonterminals G)"
      in ssubst)
      apply(rename_tac p)(*strict*)
      apply(force)
     apply(rename_tac p)(*strict*)
     apply(rule F_FRESH_is_fresh)
     apply(simp add: valid_cfg_def)
    apply(rename_tac p)(*strict*)
    apply(simp add: valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      x="p"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      in ballE)
     apply(rename_tac p)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<not> setA (prod_rhs p) \<subseteq> cfg_nonterminals G")
      apply(rename_tac p)(*strict*)
      apply(force)
     apply(rename_tac p)(*strict*)
     apply(force)
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(subgoal_tac "p=\<lparr>prod_lhs=S',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>")
    apply(rename_tac p)(*strict*)
    prefer 2
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rename_tac p)(*strict*)
   apply(subgoal_tac "teA S' \<in> set [teB Do, teA (cfg_initial G), teB Do] ")
    apply(rename_tac p)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(subgoal_tac "teA S' \<notin> set [teB Do, teA (cfg_initial G), teB Do]")
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(rule set_take_head)
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(rule set_take_head)
    apply(rename_tac p)(*strict*)
    defer
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(force)
  apply(rename_tac p)(*strict*)
  apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
   apply(rename_tac p)(*strict*)
   apply(subgoal_tac "S' \<notin> cfg_nonterminals G")
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(rule_tac
      t="S'"
      and s="F_FRESH (cfg_nonterminals G)"
      in ssubst)
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac p)(*strict*)
  apply(simp add: valid_cfg_def)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_new_is_kPrefix: "
  F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G' F k S
  \<Longrightarrow> valid_cfg G \<and> cfgSTD_first_compatible F k \<and> Do = F_FRESH (cfg_events G) \<and> S' = F_FRESH (cfg_nonterminals G) \<and> G' = F_CFG_AUGMENT G S' Do \<and> valid_cfg G' \<and> (\<forall>I \<in> S. valid_item G' k I) \<and> (\<forall>I \<in> S. cfg_item_lhs I \<noteq> S' \<longrightarrow> item_core I \<in> cfg_productions G) \<and> (\<forall>I \<in> S. cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (\<forall>I \<in> S. cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G}) \<longrightarrow> (\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k S. (cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G}))"
  apply(rule_tac
      ?a0.0="G'"
      and ?a1.0="F"
      and ?a2.0="k"
      and ?a3.0="S"
      in F_VALID_ITEM_SET_GOTO__descent__fp.pinduct)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(force)
  apply(rename_tac Ga Fa ka Sa)(*strict*)
  apply(thin_tac "F_VALID_ITEM_SET_GOTO__descent__fp_valid_input G' F k S")
  apply(rename_tac Ga Fa k S)(*strict*)
  apply(rename_tac G' F k S)
  apply(rename_tac G' F k S)(*strict*)
  apply(case_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k S \<noteq> S")
   apply(rename_tac G' F k S)(*strict*)
   apply(rule impI)
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G' F k S"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k S)"
      in ssubst)
    apply(rename_tac G' F k S)(*strict*)
    prefer 2
    apply(erule meta_impE)
     apply(rename_tac G' F k S)(*strict*)
     apply(force)
    apply(rename_tac G' F k S)(*strict*)
    apply(erule impE)
     apply(rename_tac G' F k S)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G' F k S)(*strict*)
    prefer 2
    apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G' F k S"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k S = S then S else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k S))"
      in ssubst)
     apply(rename_tac G' k S)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(blast)
    apply(rename_tac G' F k S)(*strict*)
    apply(thin_tac "valid_cfg G \<and> cfgSTD_first_compatible F k \<and> Do = F_FRESH (cfg_events G) \<and> S' = F_FRESH (cfg_nonterminals G) \<and> G' = F_CFG_AUGMENT G S' Do \<and> valid_cfg G' \<and> (\<forall>I \<in> S. valid_item G' k I) \<and> (\<forall>I \<in> S. cfg_item_lhs I \<noteq> S' \<longrightarrow> item_core I \<in> cfg_productions G) \<and> (\<forall>I \<in> S. cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (\<forall>I \<in> S. cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G})")
    apply(rename_tac G' k S)(*strict*)
    apply(force)
   apply(rename_tac G' k S)(*strict*)
   prefer 2
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G' F k S"
      and s="S"
      in ssubst)
    apply(rename_tac G' F k S)(*strict*)
    apply(rule_tac
      t = "F_VALID_ITEM_SET_GOTO__descent__fp G' F k S"
      and s = "(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k S = S then S else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k S))"
      in ssubst)
     apply(rename_tac G' k S)(*strict*)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
     apply(blast)
    apply(rename_tac G' k S)(*strict*)
    apply(force)
   apply(rename_tac G' k S)(*strict*)
   apply(clarsimp)
  apply(rename_tac G' F k S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G' k S)(*strict*)
   apply(force)
  apply(rename_tac G' F k S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G' k S)(*strict*)
   apply(force)
  apply(rename_tac G' F k S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G' k S)(*strict*)
   apply(force)
  apply(rename_tac G' F k S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G' k S)(*strict*)
   apply(force)
  apply(rename_tac G' F k S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G' k S)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rename_tac G' k S)(*strict*)
   apply(force)
  apply(rename_tac G' F k S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G' F k S)(*strict*)
   apply(erule conjE)+
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G' F k S \<subseteq> Collect (valid_item G' k)")
    apply(rename_tac G' F k S)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_adds_valid_item)
      apply(rename_tac G' F k S)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac G' F k S)(*strict*)
    apply(force)
   apply(rename_tac G' F k S)(*strict*)
   apply(force)
  apply(rename_tac G' F k S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G' k S)(*strict*)
   apply(clarsimp)
   apply(rename_tac k S I)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def item_core_def)
   apply(clarsimp)
   apply(rename_tac k S I x)(*strict*)
   apply(erule disjE)
    apply(rename_tac k S I x)(*strict*)
    apply(clarsimp)
   apply(rename_tac k S I x)(*strict*)
   apply(clarsimp)
   apply(rename_tac k S x B w z \<beta>)(*strict*)
   apply(simp add: F_CFG_AUGMENT_def)
  apply(rename_tac G' F k S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G' k S)(*strict*)
   apply(clarsimp)
   apply(rename_tac k S I)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def item_core_def)
   apply(clarsimp)
   apply(rename_tac k S I x)(*strict*)
   apply(erule disjE)
    apply(rename_tac k S I x)(*strict*)
    apply(clarsimp)
   apply(rename_tac k S I x)(*strict*)
   apply(clarsimp)
   apply(rename_tac k S x w z \<beta>)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac k S x w z \<beta>)(*strict*)
    apply(force)
   apply(rename_tac k S x w z \<beta>)(*strict*)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_item (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k x"
      in ballE)
    apply(rename_tac k S x w z \<beta>)(*strict*)
    apply(simp add: valid_item_def)
    apply(clarsimp)
    apply(rename_tac k S x w z \<beta> p)(*strict*)
    apply(subgoal_tac "p \<in> cfg_productions G\<union>{\<lparr>prod_lhs=F_FRESH (cfg_nonterminals G),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>}")
     apply(rename_tac k S x w z \<beta> p)(*strict*)
     prefer 2
     apply(simp only: F_CFG_AUGMENT_def)
     apply(force)
    apply(rename_tac k S x w z \<beta> p)(*strict*)
    apply(thin_tac "p \<in> cfg_productions (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))")
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac k S x w z \<beta> p)(*strict*)
     apply(clarsimp)
     apply(rename_tac k S x w z \<beta>)(*strict*)
     apply(case_tac x)
     apply(rename_tac k S x w z \<beta> cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
     apply(clarsimp)
     apply(rename_tac k S w z \<beta> cfg_item_rhs1a cfg_item_look_aheada)(*strict*)
     apply(case_tac cfg_item_rhs1a)
      apply(rename_tac k S w z \<beta> cfg_item_rhs1a cfg_item_look_aheada)(*strict*)
      apply(clarsimp)
     apply(rename_tac k S w z \<beta> cfg_item_rhs1a cfg_item_look_aheada a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac k S w z \<beta> cfg_item_look_aheada list)(*strict*)
     apply(case_tac list)
      apply(rename_tac k S w z \<beta> cfg_item_look_aheada list)(*strict*)
      apply(clarsimp)
      apply(rename_tac k S w z cfg_item_look_aheada)(*strict*)
      apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> cfg_nonterminals G")
       apply(rename_tac k S w z cfg_item_look_aheada)(*strict*)
       apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
        apply(rename_tac k S w z cfg_item_look_aheada)(*strict*)
        apply(force)
       apply(rename_tac k S w z cfg_item_look_aheada)(*strict*)
       apply(rule F_FRESH_is_fresh)
       apply(simp add: valid_cfg_def)
      apply(rename_tac k S w z cfg_item_look_aheada)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac k S w z \<beta> cfg_item_look_aheada list a lista)(*strict*)
     apply(clarsimp)
     apply(rename_tac k S w z \<beta> cfg_item_look_aheada lista)(*strict*)
     apply(case_tac lista)
      apply(rename_tac k S w z \<beta> cfg_item_look_aheada lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac k S w z \<beta> cfg_item_look_aheada lista a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac k S x w z \<beta> p)(*strict*)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> cfg_nonterminals G")
     apply(rename_tac k S x w z \<beta> p)(*strict*)
     apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
      apply(rename_tac k S x w z \<beta> p)(*strict*)
      apply(force)
     apply(rename_tac k S x w z \<beta> p)(*strict*)
     apply(rule F_FRESH_is_fresh)
     apply(simp add: valid_cfg_def)
    apply(rename_tac k S x w z \<beta> p)(*strict*)
    apply(case_tac p)
    apply(rename_tac k S x w z \<beta> p prod_lhsa prod_rhsa)(*strict*)
    apply(rule_tac
      A="setA (cfg_item_rhs1 x @ teA (F_FRESH (cfg_nonterminals G)) # \<beta>)"
      in set_mp)
     apply(rename_tac k S x w z \<beta> p prod_lhsa prod_rhsa)(*strict*)
     apply(rule prod_rhs_in_nonterms)
      apply(rename_tac k S x w z \<beta> p prod_lhsa prod_rhsa)(*strict*)
      apply(force)
     apply(rename_tac k S x w z \<beta> p prod_lhsa prod_rhsa)(*strict*)
     apply(force)
    apply(rename_tac k S x w z \<beta> p prod_lhsa prod_rhsa)(*strict*)
    apply(rule elemInsetA)
   apply(rename_tac k S x w z \<beta>)(*strict*)
   apply(force)
  apply(rename_tac G' F k S)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  apply(clarsimp)
  apply(rename_tac F k S I x)(*strict*)
  apply(erule disjE)
   apply(rename_tac F k S I x)(*strict*)
   apply(clarsimp)
  apply(rename_tac F k S I x)(*strict*)
  apply(clarsimp)
  apply(rename_tac F k S x B w z \<beta>)(*strict*)
  apply(erule_tac
      x="x"
      and P="\<lambda>x. valid_item (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k x"
      in ballE)
   apply(rename_tac k S x B w z \<beta>)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac F k S x B w z \<beta>)(*strict*)
  apply(erule_tac
      x="x"
      and P="\<lambda>x. cfg_item_lhs x \<noteq> F_FRESH (cfg_nonterminals G) \<longrightarrow> item_core x \<in> cfg_productions G"
      in ballE)
   apply(rename_tac k S x B w z \<beta>)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac F k S x B w z \<beta>)(*strict*)
  apply(erule_tac
      x="x"
      and P="\<lambda>x. cfg_item_lhs x = F_FRESH (cfg_nonterminals G) \<longrightarrow> cfg_item_look_ahead x = []"
      in ballE)
   apply(rename_tac k S x B w z \<beta>)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac F k S x B w z \<beta>)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac k S x B w z \<beta>)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac F k S x B w z \<beta>)(*strict*)
  apply(case_tac x)
  apply(rename_tac F k S x B w z \<beta> cfg_item_lhsa cfg_item_rhs1 cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
  apply(rename_tac A w1 w2 la)
  apply(rename_tac F k S x B w z \<beta> A w1 w2 la)(*strict*)
  apply(clarsimp)
  apply(rename_tac F k S B w z \<beta> A w1 la)(*strict*)
  apply(rule inMap)
  apply(clarsimp)
  apply(case_tac "A=F_FRESH (cfg_nonterminals G)")
   apply(rename_tac F k S B w z \<beta> A w1 la)(*strict*)
   apply(clarsimp)
   apply(rename_tac F k S B w z \<beta> w1)(*strict*)
   apply(simp add: valid_item_def)
   apply(clarsimp)
   apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
   apply(subgoal_tac "p \<in> cfg_productions G\<union>{\<lparr>prod_lhs=F_FRESH (cfg_nonterminals G),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>}")
    apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
    prefer 2
    apply(simp only: F_CFG_AUGMENT_def)
    apply(force)
   apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
   apply(thin_tac "p \<in> cfg_productions (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))")
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
    apply(clarsimp)
    apply(rename_tac F k S B w z \<beta> w1)(*strict*)
    apply(case_tac w1)
     apply(rename_tac F k S B w z \<beta> w1)(*strict*)
     apply(clarsimp)
    apply(rename_tac F k S B w z \<beta> w1 a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac F k S B w z \<beta> list)(*strict*)
    apply(case_tac list)
     apply(rename_tac F k S B w z \<beta> list)(*strict*)
     apply(clarsimp)
     apply(rename_tac F k S w z)(*strict*)
     apply(subgoal_tac "z = take k [F_FRESH (cfg_events G)]")
      apply(rename_tac F k S w z)(*strict*)
      apply(clarsimp)
      apply(rename_tac F k S w)(*strict*)
      apply(simp add: kPrefix_def)
      apply(rule_tac
      x="[F_FRESH (cfg_events G)]"
      in exI)
      apply(clarsimp)
     apply(rename_tac F k S w z)(*strict*)
     apply(subgoal_tac "F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k [teB (F_FRESH (cfg_events G))] = {kPrefix k (filterB [teB (F_FRESH (cfg_events G))])}")
      apply(rename_tac F k S w z)(*strict*)
      prefer 2
      apply(subgoal_tac "cfgSTD_first (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k [teB (F_FRESH (cfg_events G))] = F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k [teB (F_FRESH (cfg_events G))]")
       prefer 2
       apply(simp add: cfgSTD_first_compatible_def)
       apply(erule_tac x="(F_CFG_AUGMENT G
          (F_FRESH (cfg_nonterminals G))
          (F_FRESH (cfg_events G)))" in allE)
       apply(clarsimp)
       apply(erule_tac x="[teB (F_FRESH (cfg_events G))]" in allE)
       apply(erule_tac x="k" in allE)
       apply(clarsimp)
       apply(rule sym)
       apply(erule impE)
        apply(simp add: F_CFG_AUGMENT_def)
       apply(force)
      apply(subgoal_tac "cfgSTD_first (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k [teB (F_FRESH (cfg_events G))] = {kPrefix k (filterB [teB (F_FRESH (cfg_events G))])}")
       prefer 2
       apply(rule cfgSTD_first_on_terminal_string_is_kPrefix)
       apply(clarsimp)
      apply(force)
     apply(rename_tac F k S w z)(*strict*)
     apply(clarsimp)
     apply(rename_tac F k S w)(*strict*)
     apply(simp add: kPrefix_def)
    apply(rename_tac F k S B w z \<beta> list a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac F k S B w z \<beta> lista)(*strict*)
    apply(case_tac lista)
     apply(rename_tac F k S B w z \<beta> lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac F k S B w z \<beta> lista a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> cfg_nonterminals G")
    apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
     apply(force)
    apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac F k S B w z \<beta> w1 p)(*strict*)
   apply(case_tac p)
   apply(rename_tac F k S B w z \<beta> w1 p prod_lhsa prod_rhsa)(*strict*)
   apply(rule prod_lhs_in_nonterms)
    apply(rename_tac F k S B w z \<beta> w1 p prod_lhsa prod_rhsa)(*strict*)
    apply(force)
   apply(rename_tac F k S B w z \<beta> w1 p prod_lhsa prod_rhsa)(*strict*)
   apply(force)
  apply(rename_tac k S B w z \<beta> A w1 la)(*strict*)
  apply(clarsimp)
  apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
  apply(subgoal_tac "set (teA B # \<beta>) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
   apply(rename_tac w')
   apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
   apply(subgoal_tac "\<exists>x. (kPrefix k (w'@[F_FRESH (cfg_events G)]) @ x = w'@[F_FRESH (cfg_events G)])")
    apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
    prefer 2
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(case_tac "length w' \<le> k")
     apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
     apply(rule_tac
      t="take k w'"
      and s="w'"
      in ssubst)
      apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
      apply(clarsimp)
     apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
     apply(case_tac "length w' < k")
      apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
      apply(clarsimp)
     apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
     apply(rule_tac
      t="take (k - length w') [F_FRESH (cfg_events G)]"
      and s="[]"
      in ssubst)
      apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
      apply(clarsimp)
     apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
     apply(rule_tac
      x="[F_FRESH (cfg_events G)]"
      in exI)
     apply(clarsimp)
    apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
    apply(rule_tac
      t="take (k - length w') [F_FRESH (cfg_events G)]"
      and s="[]"
      in ssubst)
     apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
     apply(clarsimp)
    apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
    apply(rule_tac
      x="drop k w' @ [F_FRESH (cfg_events G)]"
      in exI)
    apply(clarsimp)
   apply(rename_tac k S B w z \<beta> A w1 w')(*strict*)
   apply(erule exE)+
   apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "setA \<beta> \<subseteq> cfg_nonterminals G")
    apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
    prefer 2
    apply(rule two_elements_construct_domain_setA)
    apply(force)
   apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
   apply(subgoal_tac "setB \<beta> \<subseteq> cfg_events G")
    apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
    prefer 2
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
   apply(subgoal_tac "z \<in> (kPrefix k) ` (append_language (cfgSTD_first G k \<beta>) {(kPrefix k (w' @ [F_FRESH (cfg_events G)]))})")
    apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
    prefer 2
    apply(rule_tac
      t="(kPrefix k) ` (append_language (cfgSTD_first G k \<beta>) {(kPrefix k (w' @ [F_FRESH (cfg_events G)]))})"
      and s="F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k (\<beta> @ liftB (kPrefix k (w' @ [F_FRESH (cfg_events G)])))"
      in ssubst)
     apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
    apply(rule_tac
      t="F (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k (\<beta> @ liftB (kPrefix k (w' @ [F_FRESH (cfg_events G)])))"
      and s="cfgSTD_first (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k (\<beta> @ liftB (kPrefix k (w' @ [F_FRESH (cfg_events G)])))"
      in ssubst)
     apply(simp add: cfgSTD_first_compatible_def)
     apply(erule_tac x="(F_CFG_AUGMENT G
          (F_FRESH (cfg_nonterminals G))
          (F_FRESH (cfg_events G)))" in allE)
     apply(clarsimp)
     apply(erule_tac x="(\<beta> @ liftB (kPrefix k (w' @ [F_FRESH (cfg_events G)])))" in allE)
     apply(erule_tac x="k" in allE)
     apply(erule impE)
      apply(force)
     apply(erule impE)
      apply(simp add: simpY F_CFG_AUGMENT_def)
      apply(force)
     apply(erule impE)
      apply(simp add: simpY F_CFG_AUGMENT_def)
      apply(rule conjI)
       apply(force)
      apply(simp add: kPrefix_def)
      apply(case_tac "k - length w'")
       apply(clarsimp)
       apply(case_tac w')
        apply(force)
       apply(case_tac k)
        apply(force)
       apply(clarsimp)
       apply(rule_tac xs="x" in rev_cases)
        apply(clarsimp)
        apply(blast)
       apply(clarsimp)
       apply(erule disjE)
        apply(blast)
       apply(subgoal_tac "xa \<in> set ( list)")
        apply(blast)
       apply(rule_tac A="set(take nat list)" in set_mp)
        apply(rule set_take_subset)
       apply(blast)
      apply(clarsimp)
      apply(blast)
     apply(blast)
    apply(rule_tac
      t="cfgSTD_first G k \<beta>"
      and s="cfgSTD_first (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k \<beta>"
      in ssubst)
     apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
     apply(rule cfgSTD_first_F_CFG_AUGMENT__no_change_on_old_input)
           apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
           apply(force)
          apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
          apply(force)
         apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
         apply(force)
        apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
        apply(force)
       apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
       apply(force)
      apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
      apply(force)
     apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
     apply(force)
    apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
    apply(rule cfgSTD_first_pull_out_terimal_tail_string)
    apply(force)
   apply(rename_tac k S B w z \<beta> A w1 w' x)(*strict*)
   apply(simp add: append_language_def)
   apply(clarsimp)
   apply(rename_tac k S B w \<beta> A w1 w' x a)(*strict*)
   apply(rule_tac
      x="a@w'@[F_FRESH (cfg_events G)]"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac k S B w \<beta> A w1 w' x a)(*strict*)
    apply(rule cfgSTD_firstk_in_cfg_events)
       apply(rename_tac k S B w \<beta> A w1 w' x a)(*strict*)
       apply(force)
      apply(rename_tac k S B w \<beta> A w1 w' x a)(*strict*)
      apply(force)
     apply(rename_tac k S B w \<beta> A w1 w' x a)(*strict*)
     apply(force)
    apply(rename_tac k S B w \<beta> A w1 w' x a)(*strict*)
    apply(force)
   apply(rename_tac k S B w \<beta> A w1 w' x a)(*strict*)
   apply(rule kPrefix_append)
  apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w1 @ teA B # \<beta>\<rparr>"
      and P="\<lambda>x. prod_lhs x \<in> cfg_nonterminals G \<and> setA (prod_rhs x) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs x) \<subseteq> cfg_events G"
      in ballE)
   apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
   apply(clarsimp)
   apply(simp only: setAConcat concat_asso setBConcat)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
    apply(simp add: two_elements_construct_domain_def)
   apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
   apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
    apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
    apply(force)
   apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
   apply(force)
  apply(rename_tac k S B w z \<beta> A w1 wa)(*strict*)
  apply(simp add: item_core_def)
  done

lemma F_CFG_AUGMENT__Initial_only_in_F_VALID_ITEM_SET_INITIAL: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k v
  \<Longrightarrow> v = []"
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n d e1 e2 z)(*strict*)
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>) \<lparr>cfg_conf=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>)")
   apply(rename_tac n d e1 e2 z)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac n d e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac n d e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac n d e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac n d e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n d e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac n d e1 e2 z)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac n d e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n d e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n d e1 e2 z)(*strict*)
  apply(case_tac n)
   apply(rename_tac n d e1 e2 z)(*strict*)
   apply(clarsimp)
   apply(rename_tac d z)(*strict*)
   apply(case_tac v)
    apply(rename_tac d z)(*strict*)
    apply(clarsimp)
   apply(rename_tac d z a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d e1 e2 z nat)(*strict*)
  apply(subgoal_tac " \<forall>e2 w'. d n=Some (pair e2 \<lparr>cfg_conf=w'\<rparr>) \<longrightarrow> ((F_FRESH (cfg_nonterminals G)) \<notin> setA w') ")
   apply(rename_tac n d e1 e2 z nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e1 e2 z nat)(*strict*)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> setA (v @ teA (F_FRESH (cfg_nonterminals G)) # z)")
    apply(rename_tac d e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac d e1 e2 z nat)(*strict*)
   apply(rule_tac
      t="teA (F_FRESH (cfg_nonterminals G)) # z"
      and s="[teA (F_FRESH (cfg_nonterminals G))] @ z"
      in ssubst)
    apply(rename_tac d e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac d e1 e2 z nat)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
  apply(rename_tac n d e1 e2 z nat)(*strict*)
  apply(rule_tac
      m="Suc 0"
      and n="Suc n"
      in cfgRM.property_preseved_under_steps_is_invariant2)
      apply(rename_tac n d e1 e2 z nat)(*strict*)
      apply(force)
     apply(rename_tac n d e1 e2 z nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac d e1 e2 z nat)(*strict*)
     apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
      apply(rename_tac d e1 e2 z nat)(*strict*)
      apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
       apply(rename_tac d e1 e2 z nat)(*strict*)
       apply(force)
      apply(rename_tac d e1 e2 z nat)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac d e1 e2 z nat)(*strict*)
     apply(rule F_FRESH_is_fresh)
     apply(simp add: valid_cfg_def)
    apply(rename_tac n d e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac n d e1 e2 z nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d e1 e2 z nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 e2 z nat i e2a w')(*strict*)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac d e1 e2 z nat i e2a w')(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in cfgRM.pre_some_position_is_some_position)
     apply(rename_tac d e1 e2 z nat i e2a w')(*strict*)
     apply(blast)
    apply(rename_tac d e1 e2 z nat i e2a w')(*strict*)
    apply(blast)
   apply(rename_tac d e1 e2 z nat i e2a w')(*strict*)
   apply(force)
  apply(rename_tac d e1 e2 z nat i e2a w')(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 e2 z nat i e2a w' e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d e1 e2 z nat i e2a w' e c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
     apply(blast)
    apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
    apply(blast)
   apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
   apply(subgoal_tac "\<forall>m>(Suc (Suc nat)). d m = None")
    apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
    apply(erule_tac
      x="Suc i"
      in allE)
    apply(clarsimp)
   apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
   apply(rule cfgRM.noSomeAfterMaxDom)
    apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac d e1 e2 z nat i e2a w' e cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 e2 z nat i w' e cfg_conf ea)(*strict*)
  apply(subgoal_tac "cfgRM_step_relation (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) \<lparr>cfg_conf = cfg_conf\<rparr> ea \<lparr>cfg_conf=w'\<rparr>")
   apply(rename_tac d e1 e2 z nat i w' e cfg_conf ea)(*strict*)
   prefer 2
   apply(rule cfgRM.position_change_due_to_step_relation)
     apply(rename_tac d e1 e2 z nat i w' e cfg_conf ea)(*strict*)
     apply(blast)
    apply(rename_tac d e1 e2 z nat i w' e cfg_conf ea)(*strict*)
    apply(blast)
   apply(rename_tac d e1 e2 z nat i w' e cfg_conf ea)(*strict*)
   apply(blast)
  apply(rename_tac d e1 e2 z nat i w' e cfg_conf ea)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
  apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<in> setA (prod_rhs ea)")
   apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(erule_tac
      P="k=0"
      in disjE)
    apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
    apply(clarsimp)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="ea"
      and P="\<lambda>ea. prod_lhs ea \<in> cfg_nonterminals G \<and> setA (prod_rhs ea) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs ea) \<subseteq> cfg_events G"
      in ballE)
     apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
      apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
      apply(force)
     apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
     apply(rule F_FRESH_is_fresh)
     apply(simp add: valid_cfg_def)
    apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e1 e2 z nat i e l r)(*strict*)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac d e1 e2 z nat i e l r)(*strict*)
     apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
      apply(rename_tac d e1 e2 z nat i e l r)(*strict*)
      apply(force)
     apply(rename_tac d e1 e2 z nat i e l r)(*strict*)
     apply(simp add: valid_cfg_def)
    apply(rename_tac d e1 e2 z nat i e l r)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e1 e2 nat i e ea l r)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="ea"
      and P="\<lambda>ea. prod_lhs ea \<in> cfg_nonterminals G \<and> setA (prod_rhs ea) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs ea) \<subseteq> cfg_events G"
      in ballE)
    apply(rename_tac d e1 e2 nat i e ea l r)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac d e1 e2 nat i e ea l r)(*strict*)
     apply(force)
    apply(rename_tac d e1 e2 nat i e ea l r)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d e1 e2 nat i e ea l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e1 e2 nat i e l r)(*strict*)
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    apply(rename_tac d e1 e2 nat i e l r)(*strict*)
    apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
     apply(rename_tac d e1 e2 nat i e l r)(*strict*)
     apply(force)
    apply(rename_tac d e1 e2 nat i e l r)(*strict*)
    apply(simp add: valid_cfg_def)
   apply(rename_tac d e1 e2 nat i e l r)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac d e1 e2 z nat i e ea l r)(*strict*)
  apply(thin_tac "valid_cfg G")
  apply(thin_tac "valid_cfg (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))")
  apply(thin_tac "cfgRM.derivation (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) d")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr>)")
  apply(thin_tac "d (Suc nat) = Some (pair e1 \<lparr>cfg_conf = v @ teA (F_FRESH (cfg_nonterminals G)) # z\<rparr>)")
  apply(thin_tac "d (Suc (Suc nat)) = Some (pair e2 \<lparr>cfg_conf = v @ teB (F_FRESH (cfg_events G)) # teA (cfg_initial G) # teB (F_FRESH (cfg_events G)) # z\<rparr>)")
  apply(thin_tac "k = 0 \<or> z = []")
  apply(thin_tac "maximum_of_domain d (Suc (Suc nat))")
  apply(thin_tac "setA z = {}")
  apply(thin_tac "d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))), prod_rhs = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>) \<lparr>cfg_conf = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>)")
  apply(thin_tac "Suc 0 \<le> i")
  apply(thin_tac "i < Suc (Suc (Suc nat))")
  apply(thin_tac "d (Suc i) = Some (pair (Some ea) \<lparr>cfg_conf = l @ prod_rhs ea @ r\<rparr>)")
  apply(thin_tac "d i = Some (pair e \<lparr>cfg_conf = l @ teA (prod_lhs ea) # r\<rparr>)")
  apply(thin_tac "ea \<in> cfg_productions (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))")
  apply(thin_tac "setA r = {}")
  apply(clarsimp)
  apply(rename_tac ea l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__dollar_first: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> I \<in> valid_item_set G' k w
  \<Longrightarrow> cfg_item_rhs1 I \<noteq> []
  \<Longrightarrow> \<exists>w'. w = teB Do # w'"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(force)
  apply(unfold valid_item_set_def valid_item_set_n_def)
  apply(simp (no_asm_use))
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
         apply(simp add: F_CFG_AUGMENT__input_def)
        apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(subgoal_tac "\<exists>e w. d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w\<rparr>)")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and m="Suc 0"
      and n="n"
      in terminal_at_beginning_are_never_modified)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
  apply(case_tac "\<delta>")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
   apply(case_tac "\<alpha>")
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa a list)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__ItemInvalid: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> I \<in> valid_item_set G' k w
  \<Longrightarrow> teB x \<in> set (cfg_item_rhs1 I)
  \<Longrightarrow> x \<in> cfg_events G
  \<Longrightarrow> item_core I \<in> cfg_productions G"
  apply(case_tac I)
  apply(rename_tac cfg_item_lhs cfg_item_rhs1a cfg_item_rhs2 cfg_item_look_ahead)(*strict*)
  apply(rename_tac A w1 w2 z)
  apply(rename_tac A w1 w2 z)(*strict*)
  apply(simp add: item_core_def)
  apply(auto)
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(auto)
  apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>) \<lparr>cfg_conf=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>)")
   apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
          apply(force)
         apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
         apply(force)
        apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
        apply(force)
       apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
       apply(force)
      apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
      apply(force)
     apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
    apply(force)
   apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
   apply(force)
  apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
  apply(case_tac n)
   apply(rename_tac A w1 w2 z n d \<delta> e1 e2 za)(*strict*)
   apply(auto)
   apply(rename_tac A w1 w2 z d \<delta> za)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac A w1 w2 z d \<delta> za)(*strict*)
    apply(force)
   apply(rename_tac A w1 w2 z d \<delta> za)(*strict*)
   apply(subgoal_tac "F_FRESH (cfg_events G) \<notin> cfg_events G")
    apply(rename_tac A w1 w2 z d \<delta> za)(*strict*)
    prefer 2
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac A w1 w2 z d \<delta> za)(*strict*)
   apply(case_tac "\<delta>")
    apply(rename_tac A w1 w2 z d \<delta> za)(*strict*)
    apply(auto)
   apply(rename_tac w1 w2 z d)(*strict*)
   apply(case_tac w1)
    apply(rename_tac w1 w2 z d)(*strict*)
    apply(auto)
   apply(rename_tac w2 z d list)(*strict*)
   apply(case_tac list)
    apply(rename_tac w2 z d list)(*strict*)
    apply(auto)
   apply(rename_tac w2 z d lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac w2 z d lista)(*strict*)
    apply(auto)
  apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
  apply(subgoal_tac "setA (\<delta> @ teA A # za) \<subseteq> cfg_nonterminals G")
   apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__later_at_old_grammar)
          apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
          apply(force)
         apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
         apply(force)
        apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
        apply(force)
       apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
       apply(force)
      apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
      apply(force)
     apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
     apply(force)
    apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
    apply(force)
   apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
   apply(force)
  apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc (Suc nat)) = Some (pair (Some e) c)")
   apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
     apply(blast)
    apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
    apply(blast)
   apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
   apply(arith)
  apply(rename_tac A w1 w2 z d \<delta> e1 e2 za nat)(*strict*)
  apply(auto)
  apply(rename_tac A w1 w2 z d \<delta> e1 za nat e)(*strict*)
  apply(subgoal_tac "cfgRM_step_relation (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) \<lparr>cfg_conf = \<delta> @ teA A # za\<rparr> e \<lparr>cfg_conf = \<delta> @ w1 @ w2 @ za\<rparr>")
   apply(rename_tac A w1 w2 z d \<delta> e1 za nat e)(*strict*)
   prefer 2
   apply(simp add: cfgRM.derivation_def)
   apply(erule_tac
      x="Suc (Suc nat)"
      in allE)
   apply(clarsimp)
  apply(rename_tac A w1 w2 z d \<delta> e1 za nat e)(*strict*)
  apply(subgoal_tac "e = \<lparr>prod_lhs = A, prod_rhs = w1 @ w2\<rparr>")
   apply(rename_tac A w1 w2 z d \<delta> e1 za nat e)(*strict*)
   prefer 2
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac A w1 w2 z d \<delta> e1 za nat e l r)(*strict*)
   apply(case_tac e)
   apply(rename_tac A w1 w2 z d \<delta> e1 za nat e l r prod_lhsa prod_rhsa)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac Aa w1 w2 z d \<delta> e1 za nat e l r A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac Aa w1 w2 z d \<delta> e1 za nat l r A w)(*strict*)
   apply(subgoal_tac "za=r")
    apply(rename_tac Aa w1 w2 z d \<delta> e1 za nat l r A w)(*strict*)
    prefer 2
    apply(rule terminalTailEquals1)
      apply(rename_tac Aa w1 w2 z d \<delta> e1 za nat l r A w)(*strict*)
      apply(force)
     apply(rename_tac Aa w1 w2 z d \<delta> e1 za nat l r A w)(*strict*)
     apply(force)
    apply(rename_tac Aa w1 w2 z d \<delta> e1 za nat l r A w)(*strict*)
    apply(force)
   apply(rename_tac Aa w1 w2 z d \<delta> e1 za nat l r A w)(*strict*)
   apply(force)
  apply(rename_tac A w1 w2 z d \<delta> e1 za nat e)(*strict*)
  apply(subgoal_tac "e \<in> cfg_productions (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))")
   apply(rename_tac A w1 w2 z d \<delta> e1 za nat e)(*strict*)
   prefer 2
   apply(simp add: cfgRM_step_relation_def)
  apply(rename_tac A w1 w2 z d \<delta> e1 za nat e)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(rename_tac w1 w2 z d \<delta> e1 za nat)(*strict*)
  apply(subgoal_tac "(F_FRESH (cfg_nonterminals G)) \<in> cfg_nonterminals G")
   apply(rename_tac w1 w2 z d \<delta> e1 za nat)(*strict*)
   prefer 2
   apply(rule_tac
      A="setA (\<delta> @ teA (F_FRESH (cfg_nonterminals G)) # za)"
      in set_mp)
    apply(rename_tac w1 w2 z d \<delta> e1 za nat)(*strict*)
    apply(force)
   apply(rename_tac w1 w2 z d \<delta> e1 za nat)(*strict*)
   apply(rule elemInsetA)
  apply(rename_tac w1 w2 z d \<delta> e1 za nat)(*strict*)
  apply(subgoal_tac "(F_FRESH (cfg_nonterminals G)) \<notin> cfg_nonterminals G")
   apply(rename_tac w1 w2 z d \<delta> e1 za nat)(*strict*)
   prefer 2
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac w1 w2 z d \<delta> e1 za nat)(*strict*)
  apply(force)
  done

lemma F_CFG_AUGMENT__Do_viable_prefix: "
  valid_cfg G
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> viable_prefix G' [teB Do]"
  apply(simp add: viable_prefix_def)
  apply(rule_tac
      x = "der2 \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr> \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr> \<lparr>cfg_conf=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rule der2_maximum_of_domain)
  apply(simp add: der2_def)
  apply(rule_tac
      x="[teB (F_FRESH (cfg_events G))]"
      in exI)
  apply(clarsimp)
  done

lemma F_CFG_AUGMENT__viable_prefix_Do: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> viable_prefix G' [teB Do]"
  apply(simp add: viable_prefix_def)
  apply(rule_tac
      x="(der2 \<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr> \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr> \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)"
      in exI)
  apply(rule conjI)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(rule conjI)
    apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def)
   apply(force)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rule der2_maximum_of_domain)
  apply(simp add: der2_def)
  apply(rule_tac
      x="[teB Do]"
      in exI)
  apply(rule_tac
      x="[teA (cfg_initial G), teB Do]"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule_tac
      x="cfg_initial G'"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(force)
  done

lemma lookaheads_are_kprefixes: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfg_item_lhs I \<in> cfg_nonterminals G
  \<Longrightarrow> I \<in> valid_item_set G' k w
  \<Longrightarrow> \<exists>w. set w \<subseteq> cfg_events G \<and> ((cfg_item_look_ahead I = w \<and> length w = k) \<or> (cfg_item_look_ahead I = w @ [Do] \<and> length w < k))"
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(case_tac n)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
   apply(case_tac "\<delta>")
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<alpha> \<beta> y d e2)(*strict*)
    apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(clarsimp)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac \<alpha> \<beta> y d e2)(*strict*)
     apply(force)
    apply(rename_tac \<alpha> \<beta> y d e2)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: F_LR_PARSER_def)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> e2 z a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf SSc=[teB Do]@w@[teB Do]" for SSc)
   apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and i="nat"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def )
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: F_CFG_AUGMENT__input_def )
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(simp add: cfg_initial_configurations_def get_configuration_def cfg_configurations_def valid_cfg_def)
    apply(simp add: F_CFG_AUGMENT__input_def )
   apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
   apply(force)
  apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w)(*strict*)
  apply(case_tac "\<delta>")
   apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w)(*strict*)
   apply(clarsimp)
  apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w list)(*strict*)
  apply(case_tac "z")
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w list)(*strict*)
   apply(clarsimp)
  apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w list a lista)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. z = w' @ [x']")
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w list a lista)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w list a lista)(*strict*)
  apply(thin_tac "z=a#lista")
  apply(clarsimp)
  apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
  apply(case_tac "k-length w'")
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="filterB(take k w')"
      in exI)
   apply(rule conjI)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
    apply(rule_tac
      B="set (filterB (w'))"
      in subset_trans)
     apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
     apply (metis setATakeRestricted setA_liftB liftBDeConv1 List.set_take_subset)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
    apply (metis setA_Concat2 liftBDeConv2 liftB_in_two_elements_construct_domain_to_subset empty_subsetI subset_empty)
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
   apply(rule disjI1)
   apply(rule_tac
      t="take k w'"
      and s="liftB y"
      in ssubst)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
   apply(rule conjI)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
    apply (metis liftBDeConv1)
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
   apply(rule_tac
      t="filterB (liftB y)"
      and s="y"
      in ssubst)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
    apply (metis liftBDeConv1)
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w')(*strict*)
   apply (metis liftB_reflects_length take_all_length)
  apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="(filterB(w'))"
      in exI)
  apply(rule conjI)
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
   apply(rule_tac
      B="set (filterB (w'))"
      in subset_trans)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
   apply (metis setA_Concat2 liftBDeConv2 liftB_in_two_elements_construct_domain_to_subset empty_subsetI subset_empty)
  apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
  apply(rule disjI2)
  apply(rule conjI)
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
   prefer 2
   apply (metis setA_Concat2 setA_liftB filterBLength empty_subsetI subset_empty zero_less_Suc zero_less_diff)
  apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
  apply(rule liftB_inj)
  apply(rule_tac
      t="liftB y"
      and s="w'@[teB Do]"
      in ssubst)
   apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
   apply(force)
  apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list w' nata)(*strict*)
  apply (metis liftB.simps(2) liftBDeConv1 liftB_commutes_over_concat append_Cons append_Nil2 concat_asso eq_Nil_appendI take_liftB take_append_prime)
  done

lemma no_shift_reduce_conflicts_hlp: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> teB Do \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> teB a \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> (a # y) \<sqsubseteq> y1 \<or> y1 \<sqsubseteq> (a # y)
  \<Longrightarrow> y \<in> cfgSTD_first G' k (\<beta> @ liftB z)
  \<Longrightarrow> A \<in> cfg_nonterminals G
  \<Longrightarrow> B \<in> cfg_nonterminals G
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teB a # \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' (Suc k) (teB Do # w)
  \<Longrightarrow> \<lparr>cfg_item_lhs = B, cfg_item_rhs1 = w2, cfg_item_rhs2 = [], cfg_item_look_ahead = y1\<rparr> \<in> valid_item_set G' (Suc k) (teB Do # w)
  \<Longrightarrow> y1 \<notin> cfgSTD_first G' (Suc k) (teB a # \<beta> @ liftB z)
  \<Longrightarrow> length y \<le> k
  \<Longrightarrow> (\<forall>w v. y = w @ [Do] @ v \<longrightarrow> (v = [] \<and> set w \<subseteq> cfg_events G \<and> (\<exists>w. set w \<subseteq> cfg_events G \<and> z = w @ [Do])))
  \<Longrightarrow> take (Suc k) (a # y) = y1"
  apply(subgoal_tac " (\<exists>w. set w \<subseteq> cfg_events G \<and> ((cfg_item_look_ahead SSI = w \<and> length w=Suc k) \<or> (cfg_item_look_ahead SSI = w@[Do] \<and> length w<Suc k)) )" for SSI)
   prefer 2
   apply(rule_tac
      I="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teB a # \<beta>, cfg_item_look_ahead = z\<rparr>"
      in lookaheads_are_kprefixes)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac " (\<exists>w. set w \<subseteq> cfg_events G \<and> ((cfg_item_look_ahead SSI = w \<and> length w=Suc k) \<or> (cfg_item_look_ahead SSI = w@[Do] \<and> length w<Suc k)) )" for SSI)
   prefer 2
   apply(rule_tac
      I="\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = w2, cfg_item_rhs2 = [], cfg_item_look_ahead = y1\<rparr>"
      in lookaheads_are_kprefixes)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(clarsimp)
  apply(rename_tac n na wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa)(*strict*)
  apply(case_tac n)
   apply(rename_tac n na wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac na wa waa d da \<delta> e2 za \<delta>' e1a e2a zaa)(*strict*)
   apply(case_tac "\<delta>")
    apply(rename_tac na wa waa d da \<delta> e2 za \<delta>' e1a e2a zaa)(*strict*)
    apply(clarsimp)
    apply(rename_tac na wa waa d da e2 \<delta>' e1a e2a za)(*strict*)
    apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(clarsimp)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac na wa waa d da e2 \<delta>' e1a e2a za)(*strict*)
     apply(force)
    apply(rename_tac na wa waa d da e2 \<delta>' e1a e2a za)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add:   F_LR_PARSER_def)
   apply(rename_tac na wa waa d da \<delta> e2 za \<delta>' e1a e2a zaa aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n na wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac na wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat)(*strict*)
  apply(case_tac na)
   apply(rename_tac na wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e2a zaa nat)(*strict*)
   apply(case_tac "\<delta>'")
    apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e2a zaa nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac wa waa d da \<delta> e1 e2 za e2a nat)(*strict*)
    apply(simp add: F_CFG_AUGMENT__input_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(clarsimp)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(rename_tac wa waa d da \<delta> e1 e2 za e2a nat)(*strict*)
     apply(force)
    apply(rename_tac wa waa d da \<delta> e1 e2 za e2a nat)(*strict*)
    apply(rule F_FRESH_is_fresh)
    apply(simp add:   F_LR_PARSER_def)
   apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e2a zaa nat aa list)(*strict*)
   apply(clarsimp)
  apply(rename_tac na wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf SSc=[teB Do]@w@[teB Do]" for SSc)
   apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and i="nat"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def )
    apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: F_CFG_AUGMENT__input_def )
    apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
    apply(simp add: cfg_initial_configurations_def get_configuration_def cfg_configurations_def valid_cfg_def)
    apply(simp add: F_CFG_AUGMENT__input_def )
   apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
   apply(force)
  apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata wb)(*strict*)
  apply(case_tac "\<delta>")
   apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata wb)(*strict*)
   apply(clarsimp)
  apply(rename_tac wa waa d da \<delta> e1 e2 za \<delta>' e1a e2a zaa nat nata wb aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> cfg_conf SSc=[teB Do]@w@[teB Do]" for SSc)
   apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list)(*strict*)
   prefer 2
   apply(rule_tac
      d="da"
      and i="nata"
      in F_CFG_AUGMENT__reachableConf_of_certain_form)
     apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list)(*strict*)
     apply(simp add: F_CFG_AUGMENT__input_def )
    apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list)(*strict*)
    apply(rule cfgSTD.derivation_initialI)
     apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(simp add: F_CFG_AUGMENT__input_def )
    apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list)(*strict*)
    apply(simp add: cfg_initial_configurations_def get_configuration_def cfg_configurations_def valid_cfg_def)
    apply(simp add: F_CFG_AUGMENT__input_def )
   apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list)(*strict*)
   apply(force)
  apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list wc)(*strict*)
  apply(case_tac "\<delta>'")
   apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list wc)(*strict*)
   apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 za \<delta>' e1a e2a zaa nat nata wb list wc aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 za e1a e2a zaa nat nata wb list wc lista)(*strict*)
  apply(subgoal_tac "\<exists>zaa'. liftB zaa'=zaa")
   apply(rename_tac w wa d da e1 e2 za e1a e2a zaa nat nata wb list wc lista)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB zaa"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac w wa d da e1 e2 za e1a e2a zaa nat nata wb list wc lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 za e1a e2a nat nata wb list wc lista zaa')(*strict*)
  apply(subgoal_tac "\<exists>za'. liftB za'=za")
   apply(rename_tac w wa d da e1 e2 za e1a e2a nat nata wb list wc lista zaa')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB za"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac w wa d da e1 e2 za e1a e2a nat nata wb list wc lista zaa')(*strict*)
  apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' za')(*strict*)
  apply(case_tac za')
   apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' za')(*strict*)
   apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' za' aa listb)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. za' = w' @ [x']")
   apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' za' aa listb)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' za' aa listb)(*strict*)
  apply(thin_tac "za'=aa#listb")
  apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' w' x')(*strict*)
  apply(case_tac zaa')
   apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' w' x')(*strict*)
   apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' w' x' aa listb)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. zaa' = w' @ [x']")
   apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' w' x' aa listb)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista zaa' w' x' aa listb)(*strict*)
  apply(thin_tac "zaa'=aa#listb")
  apply(clarsimp)
  apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista w' x' w'nonterminal x'nonterminal)(*strict*)
  apply(thin_tac "setA (liftB (w'nonterminal @ [x'nonterminal])) = {}")
  apply(thin_tac "setA (liftB (w' @ [x'])) = {}")
  apply(subgoal_tac "x'=Do")
   apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista w' x' w'nonterminal x'nonterminal)(*strict*)
   apply(clarsimp)
   apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista w' w'nonterminal x'nonterminal)(*strict*)
   apply(subgoal_tac "wb=list@teA A#(liftB w')")
    apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista w' w'nonterminal x'nonterminal)(*strict*)
    apply(clarsimp)
    apply(rename_tac w wa d da e1 e2 e1a e2a nat nata list wc lista w' w'nonterminal x'nonterminal)(*strict*)
    apply(thin_tac "liftB (w' @ [Do]) = liftB w' @ [teB Do]")
    apply(subgoal_tac "x'nonterminal=Do")
     apply(rename_tac w wa d da e1 e2 e1a e2a nat nata list wc lista w' w'nonterminal x'nonterminal)(*strict*)
     apply(clarsimp)
     apply(rename_tac w wa d da e1 e2 e1a e2a nat nata list wc lista w' w'nonterminal)(*strict*)
     apply(subgoal_tac "wc=lista@teA B#(liftB w'nonterminal)")
      apply(rename_tac w wa d da e1 e2 e1a e2a nat nata list wc lista w' w'nonterminal)(*strict*)
      apply(clarsimp)
      apply(rename_tac w wa d da e1 e2 e1a e2a nat nata list lista w' w'nonterminal)(*strict*)
      apply(thin_tac "liftB (w'nonterminal @ [Do]) = liftB w'nonterminal @ [teB Do]")
      apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')
      apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
      apply(thin_tac "teA A \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
      apply(thin_tac "teA B \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
      apply(subgoal_tac "(a # y) \<sqsubseteq> y1 \<and> y1 \<sqsubseteq> (a # y)")
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
       apply(simp add: prefix_def)
       apply(force)
      apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
      apply(erule_tac
      P="(a # y) \<sqsubseteq> y1"
      in disjE)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
       apply(rule conjI)
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
        apply(force)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
       apply(simp add: prefix_def)
       apply(clarsimp)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' c)(*strict*)
       apply(case_tac c)
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' c)(*strict*)
        apply(force)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' c aa list)(*strict*)
       apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' c aa list)(*strict*)
        prefer 2
        apply(rule NonEmptyListHasTailElem)
        apply(force)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' c aa list)(*strict*)
       apply(thin_tac "c=aa#list")
       apply(clarsimp)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
       apply(case_tac "length y<k")
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        apply(subgoal_tac "suffix y z")
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
         apply(simp add: suffix_def)
         apply(clarsimp)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c)(*strict*)
         apply(subgoal_tac "Suc k - length (liftB v1')=0")
          apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c)(*strict*)
          apply(clarsimp)
          apply(subgoal_tac "v1'=z")
           apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c)(*strict*)
           apply(clarsimp)
           apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v2' w' x' c)(*strict*)          
           apply (smt liftB_reflects_length Suc_leD length_append less_irrefl_nat less_or_eq_imp_le add.commute take_all take_all_length take_append2)
          apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c)(*strict*)
          apply (smt liftB_commute_one_elem_app liftB_reflects_length add_Suc_right add.commute not_add_less1 take_liftB take_all_length take_append take_append2)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c)(*strict*)
         apply(case_tac "Suc k - length (liftB v1')")
          apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c)(*strict*)
          apply(force)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat)(*strict*)
         apply(case_tac z)
          apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat)(*strict*)
          apply(force)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat aa list)(*strict*)
         apply(subgoal_tac "\<exists>w' x'. z = w' @ [x']")
          apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat aa list)(*strict*)
          prefer 2
          apply(rule NonEmptyListHasTailElem)
          apply(force)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat aa list)(*strict*)
         apply(thin_tac "z=aa#list")
         apply(clarsimp)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat w'nonterminal x'nonterminal)(*strict*)
         apply(subgoal_tac "x'nonterminal=Do")
          apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat w'nonterminal x'nonterminal)(*strict*)
          prefer 2
          apply (smt Suc_length add_Suc_right add.commute not_add_less1)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat w'nonterminal x'nonterminal)(*strict*)
         apply(clarsimp)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat w'nonterminal)(*strict*)
         apply(rule_tac
      DO="teB Do"
      and A="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      and w="take (Suc k) (liftB v2')"
      and n="(Suc k - length (liftB v2'))"
      and X="teB Do"
      and ?w1.0="[teB a]@(liftB (c @ w'nonterminal))"
      and ?w2.0="liftB w'"
      and v="v2'"
      and Y="teB x'"
      in LRP_determ_hlp1)
            apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat w'nonterminal)(*strict*)
            apply(force)
           apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat w'nonterminal)(*strict*)
           apply(clarsimp)
           apply(simp add: liftB_commutes_over_concat)
          apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat w'nonterminal)(*strict*)
          apply (smt List.set_take_subset)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' c nat w'nonterminal)(*strict*)
         apply(force)
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        apply(rule cfgSTD_first_suffix_is_shorter)
          apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
          apply(force)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
         apply(force)
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        apply(force)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
       apply(clarsimp)
       apply(case_tac "Suc (length y) - length (liftB v1')")
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        prefer 2
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x' nat)(*strict*)
        apply(force)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "take (Suc (length y)) v1'=z")
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        prefer 2
        apply(rule liftB_inj)
        apply(rule_tac
      t="liftB z"
      and s="take (Suc (length y)) (liftB v1') @ take (Suc (length y) - length (liftB v1')) [teB Do]"
      in ssubst)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
         apply(force)
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        apply(rule_tac
      t="take (Suc (length y) - length (liftB v1')) [teB Do]"
      and s="[]"
      in ssubst)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
         apply(force)
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        apply(rule_tac
      t="take (Suc (length y)) (liftB v1') @ []"
      and s="take (Suc (length y)) (liftB v1')"
      in ssubst)
         apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
         apply(force)
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        apply(force)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "Suc (length y) \<le> length v1'")
        apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
        prefer 2
        apply (simp only: liftB_length)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
       apply(thin_tac "Suc (length y) \<le> length (liftB v1')")
       apply(thin_tac "take (Suc (length y)) (liftB v1') @ take (Suc (length y) - length (liftB v1')) [teB Do] = liftB (take (Suc (length y)) v1')")
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
       apply(thin_tac "a # y @ w' @ [x'] \<notin> cfgSTD_first G' (Suc (length y)) (teB a # \<beta> @ liftB (take (Suc (length y)) v1'))")
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2' w' x')(*strict*)
       apply(thin_tac "cfgRM.derivation G' d1")
       apply(thin_tac "cfgRM.derivation G' d2")
       apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
       apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
       apply(thin_tac "d1 (Suc n1) = Some (pair e1 \<lparr>cfg_conf = teB Do # v1 @ teA A # liftB v1' @ [teB Do]\<rparr>)")
       apply(thin_tac "d2 (Suc n2) = Some (pair e2 \<lparr>cfg_conf = teB Do # v2 @ teA B # liftB v2' @ [teB Do]\<rparr>)")
       apply(thin_tac "d1 (Suc (Suc n1)) = Some (pair e1' \<lparr>cfg_conf = teB Do # v1 @ \<alpha> @ teB a # \<beta> @ liftB v1' @ [teB Do]\<rparr>)")
       apply(thin_tac "d2 (Suc (Suc n2)) = Some (pair e2' \<lparr>cfg_conf = teB Do # v2 @ w2 @ liftB v2' @ [teB Do]\<rparr>)")
       apply(thin_tac "maximum_of_domain d1 (Suc (Suc n1))")
       apply(thin_tac "maximum_of_domain d2 (Suc (Suc n2))")
       apply(clarsimp)
       apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
       apply(erule_tac
      P="a # y @ w' @ [x'] = v2a \<and> length v2a = Suc (length y)"
      in disjE)
        apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
        prefer 2
        apply(clarsimp)
       apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
       apply(clarsimp)
      apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
      apply(thin_tac "cfgRM.derivation G' d1")
      apply(thin_tac "cfgRM.derivation G' d2")
      apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
      apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
      apply(thin_tac "d1 (Suc n1) = Some (pair e1 \<lparr>cfg_conf = teB Do # v1 @ teA A # liftB v1' @ [teB Do]\<rparr>)")
      apply(thin_tac "d2 (Suc n2) = Some (pair e2 \<lparr>cfg_conf = teB Do # v2 @ teA B # liftB v2' @ [teB Do]\<rparr>)")
      apply(thin_tac "d1 (Suc (Suc n1)) = Some (pair e1' \<lparr>cfg_conf = teB Do # v1 @ \<alpha> @ teB a # \<beta> @ liftB v1' @ [teB Do]\<rparr>)")
      apply(thin_tac "d2 (Suc (Suc n2)) = Some (pair e2' \<lparr>cfg_conf = teB Do # v2 @ w2 @ liftB v2' @ [teB Do]\<rparr>)")
      apply(thin_tac "maximum_of_domain d1 (Suc (Suc n1))")
      apply(thin_tac "maximum_of_domain d2 (Suc (Suc n2))")
      apply(rule conjI)
       apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac v1a v2a d1 d2 e1 e1' e2 e2' n1 n2 v1 v2 v1' v2')(*strict*)
      apply(simp add: prefix_def)
      apply(rename_tac v1a v2a v1 v2 v1' v2')(*strict*)
      apply(clarsimp)
      apply(rename_tac v1a v2a v1 v2 v1' v2' c)(*strict*)
      apply(case_tac c)
       apply(rename_tac v1a v2a v1 v2 v1' v2' c)(*strict*)
       apply(force)
      apply(rename_tac v1a v2a v1 v2 v1' v2' c aa list)(*strict*)
      apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
       apply(rename_tac v1a v2a v1 v2 v1' v2' c aa list)(*strict*)
       prefer 2
       apply(rule NonEmptyListHasTailElem)
       apply(force)
      apply(rename_tac v1a v2a v1 v2 v1' v2' c aa list)(*strict*)
      apply(thin_tac "c=aa#list")
      apply(clarsimp)
      apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
      apply(subgoal_tac "False")
       apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
       apply(force)
      apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
      apply(erule_tac
      P="y1 = v2a \<and> length v2a = Suc k"
      in disjE)
       apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
       apply(clarsimp)
       apply(rename_tac v1a v1 v2 v1' v2' w' x')(*strict*)
       apply(case_tac y1)
        apply(rename_tac v1a v1 v2 v1' v2' w' x')(*strict*)
        apply(clarsimp)
       apply(rename_tac v1a v1 v2 v1' v2' w' x' aa list)(*strict*)
       apply(clarsimp)
      apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
      apply(clarsimp)
      apply(case_tac y)
       apply(rename_tac v1a v2a v1 v2 v1' v2' w' x')(*strict*)
       apply(clarsimp)
      apply(rename_tac v1a v2a v1 v2 v1' v2' w' x' aa list)(*strict*)
      apply(subgoal_tac "\<exists>w' x'. y = w' @ [x']")
       apply(rename_tac v1a v2a v1 v2 v1' v2' w' x' aa list)(*strict*)
       prefer 2
       apply(rule NonEmptyListHasTailElem)
       apply(force)
      apply(rename_tac v1a v2a v1 v2 v1' v2' w' x' aa list)(*strict*)
      apply(thin_tac "y=aa#list")
      apply(clarsimp)
      apply(rename_tac v1a v2a v1 v2 v1' v2' w' w'nonterminal x'nonterminal)(*strict*)
      apply(case_tac v2a)
       apply(rename_tac v1a v2a v1 v2 v1' v2' w' w'nonterminal x'nonterminal)(*strict*)
       apply(clarsimp)
      apply(rename_tac v1a v2a v1 v2 v1' v2' w' w'nonterminal x'nonterminal aa list)(*strict*)
      apply(clarsimp)
      apply(rename_tac v1a v1 v2 v1' v2' w' x'nonterminal list)(*strict*)
      apply(case_tac "v2'")
       apply(rename_tac v1a v1 v2 v1' v2' w' x'nonterminal list)(*strict*)
       apply(clarsimp)
      apply(rename_tac v1a v1 v2 v1' v2' w' x'nonterminal list aa lista)(*strict*)
      apply(clarsimp)
      apply(rename_tac v1a v1 v2 v1' w' x'nonterminal list lista)(*strict*)
      apply(erule_tac
      x="list"
      in allE)
      apply(erule_tac
      x="w'@[x'nonterminal]"
      in allE)
      apply(clarsimp)
     apply(rename_tac w wa d da e1 e2 e1a e2a nat nata list wc lista w' w'nonterminal)(*strict*)
     apply(simp add: liftB_commutes_over_concat)
    apply(rename_tac w wa d da e1 e2 e1a e2a nat nata list wc lista w' w'nonterminal x'nonterminal)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista w' w'nonterminal x'nonterminal)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac w wa d da e1 e2 e1a e2a nat nata wb list wc lista w' x' w'nonterminal x'nonterminal)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  done

theorem F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL_valid_item_set: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_item_set G' k [] = F_VALID_ITEM_SET_INITIAL G' F k"
  apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G' F k"
      and s="{\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[],cfg_item_rhs2=[teB Do,teA (cfg_initial G),teB Do],cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
   apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL)
        apply(force)+
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
   apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>) \<lparr>cfg_conf=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>)")
    apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
           apply(force)
          apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(force)
     apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
   apply(case_tac n)
    apply(rename_tac n A \<beta> y d e1 e2 z)(*strict*)
    apply(clarsimp)
    apply(rename_tac y d)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(subgoal_tac "length y = length (liftB y)")
     apply(rename_tac y d)(*strict*)
     prefer 2
     apply(rule liftB_reflects_length)
    apply(rename_tac y d)(*strict*)
    apply(subgoal_tac "length y = length []")
     apply(rename_tac y d)(*strict*)
     prefer 2
     apply(rule_tac
      t="[]"
      and s="liftB y"
      in ssubst)
      apply(rename_tac y d)(*strict*)
      apply(force)
     apply(rename_tac y d)(*strict*)
     apply(blast)
    apply(rename_tac y d)(*strict*)
    apply(force)
   apply(rename_tac n A \<beta> y d e1 e2 z nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
   apply(subgoal_tac "\<exists>e w. d (Suc nat) = Some (pair e \<lparr>cfg_conf = teB (F_FRESH (cfg_events G)) # w\<rparr>)")
    apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc 0"
      in terminal_at_beginning_are_never_modified)
        apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
        apply(rule cfgRM_derivations_are_cfg_derivations)
        apply(force)
       apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
       apply(force)
      apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
      apply(force)
     apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
     apply(force)
    apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac A \<beta> y d e1 e2 z nat)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr> \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr> \<lparr>cfg_conf = teB (F_FRESH (cfg_events G)) # teA (cfg_initial G) # [teB (F_FRESH (cfg_events G))]\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp add: der2_def)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="p" for p
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule conjI)
   apply(simp add: der2_def)
   apply(simp add: F_CFG_AUGMENT_def)
  apply(rule conjI)
   apply(simp add: der2_def)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(rule der2_maximum_of_domain)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO__descent__fp_new_is_from_old_G: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> \<forall>I \<in> S. cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G}
  \<Longrightarrow> \<forall>I \<in> S. cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []
  \<Longrightarrow> I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k S
  \<Longrightarrow> \<forall>I \<in> S. valid_item G' k I
  \<Longrightarrow> (cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G})"
  apply(subgoal_tac "(valid_cfg G
  \<and> cfgSTD_first_compatible F k \<and> Do = F_FRESH (cfg_events G) \<and> S' = F_FRESH (cfg_nonterminals G) \<and> G' = F_CFG_AUGMENT G S' Do \<and> valid_cfg G' \<and> (\<forall>I \<in> S. valid_item G' k I) \<and> (\<forall>I \<in> S. cfg_item_lhs I \<noteq> S' \<longrightarrow> item_core I \<in> cfg_productions G) \<and> (\<forall>I \<in> S. cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (\<forall>I \<in> S. cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G})) \<longrightarrow> (\<forall>I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k S. (cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G}))")
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_new_is_kPrefix)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(erule impE)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    apply(force)
   apply(rule conjI)
    prefer 2
    apply(rule conjI)
     apply(force)
    apply(force)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac Ia)(*strict*)
  apply(erule_tac
      x="Ia"
      and P="\<lambda>Ia. valid_item (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k Ia"
      in ballE)
   apply(rename_tac Ia)(*strict*)
   apply(simp add: item_core_def valid_item_def)
   apply(clarsimp)
   apply(rename_tac Ia p)(*strict*)
   apply(case_tac Ia)
   apply(rename_tac Ia p cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_aheada)(*strict*)
   apply(clarsimp)
   apply(rename_tac p cfg_item_rhs1 cfg_item_rhs2 cfg_item_look_aheada)(*strict*)
   apply(rename_tac w1 w2 la)
   apply(rename_tac p w1 w2 la)(*strict*)
   apply(case_tac p)
   apply(rename_tac p w1 w2 la prod_lhsa prod_rhsa)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac p w1 w2 la A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 w2 la A)(*strict*)
   apply(simp add: F_CFG_AUGMENT_def)
  apply(rename_tac Ia)(*strict*)
  apply(clarsimp)
  done

theorem valid_item_set_to_valid_item_set__recursive: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> valid_item_set G k w = valid_item_set__recursive G F k w"
  apply(clarsimp)
  apply(subgoal_tac "setA w \<subseteq> cfg_nonterminals G \<and> setB w \<subseteq> cfg_events G \<longrightarrow> valid_item_set G k w = valid_item_set__recursive G F k w")
   apply(force)
  apply(thin_tac "setA w \<subseteq> cfg_nonterminals G")
  apply(thin_tac "setB w \<subseteq> cfg_events G")
  apply(induct w rule: length_induct)
  apply(rename_tac xs)(*strict*)
  apply(case_tac xs)
   apply(rename_tac xs)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="valid_item_set G k []"
      and s="(if []=[] then F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL G F k) else F_VALID_ITEM_SET_GOTO__descent__fp G F k (essential_items (valid_item_set G k [])) )"
      in ssubst)
    apply(rule Lemma6__23)
       apply(blast)+
     apply(simp add: setA_def)
    apply(simp add: setB_def)
   apply(clarsimp)
   apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_idemp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
  apply(rename_tac xs a list)(*strict*)
  apply(rule impI,erule conjE)
  apply(subgoal_tac "\<exists>w' X. xs=w'@[X]")
   apply(rename_tac xs a list)(*strict*)
   apply(erule exE)+
   apply(rename_tac xs a list w' X)(*strict*)
   apply(rule_tac
      t="xs"
      and s="w'@[X]"
      in ssubst)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(force)
   apply(rename_tac xs a list w' X)(*strict*)
   apply(rule_tac
      t="valid_item_set G k (w' @ [X])"
      and s="F_VALID_ITEM_SET_GOTO G F k X (valid_item_set G k w')"
      in ssubst)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(rule Lemma6__26)
       apply(rename_tac xs a list w' X)(*strict*)
       apply(blast)
      apply(force)
     apply(rename_tac xs a list w' X)(*strict*)
     apply(force)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(force)
   apply(rename_tac xs a list w' X)(*strict*)
   apply(erule_tac
      x="w'"
      in allE)
   apply(erule impE)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(force)
   apply(rename_tac xs a list w' X)(*strict*)
   apply(erule impE)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(force)
   apply(rename_tac xs a list w' X)(*strict*)
   apply(erule impE)
    apply(force)
   apply(erule impE)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(rule conjI)
     apply(rename_tac xs a list w' X)(*strict*)
     apply(rule setA_Concat2)
      apply(rename_tac xs a list w' X)(*strict*)
      apply(blast)+
    apply(rename_tac xs a list w' X)(*strict*)
    apply(rule setB_Concat2)
     apply(rename_tac xs a list w' X)(*strict*)
     apply(blast)+
   apply(rename_tac xs a list w' X)(*strict*)
   apply(rule_tac
      t="valid_item_set G k w'"
      and s="valid_item_set__recursive G F k w'"
      in ssubst)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(force)
   apply(rename_tac xs a list w' X)(*strict*)
   apply(thin_tac "valid_item_set G k w' = valid_item_set__recursive G F k w'")
   apply(thin_tac "xs = a # list")
   apply(rule_tac
      t="valid_item_set__recursive SSG SSF SSk SSw"
      and s="(case SSw of [] \<Rightarrow> F_VALID_ITEM_SET_INITIAL SSG SSF SSk | y # w' \<Rightarrow> F_VALID_ITEM_SET_GOTO SSG SSF SSk (last SSw) (valid_item_set__recursive SSG SSF SSk (butlast SSw)))" for SSG SSF SSk SSw
      in ssubst)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(rule valid_item_set__recursive.simps)
   apply(rename_tac xs a list w' X)(*strict*)
   apply(rule_tac
      t="last(w'@[X])"
      and s="X"
      in ssubst)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(force)
   apply(rename_tac xs a list w' X)(*strict*)
   apply(rule_tac
      t="butlast(w'@[X])"
      and s="w'"
      in ssubst)
    apply(rename_tac xs a list w' X)(*strict*)
    apply(force)
   apply(rename_tac xs a list w' X)(*strict*)
   apply(case_tac "w'@[X]")
    apply(rename_tac xs a list w' X)(*strict*)
    apply(force)
   apply(rename_tac xs a list w' X aa lista)(*strict*)
   apply(force)
  apply(rename_tac xs a list)(*strict*)
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  done

definition viable_prefix_ALT2 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> bool"
  where
    "viable_prefix_ALT2 G \<gamma> \<equiv>
  \<exists>d n \<omega> y A \<delta> e e'.
    cfgRM.derivation_initial G d
    \<and> d n = Some (pair e \<lparr>cfg_conf = \<delta> @ [teA A] @ liftB y\<rparr>)
    \<and> d (Suc n) = Some (pair e' \<lparr>cfg_conf = \<delta> @ \<omega> @ liftB y\<rparr>)
    \<and> prefix \<gamma> (\<delta> @ \<omega>)"

lemma viable_prefix_ALT2_vs_viable_prefix: "
  valid_cfg (G:: ('nonterminal, 'event) cfg)
  \<Longrightarrow> cfgSTD_first_compatible (F:: ('nonterminal, 'event) DT_first_function) k
  \<Longrightarrow> viable_prefix G \<gamma> = viable_prefix_ALT2 G \<gamma>"
  apply(rule antisym)
   apply(simp add: viable_prefix_ALT2_def viable_prefix_def)
   apply(clarsimp)
   apply(rule_tac x="d" in exI)
   apply(rule conjI)
    apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def cfgRM.derivation_initial_def)
   apply(rule_tac x="n" in exI)
   apply(clarsimp)
   apply(rule_tac x="\<alpha>@\<beta>" in exI)
   apply(rule_tac x="filterB y" in exI)
   apply(rule_tac x="A" in exI)
   apply(rule_tac x="\<delta>" in exI)
   apply(simp add: prefix_def)
   apply (metis liftBDeConv2)
  apply(clarsimp)
  apply(simp add: prefix_def viable_prefix_ALT2_def)
  apply(clarsimp)
  apply(case_tac "prefix \<delta> \<gamma>")
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(simp add: viable_prefix_ALT2_def viable_prefix_def)
   apply(rule_tac x="derivation_take d (Suc n)" in exI)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(force)
   apply(rule_tac x="n" in exI)
   apply(rule conjI)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rule conjI)
    apply(simp add: derivation_take_def)
    apply(case_tac "d 0")
     apply(clarsimp)
    apply(clarsimp)
    apply(case_tac a)
    apply(clarsimp)
    apply(simp add: cfg_initial_configurations_def)
   apply(rule_tac x="ca" in exI)
   apply(rule_tac x="c" in exI)
   apply(rule_tac x="liftB y" in exI)
   apply(rule_tac x="A" in exI)
   apply(rule_tac x="\<delta>" in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="Suc n" and
      m="Suc n"
      in cfgRM.pre_some_position_is_some_position_prime)
       apply(blast)
      apply(blast)
     apply(force)
    apply(clarsimp)
   apply(clarsimp)
   apply (metis setA_liftB_empty)
  apply(subgoal_tac "\<lparr>cfg_conf = \<delta> @ \<omega> @ liftB y\<rparr> \<in> cfg_configurations G")
   prefer 2
   apply (metis cfgRM.derivation_initial_configurations)
  apply(subgoal_tac "\<gamma> \<sqsubseteq> \<delta>")
   prefer 2
   apply (metis (full_types) prefix_append prefix_append1)
  apply(thin_tac "\<not> \<delta> \<sqsubseteq> \<gamma>")
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rule_tac v="\<gamma>" and x="ca" and F="F" and k="k" in viable_prefix_nonempty_on_every_prefix)
       apply(force)
      apply(force)
     prefer 2
     apply(force)
    prefer 2
    apply(simp add: cfg_configurations_def)
    apply(simp add: simpY)
   prefer 2
   apply(simp add: cfg_configurations_def)
   apply(simp add: simpY)
  apply(simp add: viable_prefix_ALT2_def viable_prefix_def)
  apply(rule_tac x="derivation_take d (Suc n)" in exI)
  apply(simp add: cfgRM.derivation_initial_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule cfgRM.derivation_take_preserves_derivation)
   apply(force)
  apply(rule_tac x="n" in exI)
  apply(rule conjI)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rule conjI)
   apply(simp add: derivation_take_def)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(clarsimp)
   apply(case_tac a)
   apply(clarsimp)
   apply(simp add: cfg_initial_configurations_def)
  apply(rule_tac x="[]" in exI)
  apply(rule_tac x="\<omega>" in exI)
  apply(rule_tac x="liftB y" in exI)
  apply(rule_tac x="A" in exI)
  apply(rule_tac x="\<gamma>@ca" in exI)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      n="Suc n" and
      m="Suc n"
      in cfgRM.pre_some_position_is_some_position_prime)
      apply(blast)
     apply(blast)
    apply(force)
   apply(clarsimp)
  apply(clarsimp)
  apply (metis setA_liftB_empty)
  done

end
