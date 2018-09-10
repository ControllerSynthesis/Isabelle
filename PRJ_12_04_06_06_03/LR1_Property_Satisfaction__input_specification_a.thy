section {*LR1\_Property\_Satisfaction\_\_input\_specification\_a*}
theory
  LR1_Property_Satisfaction__input_specification_a

imports
  PRJ_12_04_06_06_03__ENTRY

begin

definition CFG_no_self_loop :: "
  ('a, 'b) cfg
  \<Rightarrow> bool"
  where
    "CFG_no_self_loop G \<equiv>
   (\<forall>e\<in> cfg_productions G. [teA (prod_lhs e)] \<noteq> prod_rhs e)"

definition CFGuniqueElim :: "
  ('a, 'b) cfg
  \<Rightarrow> bool"
  where
    "CFGuniqueElim G \<equiv>
   ( \<forall>d1 d2 \<pi>1 \<pi>2 c. cfgLM.trans_der G d1 c \<pi>1 \<lparr>cfg_conf = []\<rparr> \<longrightarrow> cfgLM.trans_der G d2 c \<pi>2 \<lparr>cfg_conf = []\<rparr> \<longrightarrow> \<pi>1 = \<pi>2)"

definition CFGtermLeft :: "
  ('a, 'b) cfg
  \<Rightarrow> bool"
  where
    "CFGtermLeft G \<equiv>
   ( \<forall>d c \<pi> c'. cfgLM.trans_der G d c \<pi> c' \<longrightarrow> (\<exists>w1 w2. cfg_conf c = (liftB w1) @ (liftA w2)) \<longrightarrow> (\<exists>w1 w2. cfg_conf c' = (liftB w1) @ (liftA w2)))"

definition CFGdetEntire :: "
  ('a, 'b) cfg
  \<Rightarrow> bool"
  where
    "CFGdetEntire G \<equiv>
   ( \<forall>d \<pi> w d1 d2 \<pi>1 \<pi>2 v v1 v2. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf = (v1 @ w @ v2)\<rparr> \<longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf = w\<rparr> \<pi>1 \<lparr>cfg_conf = v\<rparr> \<longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf = w\<rparr> \<pi>2 \<lparr>cfg_conf = v\<rparr> \<longrightarrow> \<pi>1 = \<pi>2)"

definition CFGdetProduceLength2 :: "
  ('a, 'b) cfg
  \<Rightarrow> bool"
  where
    "CFGdetProduceLength2 G \<equiv>
   ( \<forall>d1 d2 d \<pi>1 \<pi>2 S \<alpha> A v1 v2 \<pi> b v3. cfgLM.trans_der G d1 \<lparr>cfg_conf = [teA S]\<rparr> \<pi>1 \<lparr>cfg_conf = liftB \<alpha> @ teA A # v1\<rparr> \<longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA S]\<rparr> \<pi>2 \<lparr>cfg_conf = liftB \<alpha> @ teA A # v2\<rparr> \<longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = [teA A]\<rparr> \<pi> \<lparr>cfg_conf = teB b # v3\<rparr> \<longrightarrow> length \<pi>1 = length \<pi>2)"

definition CFG_not_end_nterm :: "
  ('a, 'b) cfg
  \<Rightarrow> 'a set"
  where
    "CFG_not_end_nterm G \<equiv>
  {A. \<exists>d n e w1 w2. cfgLM.derivation_initial G d
  \<and> d n = Some (pair e \<lparr>cfg_conf = w1 @ [teA A] @ w2\<rparr>)
  \<and> w2 \<noteq> [] }"

definition CFGprodXORelim :: "
  ('a, 'b) cfg
  \<Rightarrow> bool"
  where
    "CFGprodXORelim G \<equiv>
   ( \<forall>d1 A \<pi>1 d2 \<pi>2 b w. A \<in> CFG_not_end_nterm G \<longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf = [teA A]\<rparr> \<pi>1 \<lparr>cfg_conf = []\<rparr> \<longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf = [teA A]\<rparr> \<pi>2 \<lparr>cfg_conf = teB b # w\<rparr> \<longrightarrow> False )"

definition split_TSstructure :: "
  ('a, 'b) cfg
  \<Rightarrow> bool"
  where
    "split_TSstructure G \<equiv>
  valid_cfg G
  \<and> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<and> CFGlm_unambiguous G
  \<and> CFG_no_self_loop G
  \<and> CFGuniqueElim G
  \<and> LR1ProdFormSimp G
  \<and> CFGtermLeft G
  \<and> CFGdetEntire G
  \<and> CFGdetProduceLength2 G
  \<and> CFGprodXORelim G"

lemma CFGlm_unambiguous_implies_CFG_no_self_loop: "
  valid_cfg G
  \<Longrightarrow> CFGlm_unambiguous G
  \<Longrightarrow> cfg_nonterminals G = cfgLM_accessible_nonterminals G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> CFG_no_self_loop G"
  apply(simp add: CFG_no_self_loop_def CFGlm_unambiguous_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(case_tac e)
  apply(rename_tac e prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac e A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac A)(*strict*)
  apply(subgoal_tac "A \<in> cfgLM_accessible_nonterminals G")
   apply(rename_tac A)(*strict*)
   prefer 2
   apply(simp add: valid_cfg_def)
   apply(force)
  apply(rename_tac A)(*strict*)
  apply(subgoal_tac "\<exists>d n c. cfgLM.derivation_initial G d \<and> get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2)")
   apply(rename_tac A)(*strict*)
   prefer 2
   apply(thin_tac "cfg_nonterminals G = cfgLM_accessible_nonterminals G")
   apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(rename_tac A)(*strict*)
  apply(clarsimp)
  apply(rename_tac A d n c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac A d n c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac A d n w1 w2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(rename_tac A d n w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac A d n w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac A d n w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac A d n w1 w2 option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac A d n w1 w2 e)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<in> cfg_configurations G")
   apply(rename_tac A d n w1 w2 e)(*strict*)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac A d n w1 w2 e)(*strict*)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(rename_tac A d n w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac A d n w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac A d n w1 w2 e)(*strict*)
   apply(force)
  apply(rename_tac A d n w1 w2 e)(*strict*)
  apply(subgoal_tac "\<exists>d n e v. cfgLM.derivation SSG d \<and> d 0 = Some (pair None \<lparr>cfg_conf = SSw\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB v\<rparr>)" for SSG SSw)
   apply(rename_tac A d n w1 w2 e)(*strict*)
   prefer 2
   apply(rule_tac
      w="liftB w1 @ teA A # w2"
      in construct_elimininating_derivation_prime)
     apply(rename_tac A d n w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac A d n w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac A d n w1 w2 e)(*strict*)
   apply(simp add: cfg_configurations_def)
  apply(rename_tac A d n w1 w2 e)(*strict*)
  apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(thin_tac "cfgSTD_Nonblockingness_nonterminals G = cfgLM_accessible_nonterminals G")
  apply(thin_tac "cfg_nonterminals G = cfgLM_accessible_nonterminals G")
  apply(erule_tac
      x="derivation_append d da n"
      in allE)
  apply(erule impE)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
     apply(force)
    apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
    apply(force)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
    apply(force)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(erule_tac
      x="derivation_append d (derivation_append (der2 \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA A]\<rparr> \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr>) da (Suc 0)) n"
      in allE)
  apply(erule impE)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
     apply(force)
    apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
    apply(force)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
      apply(rule cfgLM.der2_is_derivation)
      apply(simp add: cfgLM_step_relation_def)
      apply(rule_tac
      x="liftB w1"
      in exI)
      apply(clarsimp)
      apply(rule setA_liftB)
     apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
     apply(force)
    apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(erule_tac
      x="n+na"
      in allE)
  apply(erule_tac
      x="n+(Suc 0+na)"
      in allE)
  apply(erule_tac
      x="if na=0 then e else ea"
      in allE)
  apply(erule_tac
      x="if na=0 then (Some \<lparr>prod_lhs = A, prod_rhs = [teA A]\<rparr>) else ea"
      in allE)
  apply(erule_tac
      x="v"
      in allE)
  apply(erule impE)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(erule impE)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(subgoal_tac "derivation_append d da n (n+na) = derivation_append d (derivation_append (der2 \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA A]\<rparr> \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr>) da (Suc 0)) n(n+na)")
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(thin_tac "derivation_append d da n = derivation_append d (derivation_append (der2 \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA A]\<rparr> \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr>) da (Suc 0)) n")
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(subgoal_tac "derivation_append d da n (n + na) \<noteq> derivation_append d (derivation_append (der2 \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA A]\<rparr> \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr>) da (Suc 0)) n (n + na)")
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(force)
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(thin_tac "derivation_append d da n (n + na) = derivation_append d (derivation_append (der2 \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = [teA A]\<rparr> \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr>) da (Suc 0)) n (n + na)")
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rule conjI)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
    apply(case_tac na)
     apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
     apply(clarsimp)
     apply(rename_tac A d n w1 w2 e da v)(*strict*)
     apply (metis list.simps(3) maximalPrefixB_liftB maximalPrefixB_drop_liftB maximalPrefixB_front self_append_conv)
    apply(rename_tac A d n w1 w2 e da na ea v nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(clarsimp)
   apply(rename_tac A d n w1 w2 e da na v)(*strict*)
   apply (metis list.simps(3) maximalPrefixB_liftB maximalPrefixB_drop_liftB maximalPrefixB_front self_append_conv)
  apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
  apply(clarsimp)
  apply(case_tac na)
   apply(rename_tac A d n w1 w2 e da na ea v)(*strict*)
   apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da na ea v nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da ea v nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac A d n w1 w2 e da ea v nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da ea v nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da ea v nata)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. da (Suc nata) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac A d n w1 w2 e da ea v nata)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(Suc nata)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac A d n w1 w2 e da ea v nata)(*strict*)
     apply(force)
    apply(rename_tac A d n w1 w2 e da ea v nata)(*strict*)
    apply(clarsimp)
    apply(case_tac "da (Suc nata)")
     apply(rename_tac A d n w1 w2 e da ea v nata)(*strict*)
     apply(force)
    apply(rename_tac A d n w1 w2 e da ea v nata a)(*strict*)
    apply(force)
   apply(rename_tac A d n w1 w2 e da ea v nata)(*strict*)
   apply(force)
  apply(rename_tac A d n w1 w2 e da ea v nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da v nata e2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac A d n w1 w2 e da v nata e2 l r)(*strict*)
  apply (metis setA_liftB elemInsetA emptyE)
  done

lemma CFGlm_unambiguous_implies_CFGuniqueElim: "
  valid_cfg G
  \<Longrightarrow> CFGlm_unambiguous G
  \<Longrightarrow> cfg_nonterminals G = cfgLM_accessible_nonterminals G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> CFGuniqueElim G"
  apply(simp add: CFGuniqueElim_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
  apply(subgoal_tac "setB w={}")
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
   prefer 2
   apply(thin_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = w\<rparr> \<pi>2 \<lparr>cfg_conf = []\<rparr>")
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
   apply(case_tac "setB w={}")
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
   apply(subgoal_tac "\<exists>x. x \<in> setB w")
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 \<pi>1 w x)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1 @ [teB SSx] @ w2 = SSw" for SSx SSw)
    apply(rename_tac d1 \<pi>1 w x)(*strict*)
    prefer 2
    apply(rule setB_decomp)
    apply(force)
   apply(rename_tac d1 \<pi>1 w x)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 \<pi>1 x w1 w2)(*strict*)
   apply(simp add: simpY)
   apply(subgoal_tac "\<exists>w1 w2. cfg_conf \<lparr>cfg_conf = []\<rparr> = w1 @ (liftB [x]) @ w2")
    apply(rename_tac d1 \<pi>1 x w1 w2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and G="G"
      in cfgLM_trans_der_preserves_terminals)
     apply(rename_tac d1 \<pi>1 x w1 w2)(*strict*)
     apply(force)
    apply(rename_tac d1 \<pi>1 x w1 w2)(*strict*)
    apply(force)
   apply(rename_tac d1 \<pi>1 x w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftA l' = w")
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterA w"
      in exI)
   apply (metis List.set_simps(1) setB_empty_then_liftA_vs_filterA)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
  apply(thin_tac "setB (liftA l') = {}")
  apply(subgoal_tac "\<exists>\<pi>1s. length \<pi>1s = length l' \<and> elim_map G l' \<pi>1s (map (\<lambda>x. []) l') \<and> foldl (@) [] \<pi>1s = \<pi>1")
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
   apply(subgoal_tac "\<exists>\<pi>2s. length \<pi>2s = length l' \<and> elim_map G l' \<pi>2s (map (\<lambda>x. []) l') \<and> foldl (@) [] \<pi>2s = \<pi>2")
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
    apply(subgoal_tac "\<pi>1s=\<pi>2s")
     apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
    apply(rule elim_map_equal_by_CFGlm_unambiguous)
            apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
            apply(force)
           apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
           apply(force)
          apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
          apply(force)
         apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 l' \<pi>1s \<pi>2s)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
   apply(thin_tac "\<exists>\<pi>1s. length \<pi>1s = length l' \<and> elim_map G l' \<pi>1s (map (\<lambda>x. []) l') \<and> foldl (@) [] \<pi>1s = \<pi>1")
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
   apply(rule eliminating_derivation_to_elim_map)
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
   apply(force)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
  apply(rule eliminating_derivation_to_elim_map)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
   apply(force)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 l')(*strict*)
  apply(force)
  done

lemma LR1ProdFormSimp_implies_CFGtermLeft_hlp: "
valid_cfg G
  \<Longrightarrow> LR1ProdFormSimp G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> get_labels d (length \<pi>) = map Some \<pi>
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = liftB w1 @ liftA w2\<rparr>)
  \<Longrightarrow> d (length \<pi>) = Some (pair e c')
  \<Longrightarrow> \<exists>w1 w2. cfg_conf c' = liftB w1 @ liftA w2"
  apply(induct \<pi> arbitrary: e c' rule: rev_induct)
   apply(rename_tac e c')(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac x xs e c')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs e c')(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs e c')(*strict*)
     apply(force)
    apply(rename_tac x xs e c')(*strict*)
    apply(clarsimp)
   apply(rename_tac x xs e c')(*strict*)
   apply(force)
  apply(rename_tac x xs e c')(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 c1 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac x xs c' e1 e2 c1 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac x xs c' e1 e2 c1 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 c1 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e2)
  apply(rename_tac x xs c' e1 e2 c1 r l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 c1 r l' prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac x xs c' e1 c1 r l' A w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs c' e1 c1 r l' A w cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 r l' A w)(*strict*)
  apply(case_tac c')
  apply(rename_tac x xs c' e1 r l' A w cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 r l' A w)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = liftB l' @ teA A # r\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x xs e1 r l' A w)(*strict*)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs e1 r l' A w)(*strict*)
    apply(force)
   apply(rename_tac x xs e1 r l' A w)(*strict*)
   apply(force)
  apply(rename_tac x xs e1 r l' A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 r l' A w w1a w2a)(*strict*)
  apply(case_tac w2a)
   apply(rename_tac x xs e1 r l' A w w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs e1 r l' A w w1a)(*strict*)
   apply (metis teA_not_in_liftB elem_set_app head_in_set)
  apply(rename_tac x xs e1 r l' A w w1a w2a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 r l' A w w1a a list)(*strict*)
  apply(subgoal_tac "l'=w1a")
   apply(rename_tac x xs e1 r l' A w w1a a list)(*strict*)
   prefer 2
   apply (metis liftA.simps(2) simple_identify)
  apply(rename_tac x xs e1 r l' A w w1a a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 w w1a a list)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac x xs e1 wa w1a A w)(*strict*)
  apply(thin_tac "cfgLM.derivation G d")
  apply(thin_tac "cfgLM.belongs G d")
  apply(thin_tac "get_labels d (Suc (length xs)) = map Some xs @ [Some x]")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = liftB w1 @ liftA w2\<rparr>)")
  apply(rename_tac x xs e1 wa w1 A w)(*strict*)
  apply(thin_tac "d (Suc (length xs)) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = wa\<rparr>) \<lparr>cfg_conf = liftB w1 @ wa @ liftA w\<rparr>)")
  apply(rename_tac x xs e1 wa w1 A w)(*strict*)
  apply(thin_tac "d (length xs) = Some (pair e1 \<lparr>cfg_conf = liftB w1 @ teA A # liftA w\<rparr>)")
  apply(clarsimp)
  apply(rename_tac wa w1 A w)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. wa = liftB w1 @ liftA w2")
   apply(rename_tac wa w1 A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 A w w1a w2)(*strict*)
   apply(rule_tac
      x="w1@w1a"
      in exI)
   apply(rule_tac
      x="w2@w"
      in exI)
   apply(simp add: simpY)
  apply(rename_tac wa w1 A w)(*strict*)
  apply(simp add: LR1ProdFormSimp_def)
  apply(rename_tac wa A)(*strict*)
  apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = wa\<rparr>"
      in ballE)
   apply(rename_tac wa A)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac wa A)(*strict*)
  apply(clarsimp)
  apply(thin_tac "\<lparr>prod_lhs = A, prod_rhs = wa\<rparr> \<in> cfg_productions G")
  apply(erule disjE)
   apply(rename_tac wa A)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(force)
  apply(rename_tac wa A)(*strict*)
  apply(clarsimp)
  apply(rename_tac wa A b Aa B)(*strict*)
  apply(erule disjE)
   apply(rename_tac wa A b Aa B)(*strict*)
   apply(clarsimp)
   apply(rename_tac b B)(*strict*)
   apply(rule_tac
      x="[b]"
      in exI)
   apply(clarsimp)
   apply(rename_tac B)(*strict*)
   apply(rule_tac
      x="[B]"
      in exI)
   apply(force)
  apply(rename_tac wa A b Aa B)(*strict*)
  apply(clarsimp)
  apply(rename_tac wa A Aa B)(*strict*)
  apply(erule disjE)
   apply(rename_tac wa A Aa B)(*strict*)
   apply(clarsimp)
   apply(rename_tac B)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="[B]"
      in exI)
   apply(force)
  apply(rename_tac wa A Aa B)(*strict*)
  apply(clarsimp)
  apply(rename_tac B C)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="[B,C]"
      in exI)
  apply(force)
  done

lemma LR1ProdFormSimp_implies_CFGtermLeft: "
  valid_cfg G
  \<Longrightarrow> LR1ProdFormSimp G
  \<Longrightarrow> CFGtermLeft G"
  apply(simp add: CFGtermLeft_def)
  apply(clarsimp)
  apply(rename_tac d c \<pi> c' w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac d c \<pi> c' w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<pi> c' w1 w2)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac d \<pi> c' w1 w2 e)(*strict*)
  apply(rule LR1ProdFormSimp_implies_CFGtermLeft_hlp)
        apply(rename_tac d \<pi> c' w1 w2 e)(*strict*)
        apply(force)+
  done

lemma CFGlm_unambiguous_implies_CFGdetEntire: "
  valid_cfg G
  \<Longrightarrow> CFGlm_unambiguous G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> CFGdetEntire G"
  apply(simp add: CFGdetEntire_def)
  apply(clarsimp)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = v1 @ w @ v2\<rparr> \<in> cfg_configurations G")
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v e ea eb)(*strict*)
   apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v e ea eb)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v e ea eb)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = v\<rparr> \<in> cfg_configurations G")
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v e ea eb)(*strict*)
   apply(rule_tac
      d="d1"
      in cfgLM.belongs_configurations)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v e ea eb)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v e ea eb)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
  apply(subgoal_tac "\<exists>dv1 \<pi>v1 \<alpha>v1. cfgLM.trans_der G dv1 \<lparr>cfg_conf=v1\<rparr> \<pi>v1 \<lparr>cfg_conf=liftB \<alpha>v1\<rparr>")
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>d n e v. cfgLM.derivation SSG d \<and> d 0 = Some (pair None \<lparr>cfg_conf = SSw\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB v\<rparr>)" for SSG SSw)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
    prefer 2
    apply(rule_tac
      w="v1"
      in construct_elimininating_derivation_prime)
      apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
      apply(force)
     apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(rule_tac
      x="map the (get_labels da n)"
      in exI)
   apply(rule_tac
      x="va"
      in exI)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
   apply(rule conjI)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
    apply(rule cfgLM.derivation_belongs)
       apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
       apply(force)
      apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
      apply(force)
     apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
     apply(simp add: cfg_configurations_def simpY)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
   apply(rule_tac
      t="length (get_labels da n)"
      and s="n"
      in ssubst)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
   apply(rule conjI)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v da n e va ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
  apply(subgoal_tac "\<exists>dt \<pi>t \<alpha>t. cfgLM.trans_der G dt \<lparr>cfg_conf=v@v2\<rparr> \<pi>t \<lparr>cfg_conf=liftB \<alpha>t\<rparr>")
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>d n e v. cfgLM.derivation SSG d \<and> d 0 = Some (pair None \<lparr>cfg_conf = SSw\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB v\<rparr>)" for SSG SSw)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
    prefer 2
    apply(rule_tac
      w="v@v2"
      in construct_elimininating_derivation_prime)
      apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
      apply(force)
     apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(rule_tac
      x="map the (get_labels da n)"
      in exI)
   apply(rule_tac
      x="va"
      in exI)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
   apply(rule conjI)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
    apply(rule cfgLM.derivation_belongs)
       apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
       apply(force)
      apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
      apply(force)
     apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
     apply(simp add: cfg_configurations_def simpY)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
   apply(rule_tac
      t="length (get_labels da n)"
      and s="n"
      in ssubst)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
   apply(rule conjI)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 da \<pi>v1 \<alpha>v1 n e va ea eb ec ed)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v)(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB \<alpha>t\<rparr> \<in> cfg_configurations G")
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t e ea eb ec ed)(*strict*)
   apply(rule_tac
      d="dt"
      in cfgLM.belongs_configurations)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t e ea eb ec ed)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t e ea eb ec ed)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB \<alpha>v1\<rparr> \<in> cfg_configurations G")
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t e ea eb ec ed)(*strict*)
   apply(rule_tac
      d="dv1"
      in cfgLM.belongs_configurations)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t e ea eb ec ed)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t e ea eb ec ed)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
  apply(subgoal_tac "\<exists>d1'. cfgLM.trans_der G d1' \<lparr>cfg_conf = liftB \<alpha>v1@w@v2\<rparr> \<pi>1 \<lparr>cfg_conf = liftB \<alpha>v1@v@v2\<rparr>")
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
   prefer 2
   apply(rule cfgLM_trans_der_context_prime)
     apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d1 \<lparr>cfg_conf = w\<rparr> \<pi>1 \<lparr>cfg_conf = v\<rparr>")
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
  apply(subgoal_tac "\<exists>d2'. cfgLM.trans_der G d2' \<lparr>cfg_conf = liftB \<alpha>v1@w@v2\<rparr> \<pi>2 \<lparr>cfg_conf = liftB \<alpha>v1@v@v2\<rparr>")
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
   prefer 2
   apply(rule cfgLM_trans_der_context_prime)
     apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = w\<rparr> \<pi>2 \<lparr>cfg_conf = v\<rparr>")
  apply(rename_tac d \<pi> w v1 v2 d1 d2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t)(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2')(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB [] @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB [] @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSw1' SSw2)
   apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2')(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="dv1"
      and ?w2.0="w@v2"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2')(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2')(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2')(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2')(*strict*)
  apply(thin_tac "cfgLM.trans_der G dv1 \<lparr>cfg_conf = v1\<rparr> \<pi>v1 \<lparr>cfg_conf = liftB \<alpha>v1\<rparr>")
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dv1 dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2')(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2' da)(*strict*)
  apply(rename_tac dv1)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2' dv1)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2' dv1)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d2'"
      and ?d2.0="dt"
      and ?v1.0="\<alpha>v1"
      and ?v2.0="v@v2"
      and ?v4.0="[]"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2' dv1)(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2' dv1)(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2' dv1)(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2' dv1)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d2' \<lparr>cfg_conf = liftB \<alpha>v1 @ w @ v2\<rparr> \<pi>2 \<lparr>cfg_conf = liftB \<alpha>v1 @ v @ v2\<rparr>")
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' d2' dv1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' dv1 da)(*strict*)
  apply(rename_tac d2')
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' dv1 d2')(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' dv1 d2')(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d1'"
      and ?d2.0="dt"
      and ?v1.0="\<alpha>v1"
      and ?v2.0="v@v2"
      and ?v4.0="[]"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' dv1 d2')(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' dv1 d2')(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' dv1 d2')(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' dv1 d2')(*strict*)
  apply(thin_tac "cfgLM.trans_der G d1' \<lparr>cfg_conf = liftB \<alpha>v1 @ w @ v2\<rparr> \<pi>1 \<lparr>cfg_conf = liftB \<alpha>v1 @ v @ v2\<rparr>")
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1' dv1 d2')(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' da)(*strict*)
  apply(rename_tac d1')
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' d1')(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' d1')(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d"
      and ?d2.0="dv1"
      and ?v1.0="[]"
      and ?v2.0="v1@w@v2"
      and ?v4.0="[]"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' d1')(*strict*)
     apply(force)
    apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' d1')(*strict*)
    apply(force)
   apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' d1')(*strict*)
   apply(force)
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' d1')(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf = v1 @ w @ v2\<rparr>")
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' d1')(*strict*)
  apply(thin_tac "cfgLM.trans_der G dv1 \<lparr>cfg_conf = v1 @ w @ v2\<rparr> \<pi>v1 \<lparr>cfg_conf = liftB \<alpha>v1 @ w @ v2\<rparr>")
  apply(rename_tac d \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t dv1 d2' d1')(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d1' d)(*strict*)
  apply(rename_tac d)
  apply(thin_tac "cfgLM.trans_der G dt \<lparr>cfg_conf = v @ v2\<rparr> \<pi>t \<lparr>cfg_conf = liftB \<alpha>t\<rparr>")
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d1' d)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d1' d)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d"
      and ?d2.0="d1'"
      and ?v1.0="[]"
      and ?v2.0="liftB \<alpha>v1 @ w @ v2"
      and ?v4.0="[]"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d1' d)(*strict*)
     apply(force)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d1' d)(*strict*)
    apply(force)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d1' d)(*strict*)
   apply(force)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d1' d)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d1' \<lparr>cfg_conf = liftB \<alpha>v1 @ w @ v2\<rparr> (\<pi>1 @ \<pi>t) \<lparr>cfg_conf = liftB \<alpha>v1 @ liftB \<alpha>t\<rparr>")
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v dt \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d1' d)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d da)(*strict*)
  apply(rename_tac d1)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d d1)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d d1)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d"
      and ?d2.0="d2'"
      and ?v1.0="[]"
      and ?v2.0="liftB \<alpha>v1 @ w @ v2"
      and ?v4.0="[]"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d d1)(*strict*)
     apply(force)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d d1)(*strict*)
    apply(force)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d d1)(*strict*)
   apply(force)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d d1)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d2' \<lparr>cfg_conf = liftB \<alpha>v1 @ w @ v2\<rparr> (\<pi>2 @ \<pi>t) \<lparr>cfg_conf = liftB \<alpha>v1 @ liftB \<alpha>t\<rparr>")
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2' d d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d d1 da)(*strict*)
  apply(rename_tac d2)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d d1 d2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> (\<pi> @ \<pi>v1) \<lparr>cfg_conf = liftB \<alpha>v1 @ w @ v2\<rparr>")
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d d1 d2)(*strict*)
  apply(simp add: CFGlm_unambiguous_def)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(erule impE)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2 e ea)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule impE)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2 e ea)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2)(*strict*)
  apply(erule_tac
      x="length ((\<pi> @ \<pi>v1 @ \<pi>1 @ \<pi>t))"
      in allE)
  apply(erule_tac
      x="length ((\<pi> @ \<pi>v1 @ \<pi>2 @ \<pi>t))"
      in allE)
  apply(clarsimp)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2 e ea)(*strict*)
  apply(erule impE)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2 e ea)(*strict*)
   apply(rule_tac
      x="\<alpha>v1@\<alpha>t"
      in exI)
   apply(simp add: simpY)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d1 d2 e ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d2 e ea)(*strict*)
  apply(rename_tac d e1 e2)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
  apply(subgoal_tac "map Some \<pi> @ map Some \<pi>v1 @ map Some \<pi>1 @ map Some \<pi>t = map Some \<pi> @ map Some \<pi>v1 @ map Some \<pi>2 @ map Some \<pi>t")
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(force)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
  apply(subgoal_tac "(length \<pi> + (length \<pi>v1 + (length \<pi>1 + length \<pi>t))) = (length \<pi> + (length \<pi>v1 + (length \<pi>2 + length \<pi>t)))")
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(rule_tac
      t="map Some \<pi> @ map Some \<pi>v1 @ map Some \<pi>1 @ map Some \<pi>t"
      and s="get_labels d (length \<pi> + (length \<pi>v1 + (length \<pi>1 + length \<pi>t)))"
      in subst)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
    apply(blast)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(rule_tac
      t="map Some \<pi> @ map Some \<pi>v1 @ map Some \<pi>2 @ map Some \<pi>t"
      and s="get_labels d (length \<pi> + (length \<pi>v1 + (length \<pi>2 + length \<pi>t)))"
      in subst)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
    apply(blast)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(rule_tac
      t="(length \<pi> + (length \<pi>v1 + (length \<pi>1 + length \<pi>t)))"
      and s="(length \<pi> + (length \<pi>v1 + (length \<pi>2 + length \<pi>t)))"
      in ssubst)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
    apply(force)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(force)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
  apply(case_tac "length \<pi>1 < length \<pi>2")
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d ((length \<pi> + (length \<pi>v1 + (length \<pi>1 + length \<pi>t)))) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
    prefer 2
    apply(rule_tac
      m="(length \<pi> + (length \<pi>v1 + (length \<pi>2 + length \<pi>t)))"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
      apply(force)
     apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
     apply(force)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
    apply(force)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2 e2a c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2 e2a c2 l r)(*strict*)
   apply(case_tac c2)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2 e2a c2 l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2 e2a l r)(*strict*)
   apply (metis List.set_simps(1) setA_liftB liftB_commutes_over_concat elemInsetA length_pos_if_in_set less_not_refl list.size(3))
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
  apply(case_tac "length \<pi>1 > length \<pi>2")
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d ((length \<pi> + (length \<pi>v1 + (length \<pi>2 + length \<pi>t)))) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
    prefer 2
    apply(rule_tac
      m="(length \<pi> + (length \<pi>v1 + (length \<pi>1 + length \<pi>t)))"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
      apply(force)
     apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
     apply(force)
    apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
    apply(force)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2 e2a c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2 e2a c2 l r)(*strict*)
   apply(case_tac c2)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2 e2a c2 l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2 e2a l r)(*strict*)
   apply (metis List.set_simps(1) setA_liftB liftB_commutes_over_concat elemInsetA length_pos_if_in_set less_not_refl list.size(3))
  apply(rename_tac \<pi> w v1 v2 \<pi>1 \<pi>2 v \<pi>v1 \<pi>t \<alpha>v1 \<alpha>t d e1 e2)(*strict*)
  apply(simp (no_asm_simp))
  done

lemma use_CFGprodXORelim: "
  CFGprodXORelim G
  \<Longrightarrow> A \<in> CFG_not_end_nterm G
  \<Longrightarrow> \<exists>d1 \<pi>1. cfgLM.trans_der G
                  d1 \<lparr>cfg_conf = [teA A]\<rparr> \<pi>1 \<lparr>cfg_conf = []\<rparr>
  \<Longrightarrow> \<exists>d2 \<pi>2 b w.
               cfgLM.trans_der G
                  d2 \<lparr>cfg_conf = [teA A]\<rparr> \<pi>2 \<lparr>cfg_conf = teB b # w\<rparr>
  \<Longrightarrow> False"
  apply(simp add: CFGprodXORelim_def)
  apply(force)
  done

lemma left_degen_preserves_leading_nonterminal: "
  split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d c1 \<pi> c2
  \<Longrightarrow> c1=\<lparr>cfg_conf=teA A#w\<rparr>
  \<Longrightarrow> left_degen G d
  \<Longrightarrow> \<exists>A w. c2=\<lparr>cfg_conf=teA A#w\<rparr>"
  apply(induct \<pi> arbitrary: c2 rule: rev_induct)
   apply(rename_tac c2)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac x xs c2)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac x xs c2 e)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs c2 e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs c2 e)(*strict*)
     apply(force)
    apply(rename_tac x xs c2 e)(*strict*)
    apply(force)
   apply(rename_tac x xs c2 e)(*strict*)
   apply(force)
  apply(rename_tac x xs c2 e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c2 e1 e2 c1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xs c2 e1 e2 c1 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs c2 e1 e2 c1 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c2 e1 e2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xs c2 e1 e2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 e2 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac x xs e1 e2 l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac C v)
  apply(rename_tac x xs e1 e2 l r C v)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 l r C v)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac x xs e1 l r C v)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac x xs e1 l r C v)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 r C v l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(simp add: left_degen_def sat_refined_def)
  apply(erule_tac
      x="length xs"
      in allE)
  apply(clarsimp)
  apply(rename_tac x xs e1 r C l' wa Aa waa)(*strict*)
  apply(case_tac l')
   apply(rename_tac x xs e1 r C l' wa Aa waa)(*strict*)
   prefer 2
   apply(rename_tac x xs e1 r C l' wa Aa waa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs e1 r C l' wa Aa waa)(*strict*)
  apply(clarsimp)
  done

lemma terminal_production_repetitions_in_parallel_derivation: "
  split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=teA B#v\<rparr> \<pi>1 \<lparr>cfg_conf=teB b#w1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=teA B#v\<rparr> \<pi>2 \<lparr>cfg_conf=teB b#w2\<rparr>
  \<Longrightarrow> \<pi>1@x=\<pi>2
  \<Longrightarrow> x\<noteq>[]
  \<Longrightarrow> \<forall>i<length \<pi>2. hd (cfg_conf (the (get_configuration (d2 i)))) \<noteq> teB b
  \<Longrightarrow> Q"
  apply(subgoal_tac "d1 (length \<pi>1) = d2 (length \<pi>1)")
   apply(clarsimp)
   apply(erule_tac
      x="length \<pi>1"
      in allE)
   apply(erule impE)
    apply(case_tac x)
     apply(force)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(subgoal_tac "hd (cfg_conf (the (get_configuration (d2 (length \<pi>1))))) = teB b")
    apply(force)
   apply(thin_tac "hd (cfg_conf (the (get_configuration (d2 (length \<pi>1))))) \<noteq> teB b")
   apply(simp (no_asm_use) add: cfgLM.trans_der_def)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac e ea)(*strict*)
   apply(rule_tac
      t="d2 (length \<pi>1)"
      and s="Some (pair e \<lparr>cfg_conf = teB b # w1\<rparr>)"
      in ssubst)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(simp (no_asm) add: get_configuration_def)
  apply(rule sym)
  apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="d2"
      and ?\<pi>2.0="x"
      in cfgLM_trans_der_coincide)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfgLMMIP_and_cfgLM_trans_der_append: "
  split_TSstructure G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=[]\<rparr>
  \<Longrightarrow> cfgLMMIP G d2 w2 \<pi>2 (liftB \<alpha>) v
  \<Longrightarrow> \<pi>2\<noteq>[]
  \<Longrightarrow> \<alpha>\<noteq>[]
  \<Longrightarrow> \<exists>d. cfgLMMIP G d (w1@w2) (\<pi>1@\<pi>2) (liftB \<alpha>) v"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(unfold cfgLMMIP_def)
   apply(erule conjE)+
   apply(fold cfgLMMIP_def)
   apply(rule_tac
      ?v1.0="[]"
      and ?d1.0="d1"
      and ?d2.0="d2"
      and G="G"
      in cfgLM_trans_der_biextend_prime)
     apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def cfg_configurations_def split_TSstructure_def valid_cfg_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(simp add: cfgLMMIP_def)
  apply(rule conjI)
   apply(rename_tac d)(*strict*)
   apply(simp add: cfgLMMIyX_def)
   apply(clarsimp)
   apply(rule_tac
      xs="w1@w2"
      in rev_cases)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac d)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
   apply(rename_tac d ys y)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      xs="w2"
      in rev_cases)
    apply(rename_tac d ys y)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
     apply(rename_tac d ys y)(*strict*)
     prefer 2
     apply(rule_tac cfgLM_trans_der_from_empty)
     apply(force)
    apply(rename_tac d ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac d ys y ysa ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac d y ysa)(*strict*)
   apply(rule_tac
      ?w1.0="w1"
      and G="G"
      and ?w2.0="[]"
      and ?w3.0="ysa"
      and ?\<pi>1.0="\<pi>1"
      and ?\<pi>2.0="\<pi>2"
      in applicable_contra2)
      apply(rename_tac d y ysa)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac d y ysa)(*strict*)
     apply(force)
    apply(rename_tac d y ysa)(*strict*)
    apply(force)
   apply(rename_tac d y ysa)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(simp add: cfgLMMPX_def)
  apply(clarsimp)
  apply(rename_tac d \<pi>' da c)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(erule exE)+
  apply(rename_tac d \<pi>' da c ca)(*strict*)
  apply(fold strict_prefix_def)
  apply(clarsimp)
  apply(subgoal_tac "strict_prefix \<pi>' \<pi>1 \<or> SSX" for SSX)
   apply(rename_tac d \<pi>' da c ca)(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(force)
  apply(rename_tac d \<pi>' da c ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac d \<pi>' da c ca)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac d \<pi>' da c cb)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d \<pi>' da c cb)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="d1"
      and i="length \<pi>'"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
      apply(rename_tac d \<pi>' da c cb)(*strict*)
      apply(simp add: split_TSstructure_def)
     apply(rename_tac d \<pi>' da c cb)(*strict*)
     apply(force)
    apply(rename_tac d \<pi>' da c cb)(*strict*)
    apply(force)
   apply(rename_tac d \<pi>' da c cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<pi>' da c cb e ci ci')(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac d \<pi>' da c cb e ci ci')(*strict*)
    prefer 2
    apply(rule_tac
      n="length \<pi>'"
      and d="d1"
      in cfgLM.trans_der_crop)
        apply(rename_tac d \<pi>' da c cb e ci ci')(*strict*)
        apply(simp add: split_TSstructure_def)
        apply(force)
       apply(rename_tac d \<pi>' da c cb e ci ci')(*strict*)
       apply(force)
      apply(rename_tac d \<pi>' da c cb e ci ci')(*strict*)
      apply(force)
     apply(rename_tac d \<pi>' da c cb e ci ci')(*strict*)
     apply(force)
    apply(rename_tac d \<pi>' da c cb e ci ci')(*strict*)
    apply(force)
   apply(rename_tac d \<pi>' da c cb e ci ci')(*strict*)
   apply(case_tac ci)
   apply(rename_tac d \<pi>' da c cb e ci ci' cfg_conf)(*strict*)
   apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
    apply(rename_tac d \<pi>' da c cb e ci ci' cfg_conf)(*strict*)
    prefer 2
    apply(rule_tac
      \<pi>="\<pi>'"
      and ?w2.0="w2"
      and ?d1.0="da"
      and ?d2.0="d1"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
      apply(rename_tac d \<pi>' da c cb e ci ci' cfg_conf)(*strict*)
      apply(simp add: split_TSstructure_def)
      apply(force)
     apply(rename_tac d \<pi>' da c cb e ci ci' cfg_conf)(*strict*)
     apply(force)
    apply(rename_tac d \<pi>' da c cb e ci ci' cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac d \<pi>' da c cb e ci ci' cfg_conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<pi>' da c cb e ci' cfg_conf)(*strict*)
   apply(rename_tac w)
   apply(rename_tac d \<pi>' da c cb e ci' w)(*strict*)
   apply(case_tac \<alpha>)
    apply(rename_tac d \<pi>' da c cb e ci' w)(*strict*)
    apply(clarsimp)
   apply(rename_tac d \<pi>' da c cb e ci' w a list)(*strict*)
   apply(clarsimp)
   apply(case_tac w)
    apply(rename_tac d \<pi>' da c cb e ci' w a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d \<pi>' da c cb e ci' a list)(*strict*)
    apply(case_tac cb)
     apply(rename_tac d \<pi>' da c cb e ci' a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac d \<pi>' da c cb e ci' a list aa lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac d \<pi>' da c e ci' a list aa lista)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
   apply(rename_tac d \<pi>' da c cb e ci' w a list aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<pi>' da c cb e ci' a list lista)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac d \<pi>' da c cb e ci' a list lista)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac d \<pi>' da c cb e ci' a list lista ea eb ec ed ee)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      d="d1"
      and i="length \<pi>'"
      and j="length cb"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac d \<pi>' da c cb e ci' a list lista ea eb ec ed ee)(*strict*)
         apply(simp add: split_TSstructure_def)
         apply(force)
        apply(rename_tac d \<pi>' da c cb e ci' a list lista ea eb ec ed ee)(*strict*)
        apply(force)
       apply(rename_tac d \<pi>' da c cb e ci' a list lista ea eb ec ed ee)(*strict*)
       apply(force)
      apply(rename_tac d \<pi>' da c cb e ci' a list lista ea eb ec ed ee)(*strict*)
      apply(force)
     apply(rename_tac d \<pi>' da c cb e ci' a list lista ea eb ec ed ee)(*strict*)
     apply(force)
    apply(rename_tac d \<pi>' da c cb e ci' a list lista ea eb ec ed ee)(*strict*)
    apply(force)
   apply(rename_tac d \<pi>' da c cb e ci' a list lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<pi>' da c cb e ci' a list lista w)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(subgoal_tac "(a#maxTermPrefix lista)@w = []")
    apply(rename_tac d \<pi>' da c cb e ci' a list lista w)(*strict*)
    apply(force)
   apply(rename_tac d \<pi>' da c cb e ci' a list lista w)(*strict*)
   apply(rule_tac
      t="a#maxTermPrefix lista"
      and s="maxTermPrefix (teB a # lista)"
      in subst)
    apply(rename_tac d \<pi>' da c cb e ci' a list lista w)(*strict*)
    apply (metis maxTermPrefix_pull_out)
   apply(rename_tac d \<pi>' da c cb e ci' a list lista w)(*strict*)
   apply(rule_tac
      t="maxTermPrefix (teB a # lista) @ w"
      and s="maxTermPrefix []"
      in ssubst)
    apply(rename_tac d \<pi>' da c cb e ci' a list lista w)(*strict*)
    apply(force)
   apply(rename_tac d \<pi>' da c cb e ci' a list lista w)(*strict*)
   apply (metis maxTermPrefix_empty)
  apply(rename_tac d \<pi>' da c ca)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac d da c ca cb)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(erule_tac
      x="cb"
      in allE)
  apply(erule impE)
   apply(rename_tac d da c ca cb)(*strict*)
   apply(force)
  apply(rename_tac d da c ca cb)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da c ca cb)(*strict*)
   prefer 2
   apply(rule_tac
      i="length \<pi>1"
      and d="da"
      in cfgLM.trans_der_position_detail)
     apply(rename_tac d da c ca cb)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac d da c ca cb)(*strict*)
    apply(force)
   apply(rename_tac d da c ca cb)(*strict*)
   apply(force)
  apply(rename_tac d da c ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da c ca cb e ci)(*strict*)
  apply(thin_tac "(\<exists>y. e = Some y) = (e = Some ((\<pi>1 @ cb) ! (length \<pi>1 - Suc 0)))")
  apply(thin_tac "(\<pi>1 = []) = (e = None)")
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da c ca cb e ci)(*strict*)
   prefer 2
   apply(rule_tac
      n="length \<pi>1"
      and d="da"
      in cfgLM.trans_der_crop)
       apply(rename_tac d da c ca cb e ci)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac d da c ca cb e ci)(*strict*)
      apply(force)
     apply(rename_tac d da c ca cb e ci)(*strict*)
     apply(force)
    apply(rename_tac d da c ca cb e ci)(*strict*)
    apply(force)
   apply(rename_tac d da c ca cb e ci)(*strict*)
   apply(force)
  apply(rename_tac d da c ca cb e ci)(*strict*)
  apply(case_tac ci)
  apply(rename_tac d da c ca cb e ci cfg_conf)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac d da c ca cb e ci cfg_conf)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>="\<pi>1"
      and ?w2.0="w2"
      and ?d1.0="da"
      and ?d2.0="d1"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac d da c ca cb e ci cfg_conf)(*strict*)
     apply(simp add: split_TSstructure_def)
     apply(force)
    apply(rename_tac d da c ca cb e ci cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac d da c ca cb e ci cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac d da c ca cb e ci cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac d da c ca cb e)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d da c ca cb e)(*strict*)
   prefer 2
   apply(rule_tac
      n="length \<pi>1"
      and d="da"
      in cfgLM.trans_der_skip_prime)
       apply(rename_tac d da c ca cb e)(*strict*)
       apply(simp add: split_TSstructure_def)
       apply(force)
      apply(rename_tac d da c ca cb e)(*strict*)
      apply(force)
     apply(rename_tac d da c ca cb e)(*strict*)
     apply(force)
    apply(rename_tac d da c ca cb e)(*strict*)
    apply(force)
   apply(rename_tac d da c ca cb e)(*strict*)
   apply(force)
  apply(rename_tac d da c ca cb e)(*strict*)
  apply(clarsimp)
  done

lemma LR1_terminal_only_at_front_in_prods: "
  split_TSstructure G
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = a # teB b # w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> Q"
  apply(simp add: split_TSstructure_def LR1ProdFormSimp_def)
  apply(clarsimp)
  apply(erule_tac ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  done

lemma LR1_at_most_two_symbols: "
  split_TSstructure G
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = a # b # w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> w=[]"
  apply(simp add: split_TSstructure_def LR1ProdFormSimp_def)
  apply(clarsimp)
  apply(erule_tac ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac ba Aa B)(*strict*)
  apply(erule disjE)
   apply(rename_tac ba Aa B)(*strict*)
   apply(force)
  apply(rename_tac ba Aa B)(*strict*)
  apply(clarsimp)
  done

(* important cfgLMMIP_and_cfgLM_trans_der_append *)
(* important CFGlm_unambiguous_implies_CFGdetEntire *)
(* important CFGlm_unambiguous_implies_CFG_no_self_loop *)
(* important CFGlm_unambiguous_implies_CFGuniqueElim *)
(* important drop_and_crop_empty *)
(* important enforceSuffixS_smaller *)
(* important equal_split_prefix_hlp1 *)
(* important Esplit_inst_AX_initial_configuration_belongs *)
(* important EValidSplit_interline_preserve *)
(* important F_DPDA_DRE__revert_F_SDPDA_TO_CFG_STD__SOUND_back_hlp_prime_prime *)
(* important fillOptL_cropTol3l2_last_back_state_if_l3_nonterminal *)
(* important left_degen_preserves_leading_nonterminal *)
(* important LR1_at_most_two_symbols *)
(* important LR1ProdFormSimp_implies_CFGtermLeft *)
(* important LR1_terminal_only_at_front_in_prods *)
(* important terminal_production_repetitions_in_parallel_derivation *)
(* important use_CFGprodXORelim *)

end

