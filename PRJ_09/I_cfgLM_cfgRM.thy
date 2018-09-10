section {*I\_cfgLM\_cfgRM*}
theory
  I_cfgLM_cfgRM

imports
  I_cfgLM_misc
  I_cfgRM

begin

lemma LR1_from_rm_deri_to_lm_deri_around_nonterminal_hlp: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=w1@[teA A]@w2'\<rparr>)
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> d2 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>)
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=liftB w1'\<rparr>)
  \<Longrightarrow> \<exists>d1' n1' e1' d2' n2' e2' w2.
  cfgLM.derivation_initial G d1'
  \<and> d1' n1' = Some (pair e1' \<lparr>cfg_conf=(liftB w1')@[teA A]@w2\<rparr>)
  \<and> cfgRM.derivation G d2'
  \<and> d2' 0 = Some (pair None \<lparr>cfg_conf=w2\<rparr>)
  \<and> d2' n2' = Some (pair e2' \<lparr>cfg_conf=w2'\<rparr>)"
  apply(induct n1 arbitrary: e1 w1 A w2' w1' w2 d2 n2 e2)
   apply(rename_tac e1 w1 A w2' w1' d2 n2 e2)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac w1 A w2' w1' d2 n2 e2)(*strict*)
   apply(case_tac w1)
    apply(rename_tac w1 A w2' w1' d2 n2 e2)(*strict*)
    prefer 2
    apply(rename_tac w1 A w2' w1' d2 n2 e2 a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac w1 A w2' w1' d2 n2 e2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1' d2 n2 e2)(*strict*)
   apply(subgoal_tac "w1'=[]")
    apply(rename_tac w1' d2 n2 e2)(*strict*)
    prefer 2
    apply(case_tac n2)
     apply(rename_tac w1' d2 n2 e2)(*strict*)
     apply(clarsimp)
     apply(rename_tac w1' d2)(*strict*)
     apply(case_tac w1')
      apply(rename_tac w1' d2)(*strict*)
      apply(force)
     apply(rename_tac w1' d2 a list)(*strict*)
     apply(force)
    apply(rename_tac w1' d2 n2 e2 nat)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 0 = Some (pair e1 c1) \<and> d2 (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
     apply(rename_tac w1' d2 n2 e2 nat)(*strict*)
     prefer 2
     apply(rule_tac
      m="n2"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac w1' d2 n2 e2 nat)(*strict*)
       apply(force)
      apply(rename_tac w1' d2 n2 e2 nat)(*strict*)
      apply(force)
     apply(rename_tac w1' d2 n2 e2 nat)(*strict*)
     apply(force)
    apply(rename_tac w1' d2 n2 e2 nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1' d2 e2 nat e2a c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
   apply(rename_tac w1' d2 n2 e2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d2 n2 e2)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac d2 n2 e2)(*strict*)
    apply(rule cfgLM.derivation_initialI)
     apply(rename_tac d2 n2 e2)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d2 n2 e2)(*strict*)
    apply(clarsimp)
    apply(rename_tac d2 n2 e2 c)(*strict*)
    apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def)
   apply(rename_tac d2 n2 e2)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(simp add: der1_def get_configuration_def cfg_initial_configurations_def)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf=[]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac d2 n2 e2)(*strict*)
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac d2 n2 e2)(*strict*)
   apply(rule conjI)
    apply(rename_tac d2 n2 e2)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac d2 n2 e2)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      x="None"
      in exI)
   apply(simp add: der1_def)
  apply(rename_tac n1 e1 w1 A w2' w1' d2 n2 e2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 n1 = Some (pair e1 c1) \<and> d1 (Suc n1) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac n1 e1 w1 A w2' w1' d2 n2 e2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n1"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac n1 e1 w1 A w2' w1' d2 n2 e2)(*strict*)
     apply(rule cfgRM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n1 e1 w1 A w2' w1' d2 n2 e2)(*strict*)
    apply(force)
   apply(rename_tac n1 e1 w1 A w2' w1' d2 n2 e2)(*strict*)
   apply(force)
  apply(rename_tac n1 e1 w1 A w2' w1' d2 n2 e2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a e2a c1)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a e2a c1 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a e2a c1 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a e2a l r)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a e2a l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac B w)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a e2a l r B w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l r B w)(*strict*)
  apply(subgoal_tac "\<exists>w'. liftB w'=r")
   apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l r B w)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB r"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l r B w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l B w w')(*strict*)
  apply(thin_tac "setA (liftB w') = {}")
  apply(subgoal_tac "strict_prefix w1 l \<or> prefix l w1")
   apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l B w w')(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(force)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l B w w')(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l B w w')(*strict*)
  apply(erule disjE)
   apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l B w w')(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a B w w' c)(*strict*)
   apply(case_tac c)
    apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a B w w' c)(*strict*)
    apply(clarsimp)
   apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a B w w' c a list)(*strict*)
   apply(rename_tac C v)
   apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a B w w' c C v)(*strict*)
   apply(clarsimp)
   apply(rename_tac n1 w1 A w1' d2 n2 e2 e1a B w w' v)(*strict*)
   apply(erule_tac
      x="w1"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="A"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="v @ teA B # liftB w'"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="w1'"
      in meta_allE)
   apply(erule_tac
      x="d2"
      in meta_allE)
   apply(erule_tac
      x="n2"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="e2"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac n1 w1 A w1' d2 n2 e2 e1a B w w' v d1' n1' e1' d2' n2' e2' w2)(*strict*)
   apply(rule_tac
      x="d1'"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n1'"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="derivation_append d2' (der2 \<lparr>cfg_conf = v @ teA B # liftB w'\<rparr> \<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<lparr>cfg_conf = v @ w @ liftB w'\<rparr>) n2'"
      in exI)
   apply(rule conjI)
    apply(rename_tac n1 w1 A w1' d2 n2 e2 e1a B w w' v d1' n1' e1' d2' n2' e2' w2)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation)
      apply(rename_tac n1 w1 A w1' d2 n2 e2 e1a B w w' v d1' n1' e1' d2' n2' e2' w2)(*strict*)
      apply(force)
     apply(rename_tac n1 w1 A w1' d2 n2 e2 e1a B w w' v d1' n1' e1' d2' n2' e2' w2)(*strict*)
     apply(rule cfgRM.der2_is_derivation)
     apply(simp add: cfgRM_step_relation_def)
     apply(rule_tac
      x="v"
      in exI)
     apply(clarsimp)
     apply (metis setA_liftB)
    apply(rename_tac n1 w1 A w1' d2 n2 e2 e1a B w w' v d1' n1' e1' d2' n2' e2' w2)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac n1 w1 A w1' d2 n2 e2 e1a B w w' v d1' n1' e1' d2' n2' e2' w2)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(rule_tac
      x="Suc n2'"
      in exI)
   apply(clarsimp)
  apply(rename_tac n1 w1 A w2' w1' d2 n2 e2 e1a l B w w')(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w w' c)(*strict*)
  apply(subgoal_tac "strict_prefix c w \<or> prefix w c")
   apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w w' c)(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(force)
  apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w w' c)(*strict*)
  apply(erule disjE)
   apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w w' c)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w w' ca)(*strict*)
   apply(subgoal_tac "setA [teA A] = {}")
    apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w w' ca)(*strict*)
    prefer 2
    apply(rule_tac setA_liftB_substring)
    apply(rule sym)
    apply(clarsimp)
    apply(force)
   apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w w' ca)(*strict*)
   apply(force)
  apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w w' c)(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w' c ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w' c ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac n1 A w2' w1' d2 n2 e2 e1a l B w' c ca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c list)(*strict*)
  apply(rename_tac y)
  apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
  apply(erule_tac
      x="l"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="B"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="liftB w'"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d1 d2 Xw1' Xw2' n1X n2X. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = l\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = Xw1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = c\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = Xw2'\<rparr>} \<and> Xw1'@Xw2'=liftB w1' \<and> maximum_of_domain d1 n1X \<and> maximum_of_domain d2 n2X \<and> n1X+n2X=n2")
   apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
   prefer 2
   apply(rule_tac
      d="derivation_take d2 n2"
      in CFGLM_derivationCanBeDecomposed2)
    apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(rule conjI)
     apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
     apply(rule cfgLM.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
    apply(rule conjI)
     apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
    apply(rule conjI)
     apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
     apply(rule cfgLM.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
    apply(simp add: derivation_take_def)
    apply(rule_tac
      x="n2"
      in exI)
    apply(clarsimp)
   apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac n1 A w1' d2 n2 e2 e1a l B w' c y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X)(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa)(*strict*)
  apply(case_tac "d1a 0")
   apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa)(*strict*)
  apply(case_tac "d2a 0")
   apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa)(*strict*)
  apply(erule_tac
      x="filterB Xw1'"
      in meta_allE)
  apply(erule_tac
      x="d1a"
      in meta_allE)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="xa"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa)(*strict*)
   apply(rule sym)
   apply(rule liftBDeConv2)
   apply (metis setA_Concat2 setA_liftB empty_subsetI subset_empty)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2)(*strict*)
  apply(subgoal_tac "\<exists>w'. liftB w'=Xw1'")
   apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB Xw1'"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_Concat2 setA_liftB empty_subsetI subset_empty)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw1' Xw2' n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw2' n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2 w'a)(*strict*)
  apply(subgoal_tac "\<exists>w'. liftB w'=Xw2'")
   apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw2' n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2 w'a)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB Xw2'"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_liftB setA_setmp_concat_2 empty_subsetI ex_in_conv)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a Xw2' n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2 w'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
  apply(subgoal_tac "w1'=w'a@w'b")
   apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
   prefer 2
   apply(rule liftB_inj)
   apply(rule sym)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac n1 A w1' d2 e2 e1a l B w' c y d1a d2a n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n1 A d2 e2 e1a l B w' c y d1a d2a n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
  apply(thin_tac "liftB w'a @ liftB w'b = liftB (w'a @ w'b)")
  apply(simp add: liftB_commutes_over_concat)
  apply(thin_tac "cfgRM.derivation_initial G d1")
  apply(thin_tac "d1 (Suc n1) = Some (pair (Some \<lparr>prod_lhs = B, prod_rhs = c @ teA A # y\<rparr>) \<lparr>cfg_conf = l @ c @ teA A # y @ liftB w'\<rparr>)")
  apply(thin_tac "cfgLM.derivation G d2")
  apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = l @ c\<rparr>)")
  apply(thin_tac "d2 (n1X + n2X) = Some (pair e2 \<lparr>cfg_conf = liftB w'a @ liftB w'b\<rparr>)")
  apply(thin_tac "d1 n1 = Some (pair e1a \<lparr>cfg_conf = l @ teA B # liftB w'\<rparr>)")
  apply(rename_tac n1 A d2 e2 e1a l B w' c y d1 d2a n1X n2X n na xa xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
  apply(thin_tac "maximum_of_domain d2a n2X")
  apply(thin_tac "d2a (Suc na) = None")
  apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = l\<rparr>)")
  apply(thin_tac "d1 (Suc n) = None")
  apply(thin_tac "d1 n = Some (pair xa \<lparr>cfg_conf = liftB w'a\<rparr>)")
  apply(thin_tac "maximum_of_domain d1 n1X")
  apply(clarsimp)
  apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
  apply(subgoal_tac "\<exists>d n e. cfgLM.derivation_initial G d \<and> d n = Some (pair e \<lparr>cfg_conf = liftB w'a @ c@teA A#y @ w2\<rparr>) ")
   apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_append d1' (der2 \<lparr>cfg_conf = liftB w'a @ teA B # w2\<rparr> \<lparr>prod_lhs = B, prod_rhs = c@teA A#y\<rparr> \<lparr>cfg_conf = liftB w'a @ c@teA A#y @ w2\<rparr>) n1'"
      in exI)
   apply(rule_tac
      x="Suc n1'"
      in exI)
   apply(rule_tac
      x="Some \<lparr>prod_lhs = B, prod_rhs = c@teA A#y\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
      apply(force)
     apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
     apply(force)
    apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="liftB w'a"
      in exI)
     apply(clarsimp)
     apply (metis setA_liftB)
    apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
  apply(thin_tac "\<lparr>prod_lhs = B, prod_rhs = c @ teA A # y\<rparr> \<in> cfg_productions G")
  apply(thin_tac "d1' n1' = Some (pair e1' \<lparr>cfg_conf = liftB w'a @ teA B # w2\<rparr>)")
  apply(thin_tac "cfgLM.derivation G d1")
  apply(thin_tac "cfgLM.derivation_initial G d1'")
  apply(rename_tac A B w' c y d1 d2a na xaa d1' n1' e1' d2' n2' e2' w2 w'a w'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
  apply(subgoal_tac "\<exists>d e. cfgLM.derivation G d \<and> d 0 = Some (pair None \<lparr>cfg_conf=(liftB w'a)@(cfg_conf \<lparr>cfg_conf = c\<rparr>)@(liftB [])@(cfg_conf \<lparr>cfg_conf=teA A # y @ w2\<rparr>)@[]\<rparr>) \<and> d (na+0) = Some (pair e \<lparr>cfg_conf=(liftB w'a)@(cfg_conf \<lparr>cfg_conf = liftB w'b\<rparr>)@(liftB [])@(cfg_conf \<lparr>cfg_conf=teA A # y @ w2\<rparr>)@[]\<rparr>)")
   apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d2a"
      and ?d2.0="der1 \<lparr>cfg_conf = teA A # y @ w2\<rparr>"
      in CFGLM_composition_of_two_derivation_with_context)
          apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
          apply(force)
         apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
         apply(force)
        apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
        apply(force)
       apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
       apply(force)
      apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
      apply(rule cfgLM.der1_is_derivation)
     apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
   apply(clarsimp)
   apply (metis setA_liftB)
  apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
  apply(thin_tac "cfgLM.derivation G d2a")
  apply(thin_tac "d2a na = Some (pair xaa \<lparr>cfg_conf = liftB w'b\<rparr>)")
  apply(thin_tac "d2a 0 = Some (pair None \<lparr>cfg_conf = c\<rparr>)")
  apply(rule_tac
      x="derivation_append d da n"
      in exI)
  apply(rule conjI)
   apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
     apply(force)
    apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
    apply(force)
   apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
    apply(force)
   apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
   apply(force)
  apply(rename_tac A w' c y d2a na xaa d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
  apply(rule_tac
      x="n+na"
      in exI)
  apply(rule_tac
      x="if na=0 then e else ea"
      in exI)
  apply(rule_tac
      x="derivation_map d2' (\<lambda>v. \<lparr>cfg_conf = y@(cfg_conf v)\<rparr>)"
      in exI)
  apply(rule_tac
      x="n2'"
      in exI)
  apply(rule_tac
      x="e2'"
      in exI)
  apply(rule_tac
      x="y @ w2"
      in exI)
  apply(rule conjI)
   apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
  apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
   apply(rule cfgRM.derivation_map_preserves_derivation2)
    apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
    apply(force)
   apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea a eb b)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea a eb b l r)(*strict*)
   apply(rule_tac
      x="y @ l"
      in exI)
   apply(clarsimp)
  apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac A w' c y na d2' n2' e2' w2 w'a w'b d n e da ea)(*strict*)
  apply(simp add: derivation_map_def)
  done

lemma LR1_from_rm_deri_to_lm_deri_around_nonterminal: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation_initial G d1
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=w1@[teA A]@(liftB w2')\<rparr>)
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> d2 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>)
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=liftB w1'\<rparr>)
  \<Longrightarrow> \<exists>d1' n1' e1' d2' n2' e2' w2.
  cfgLM.derivation_initial G d1'
  \<and> d1' n1' = Some (pair e1' \<lparr>cfg_conf=(liftB w1')@[teA A]@w2\<rparr>)
  \<and> cfgRM.derivation G d2'
  \<and> d2' 0 = Some (pair None \<lparr>cfg_conf=w2\<rparr>)
  \<and> d2' n2' = Some (pair e2' \<lparr>cfg_conf=liftB w2'\<rparr>)"
  apply(rule LR1_from_rm_deri_to_lm_deri_around_nonterminal_hlp)
       apply(force)+
  done

corollary cfg_dependency_between_Nonblockingnessness_properties1LM: "
  valid_cfg G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G
  \<Longrightarrow> nonblockingness_language (cfgLM.unmarked_language G) (cfgLM.marked_language G)"
  apply(simp add: nonblockingness_language_def)
  apply (metis nonblockingness_language_def cfgLM.AX_BF_Bra_OpLa)
  done

lemma lemma_4_10_combine: "
  valid_cfg G
  \<Longrightarrow> (\<And>y d e A w \<pi>. y < Suc (Suc n) \<Longrightarrow> cfgRM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> d y = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> \<pi> = map the (get_labels d y) \<Longrightarrow> \<exists>d'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<and> (\<exists>e'. d' y = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>)) \<and> map the (get_labels d y) = CFGlm2rm G (map the (get_labels d' y)))
  \<Longrightarrow> \<forall>i<length \<pi>s. \<exists>d' n' e'.
  cfgRM.derivation G d'
  \<and> cfgLM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf = map (\<lambda>x. [x]) (prod_rhs r) ! i\<rparr>)
  \<and> d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! i)\<rparr>)
  \<and> \<pi>s ! i = map the (get_labels d' n')
  \<Longrightarrow> k\<le>length \<pi>s
  \<Longrightarrow> length(prod_rhs r)=length \<pi>s
  \<Longrightarrow> length ws=length \<pi>s
  \<Longrightarrow> r \<in> cfg_productions G
  \<Longrightarrow> Suc n = length (foldl (@) [] \<pi>s)
  \<Longrightarrow> \<exists>d e \<pi>sX. cfgLM.derivation G d
  \<and> cfgLM.belongs G d
  \<and> d 0 = Some (pair None \<lparr>cfg_conf = take k (prod_rhs r)\<rparr>)
  \<and> d (length(foldl (@) [] (take k \<pi>s))) = Some (pair e \<lparr>cfg_conf = liftB (foldl (@) [] (take k ws))\<rparr>)
  \<and> length \<pi>sX = k
  \<and> map the (get_labels d (length(foldl (@) [] (take k \<pi>s)))) = foldl (@) [] \<pi>sX
  \<and> map (CFGlm2rm G) \<pi>sX = take k \<pi>s
  \<and> (\<forall>i<k.
  \<exists>d e.
  cfgLM.derivation G d
  \<and> cfgLM.belongs G d
  \<and> d 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r!i]\<rparr>)
  \<and> d (length(\<pi>sX!i)) = Some (pair e \<lparr>cfg_conf = liftB (ws!i)\<rparr>)
  \<and> \<pi>sX!i = map the (get_labels d (length(\<pi>sX!i)))
  )"
  apply(clarsimp)
  apply(induct k)
   apply(clarsimp)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rule cfgLM.der1_is_derivation)
   apply(rule conjI)
    apply(rule cfgLM.derivation_belongs)
       apply(force)
      apply(simp add: der1_def)
     apply(simp add: cfg_configurations_def)
    apply(rule cfgLM.der1_is_derivation)
   apply(simp add: der1_def)
   apply(simp add: get_labels_def)
   apply (metis nat_seqEmpty zero_less_Suc)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e \<pi>sX)(*strict*)
  apply(erule_tac
      x="(length \<pi>sX)"
      and P="\<lambda>y. y < length \<pi>s \<longrightarrow> (\<exists>d'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r ! y]\<rparr>) \<and> (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! y)\<rparr>)) \<and> \<pi>s ! y = map the (get_labels d' n')))"
      in allE)
  apply(rename_tac d e \<pi>sX)(*strict*)
  apply(erule impE)
   apply(rename_tac d e \<pi>sX)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e \<pi>sX d' n' e')(*strict*)
  apply(erule_tac
      x="n'"
      in meta_allE)
  apply(erule_tac
      x="d'"
      in meta_allE)
  apply(erule_tac
      x="e'"
      in meta_allE)
  apply(erule_tac
      x="prod_rhs r!(length \<pi>sX)"
      in meta_allE)
  apply(erule_tac
      x="ws!(length \<pi>sX)"
      in meta_allE)
  apply(erule_tac
      x="map the (get_labels d' n')"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac d e \<pi>sX d' n' e')(*strict*)
   apply(rule_tac
      t="n'"
      and s="length(map the (get_labels d' n'))"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' n' e')(*strict*)
    apply(simp add: get_labels_def)
    apply (metis list.size(3) nat_seqEmpty nat_seq_length_Suc0 neq0_conv zero_less_Suc)
   apply(rename_tac d e \<pi>sX d' n' e')(*strict*)
   apply(rule_tac
      t="map the (get_labels d' n')"
      and s="\<pi>s ! (length \<pi>sX)"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' n' e')(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' n' e')(*strict*)
   apply (metis le_imp_less_Suc length_shorter_than_in_composition less_eq_Suc_le_raw)
  apply(rename_tac d e \<pi>sX d' n' e')(*strict*)
  apply(erule exE)+
  apply(rename_tac d e \<pi>sX d' n' e' d'a)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(subgoal_tac "cfgLM.derivation_from_to SSG (derivation_append (derivation_map SSd1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ SSw2\<rparr>)) (derivation_map SSd2 (\<lambda>v. \<lparr>cfg_conf = SSw1' @ cfg_conf v\<rparr>)) SSm1) {pair None \<lparr>cfg_conf = SSw1 @ SSw2\<rparr>} ({ y. (\<exists>xa. y = pair xa \<lparr>cfg_conf = SSw1' @ SSw2'\<rparr>)})" for SSG SSd1 SSd2 SSm1 SSw1 SSw2 SSw1' SSw2')
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   prefer 2
   apply(rule_tac
      ?d2.0="derivation_take d'a n'"
      and ?d1.0="derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))"
      and ?w1.0="take (length \<pi>sX) (prod_rhs r)"
      and ?w1'="liftB(foldl (@) [] (take (length \<pi>sX) ws))"
      and ?w2.0="[(prod_rhs r)!(length \<pi>sX)]"
      and ?w2'="liftB(ws!(length \<pi>sX))"
      in cfgLM_concatExtendIsFromToBoth)
        apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
        apply(force)
       apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
       apply(simp add: cfgLM.derivation_from_to_def)
       apply(simp add: cfgLM.derivation_from_def)
       apply(simp add: cfgLM.derivation_to_def)
       apply(rule context_conjI)
        apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
        apply(rule cfgLM.derivation_take_preserves_derivation)
        apply(force)
       apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
       apply(clarsimp)
       apply(simp add: derivation_take_def)
       apply(rule_tac
      x="length (foldl (@) [] (take (length \<pi>sX) \<pi>s))"
      in exI)
       apply(clarsimp)
      apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
      apply(simp add: cfgLM.derivation_from_to_def)
      apply(simp add: cfgLM.derivation_from_def)
      apply(simp add: cfgLM.derivation_to_def)
      apply(rule context_conjI)
       apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
       apply(rule cfgLM.derivation_take_preserves_derivation)
       apply(force)
      apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
      apply(clarsimp)
      apply(simp add: derivation_take_def)
      apply(rule_tac
      x="n'"
      in exI)
      apply(clarsimp)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_map (derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! (length \<pi>sX)]\<rparr>)) (derivation_map (derivation_take d'a n') (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))"
      in exI)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(simp add: cfgLM.derivation_from_to_def)
   apply(simp add: cfgLM.derivation_from_def)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(subgoal_tac "take (length \<pi>sX) (prod_rhs r) @ [(prod_rhs r) ! (length \<pi>sX)] = take (Suc (length \<pi>sX)) (prod_rhs r)")
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   prefer 2
   apply(subgoal_tac "(length \<pi>sX)<length (prod_rhs r)")
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply (metis take_Suc_conv_app_nth)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
      apply(force)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = (prod_rhs r)\<rparr> \<in> cfg_configurations G")
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(rule conjI)
      apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
      apply(rule_tac
      B="setA (prod_rhs r)"
      in subset_trans)
       apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
       apply (metis setATake)
      apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
      apply(force)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(rule_tac
      B="setB (prod_rhs r)"
      in subset_trans)
      apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
      apply (metis setBTakeIndexSubset2)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="r"
      in ballE)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(simp add: cfgLM.derivation_from_to_def)
   apply(simp add: cfgLM.derivation_from_def)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(case_tac "n'")
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e \<pi>sX d' d'a)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a nat)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(subgoal_tac "length (foldl (@) [] (take (Suc (length \<pi>sX)) \<pi>s)) = length (foldl (@) [] (take ((length \<pi>sX)) \<pi>s)) + (length (\<pi>s!(length \<pi>sX)))")
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   prefer 2
   apply(rule_tac
      t="take (Suc (length \<pi>sX)) \<pi>s"
      and s="take (length \<pi>sX) \<pi>s @ [\<pi>s!(length \<pi>sX)]"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(rule sym)
    apply(subgoal_tac "(length \<pi>sX)<length \<pi>s")
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(rule sym)
     apply (rule take_Suc_conv_app_nth)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(rule_tac
      t="foldl (@) [] (take (length \<pi>sX) \<pi>s @ [\<pi>s ! (length \<pi>sX)])"
      and s=" (foldl (@) [] (take (length \<pi>sX) \<pi>s)) @(foldl (@) [] ([\<pi>s ! (length \<pi>sX)]))"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(rule foldl_distrib_append)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(subgoal_tac "n' = (length (\<pi>s ! (length \<pi>sX)))")
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   prefer 2
   apply(rule_tac
      t="\<pi>s ! (length \<pi>sX)"
      and s="CFGlm2rm G (map the (get_labels d'a n'))"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(rule_tac
      t="CFGlm2rm G (map the (get_labels d'a n'))"
      and s="map the (get_labels d' n')"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(simp (no_asm) add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) n') = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(rule_tac
      x="if (length (\<pi>s!(length \<pi>sX)))=0 then e else e'a"
      in exI)
   apply(case_tac "(length (\<pi>s!(length \<pi>sX)))")
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e \<pi>sX d' d'a)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
    apply(rule_tac
      t="foldl (@) [] (take (Suc (length \<pi>sX)) ws)"
      and s="foldl (@) [] (take (length \<pi>sX) ws) @ (ws!(length \<pi>sX))"
      in ssubst)
     apply(rename_tac d e \<pi>sX d' d'a)(*strict*)
     apply(rule sym)
     apply(rule foldl_tail)
     apply(force)
    apply(rename_tac d e \<pi>sX d' d'a)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a nat)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rule_tac
      t="foldl (@) [] (take (Suc (length \<pi>sX)) ws)"
      and s="foldl (@) [] (take (length \<pi>sX) ws) @ (ws!(length \<pi>sX))"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a nat)(*strict*)
    apply(rule sym)
    apply(rule foldl_tail)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a nat)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(rule_tac
      x="\<pi>sX@[(map the (get_labels d'a n'))]"
      in exI)
  apply(rule conjI)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(rule_tac
      t="take (Suc (length \<pi>sX)) \<pi>s"
      and s="take (length \<pi>sX) \<pi>s @ [\<pi>s!(length \<pi>sX)]"
      in ssubst)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(rule sym)
     apply(subgoal_tac "(length \<pi>sX)<length \<pi>s")
      apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
      apply(rule sym)
      apply (rule take_Suc_conv_app_nth)
      apply(force)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(rule_tac
      t="map (CFGlm2rm G) (\<pi>sX @ [map the (get_labels d'a n')])"
      and s=" (map (CFGlm2rm G) (\<pi>sX)) @(map (CFGlm2rm G) ([map the (get_labels d'a n')])) "
      in ssubst)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(rule_tac
      t="map (CFGlm2rm G) \<pi>sX"
      and s="take (length \<pi>sX) \<pi>s"
      in ssubst)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(rule_tac
      t="map (CFGlm2rm G) [map the (get_labels d'a n')]"
      and s="[\<pi>s ! length \<pi>sX]"
      in ssubst)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(rule_tac allI)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
   apply(rule_tac impI)
   apply(case_tac "i=length \<pi>sX")
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
    apply(rule_tac
      x="d'a"
      in exI)
    apply(rule conjI)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
    apply(rule conjI)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
    apply(rule conjI)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
    apply(rule_tac
      t="(\<pi>sX @ [map the (get_labels d'a n')]) ! i"
      and s="map the (get_labels d'a n')"
      in ssubst)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
    apply(rule_tac
      t="length (map the (get_labels d'a n'))"
      and s="n'"
      in ssubst)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
     apply(simp add: get_labels_def)
     apply(subgoal_tac "length (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX))) = SSm + 1 - SSn" for SSm SSn)
      apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
    apply(rule conjI)
     apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i da ea)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="(\<pi>sX @ [map the (get_labels d'a (length (\<pi>s ! length \<pi>sX)))]) ! i"
      and s="\<pi>sX!i"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i da ea)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i da ea)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(subgoal_tac "length (map the (get_labels (derivation_append (derivation_map (derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a n') (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (length (foldl (@) [] (take (Suc (length \<pi>sX)) \<pi>s))))) = length (foldl (@) [] \<pi>sX) + n'")
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   prefer 2
   apply(simp add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) ((length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX)))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="foldl (@) [] \<pi>sX"
      and s="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s))))"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) ((length (foldl (@) [] (take (length \<pi>sX) \<pi>s))))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
   apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))))"
      and s="length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + 1 - Suc 0"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
    apply (metis One_nat_def length_map nat_seq_length_prime)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
  apply(rule listEqI)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(rule_tac
      t="length (map the (get_labels (derivation_append (derivation_map (derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a n') (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (length (foldl (@) [] (take (Suc (length \<pi>sX)) \<pi>s)))))"
      and s="length (foldl (@) [] \<pi>sX) + n'"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(thin_tac "length (map the (get_labels (derivation_append (derivation_map (derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a n') (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (length (foldl (@) [] (take (Suc (length \<pi>sX)) \<pi>s))))) = length (foldl (@) [] \<pi>sX) + n'")
   apply(rename_tac d e \<pi>sX d' n' e' d'a e'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' n' e' d'a e'a i)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(thin_tac "length (get_labels (derivation_append (derivation_map (derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a (length (\<pi>s ! length \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX))) = length (foldl (@) [] \<pi>sX) + length (\<pi>s ! length \<pi>sX)")
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX))) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(subgoal_tac "length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) = length (foldl (@) [] \<pi>sX)")
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(thin_tac "valid_cfg G")
   apply(thin_tac "Suc (length \<pi>sX) \<le> length \<pi>s")
   apply(thin_tac "length (prod_rhs r) = length \<pi>s")
   apply(thin_tac "length ws = length \<pi>s")
   apply(thin_tac "r \<in> cfg_productions G")
   apply(thin_tac "Suc n = length (foldl (@) [] \<pi>s)")
   apply(thin_tac "cfgLM.derivation G d")
   apply(thin_tac "cfgLM.belongs G d")
   apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = take (length \<pi>sX) (prod_rhs r)\<rparr>)")
   apply(thin_tac "d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s))) = Some (pair e \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws))\<rparr>)")
   apply(thin_tac "map (CFGlm2rm G) \<pi>sX = take (length \<pi>sX) \<pi>s")
   apply(thin_tac "\<forall>i<length \<pi>sX. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r ! i]\<rparr>) \<and> (\<exists>e. d (length (\<pi>sX ! i)) = Some (pair e \<lparr>cfg_conf = liftB (ws ! i)\<rparr>)) \<and> \<pi>sX ! i = map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (length (\<pi>sX ! i)))")
   apply(thin_tac "cfgRM.derivation G d'")
   apply(thin_tac "cfgLM.belongs G d'")
   apply(thin_tac "d' 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r ! length \<pi>sX]\<rparr>)")
   apply(thin_tac "\<pi>s ! length \<pi>sX = CFGlm2rm G (map (the \<circ> (\<lambda>i. get_label (d'a i))) (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX))))")
   apply(thin_tac "d' (length (\<pi>s ! length \<pi>sX)) = Some (pair e' \<lparr>cfg_conf = liftB (ws ! length \<pi>sX)\<rparr>)")
   apply(thin_tac "cfgLM.derivation G d'a")
   apply(thin_tac "cfgLM.belongs G d'a")
   apply(thin_tac "d'a 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r ! length \<pi>sX]\<rparr>)")
   apply(thin_tac "map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX))) = \<pi>s ! length \<pi>sX")
   apply(thin_tac "d'a (length (\<pi>s ! length \<pi>sX)) = Some (pair e'a \<lparr>cfg_conf = liftB (ws ! length \<pi>sX)\<rparr>)")
   apply(thin_tac "cfgLM.derivation_from_to G (derivation_append (derivation_map (derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a (length (\<pi>s ! length \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) {pair None \<lparr>cfg_conf = take (Suc (length \<pi>sX)) (prod_rhs r)\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ liftB (ws ! length \<pi>sX)\<rparr>}")
   apply(thin_tac "take (length \<pi>sX) (prod_rhs r) @ [prod_rhs r ! length \<pi>sX] = take (Suc (length \<pi>sX)) (prod_rhs r)")
   apply(thin_tac "length (foldl (@) [] (take (Suc (length \<pi>sX)) \<pi>s)) = length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX)")
   apply(thin_tac "i < length (foldl (@) [] \<pi>sX) + length (\<pi>s ! length \<pi>sX)")
   apply(thin_tac "length (nat_seq (Suc 0) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX))) = length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX)")
   apply (metis Suc_eq_plus1 diff_add_inverse2 length_map nat_seq_length_prime plus_nat.add_0)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(rule_tac
      t="map (\<lambda>i. get_label (derivation_append (derivation_map (derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a (length (\<pi>s ! length \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s))) i)) (nat_seq (Suc 0) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX))) ! i"
      and s="(\<lambda>i. get_label (derivation_append (derivation_map (derivation_take d (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a (length (\<pi>s ! length \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s))) i)) ((nat_seq (Suc 0) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX))) ! i)"
      in ssubst)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(rule nth_map)
   apply(force)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (length (foldl (@) [] (take (length \<pi>sX) \<pi>s)) + length (\<pi>s ! length \<pi>sX)) ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) (length (foldl (@) [] \<pi>sX))) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(case_tac "i<length (foldl (@) [] \<pi>sX)")
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(rule_tac
      t="(foldl (@) [] \<pi>sX @ map (\<lambda>a. the (get_label (d'a a))) (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX)))) ! i"
      and s="(foldl (@) [] \<pi>sX) ! i"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(rule_tac
      t="derivation_append (derivation_map (derivation_take d (length (foldl (@) [] \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a (length (\<pi>s ! length \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] \<pi>sX)) (Suc i)"
      and s=" (derivation_map (derivation_take d (length (foldl (@) [] \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (Suc i)"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
    apply(simp add: derivation_append_def)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(rule_tac
      t="foldl (@) [] \<pi>sX"
      and s="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (length (foldl (@) [] \<pi>sX)))"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (length (foldl (@) [] \<pi>sX))) ! i"
      and s=" (the \<circ> (\<lambda>i. get_label (d i))) ((nat_seq (Suc 0) (length (foldl (@) [] \<pi>sX))) ! i)"
      in ssubst)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(case_tac "length (foldl (@) [] \<pi>sX)")
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) (length (foldl (@) [] \<pi>sX)) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
     apply(force)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def derivation_append_def derivation_map_def derivation_take_def)
   apply(case_tac "d (Suc i)")
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(rule_tac
      t="(foldl (@) [] \<pi>sX @ map (\<lambda>a. the (get_label (d'a a))) (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX)))) ! i"
      and s=" (map (\<lambda>a. the (get_label (d'a a))) (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX)))) ! (i - length(foldl (@) [] \<pi>sX)) "
      in ssubst)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
  apply(clarsimp)
  apply(case_tac "length (foldl (@) [] \<pi>sX)")
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<pi>sX d' e' d'a e'a i)(*strict*)
   apply(simp add: get_label_def derivation_append_def derivation_map_def derivation_take_def)
   apply(case_tac "d'a (Suc i)")
    apply(rename_tac d \<pi>sX d' e' d'a e'a i)(*strict*)
    apply(clarsimp)
   apply(rename_tac d \<pi>sX d' e' d'a e'a i a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d \<pi>sX d' e' d'a e'a i a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) ((length (\<pi>s ! length \<pi>sX)))) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
  apply(rule_tac
      t="map (\<lambda>a. the (get_label (d'a a))) (nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX))) ! (i - length (foldl (@) [] \<pi>sX))"
      and s="(\<lambda>a. the (get_label (d'a a))) ((nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX))) ! (i - length (foldl (@) [] \<pi>sX)))"
      in ssubst)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   apply(rule nth_map)
   apply(force)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
  apply(rule_tac
      t="derivation_append (derivation_map (derivation_take d (length (foldl (@) [] \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [prod_rhs r ! length \<pi>sX]\<rparr>)) (derivation_map (derivation_take d'a (length (\<pi>s ! length \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (length (foldl (@) [] \<pi>sX)) (Suc i)"
      and s=" (derivation_map (derivation_take d'a (length (\<pi>s ! length \<pi>sX))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take (length \<pi>sX) ws)) @ cfg_conf v\<rparr>)) (Suc i - ((length (foldl (@) [] \<pi>sX))))"
      in ssubst)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
  apply(simp add: get_label_def derivation_append_def derivation_map_def derivation_take_def)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) (length (\<pi>s ! length \<pi>sX)) ! (i - Suc nat) = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
    apply(force)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="Suc (i - Suc nat)"
      and s="i-nat"
      in ssubst)
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   apply(force)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
  apply(case_tac "d'a (i-nat)")
   apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d e \<pi>sX d' e' d'a e'a i nat a option b)(*strict*)
  apply(clarsimp)
  done

lemma lemma_4_7_uniqueness_hlp2: "
  valid_cfg G
  \<Longrightarrow> i < length x1
  \<Longrightarrow> length x2 = length x1
  \<Longrightarrow> length y2 = length x1
  \<Longrightarrow> length y1 = length x1
  \<Longrightarrow> \<forall>i<length x1.
            \<exists>d'. cfgRM.derivation G d' \<and>
                 cfgLM.belongs G d' \<and>
                 d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
                 (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y1 ! i)\<rparr>)) \<and>
                       x1 ! i = map the (get_labels d' n'))
  \<Longrightarrow> \<forall>i<length x1.
            \<exists>d'. cfgRM.derivation G d' \<and>
                 cfgLM.belongs G d' \<and>
                 d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
                 (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y2 ! i)\<rparr>)) \<and>
                       x2 ! i = map the (get_labels d' n'))
  \<Longrightarrow> (x1 ! i) \<sqsubseteq> (x2 ! i)
  \<Longrightarrow> x1 ! i = x2 ! i \<and> y1 ! i = y2 ! i"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(erule_tac
      x="i"
      in allE)+
  apply(clarsimp)
  apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n') = SSn + 1 - SSi" for SSn SSi)
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n'a) = SSn + 1 - SSi" for SSn SSi)
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
  apply(subgoal_tac "n'+length c=n'a")
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="n'"
      and s="length(map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) n'))"
      in ssubst)
    apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
    apply (metis length_map)
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   apply(rule_tac
      t="n'a"
      and s="length(map (the \<circ> (\<lambda>i. get_label (d'a i))) (nat_seq (Suc 0) n'a))"
      in ssubst)
    apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
    apply (metis length_map)
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   apply (metis length_append)
  apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
  apply(subgoal_tac "d' n' = d'a n'")
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   prefer 2
   apply(rule_tac
      n="n'"
      and ?m1.0="0"
      and ?m2.0="length c"
      in equal_labels_implies_equal_cfgRMderivation)
          apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
          apply(force)
         apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
         apply(force)
        apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
        apply(force)
       apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
       apply(force)
      apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
      apply(force)
     apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
     apply(force)
    apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
    apply(rule_tac
      t="n'+length c"
      and s="n'a"
      in ssubst)
     apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
     apply(force)
    apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   apply(force)
  apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   apply(case_tac c)
    apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac c d' d'a n' n'a e' e'a a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' d'a n' e' e'a a list)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d'a n' = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac d' d'a n' e' e'a a list)(*strict*)
    prefer 2
    apply(rule_tac
      m="(Suc (n' + length list))"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac d' d'a n' e' e'a a list)(*strict*)
      apply(force)
     apply(rename_tac d' d'a n' e' e'a a list)(*strict*)
     apply(force)
    apply(rename_tac d' d'a n' e' e'a a list)(*strict*)
    apply(force)
   apply(rename_tac d' d'a n' e' e'a a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' d'a n' e' e'a a list e2 c2)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
    apply(force)
   apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
   apply(subgoal_tac "prod_lhs e2 \<in> setA (liftB (y1!i))")
    apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
    apply(subgoal_tac "setA (liftB (y1!i))={}")
     apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
     apply(force)
    apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
   apply(rule_tac
      t="liftB(y1!i)"
      and s="l @ teA (prod_lhs e2) # r"
      in ssubst)
    apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
    apply(force)
   apply(rename_tac d' d'a n' e' e'a a list e2 c2 l r)(*strict*)
   apply(simp add: setAConcat)
  apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
  apply(subgoal_tac "n'=n'a")
   apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
   prefer 2
   apply(simp add: get_labels_def)
  apply(rename_tac c d' d'a n' n'a e' e'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' d'a n'a e'a)(*strict*)
  apply(subgoal_tac "d' n'a = d'a n'a")
   apply(rename_tac d' d'a n'a e'a)(*strict*)
   apply(clarsimp)
   apply(rule liftB_inj)
   apply(force)
  apply(rename_tac d' d'a n'a e'a)(*strict*)
  apply(rule_tac
      n="n'a"
      and ?m1.0="0"
      and ?m2.0="0"
      in equal_labels_implies_equal_cfgRMderivation)
         apply(rename_tac d' d'a n'a e'a)(*strict*)
         apply(force)
        apply(rename_tac d' d'a n'a e'a)(*strict*)
        apply(force)
       apply(rename_tac d' d'a n'a e'a)(*strict*)
       apply(force)
      apply(rename_tac d' d'a n'a e'a)(*strict*)
      apply(force)
     apply(rename_tac d' d'a n'a e'a)(*strict*)
     apply(force)
    apply(rename_tac d' d'a n'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d' d'a n'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d' d'a n'a e'a)(*strict*)
  apply(force)
  done

lemma lemma_4_7_uniqueness_hlp1: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi> = map the (get_labels d n)
  \<Longrightarrow> foldl (@) [] (rev x1) = \<pi> \<and>
        length x1 = length \<alpha> \<and>
        foldl (@) [] y1 = w \<and>
        length y1 = length \<alpha> \<and>
        (\<forall>i<length x1.
            \<exists>d' n' e'.
               cfgRM.derivation G d' \<and>
               cfgLM.belongs G d' \<and>
               d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
               d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y1 ! i)\<rparr>) \<and>
               x1 ! i = map the (get_labels d' n'))
  \<Longrightarrow> foldl (@) [] (rev x2) = \<pi> \<and>
        length x2 = length \<alpha> \<and>
        foldl (@) [] y2 = w \<and>
        length y2 = length \<alpha> \<and>
        (\<forall>i<length x2.
            \<exists>d' n' e'.
               cfgRM.derivation G d' \<and>
               cfgLM.belongs G d' \<and>
               d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
               d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y2 ! i)\<rparr>) \<and>
               x2 ! i = map the (get_labels d' n'))
  \<Longrightarrow> i < length \<alpha>
  \<Longrightarrow> x1 ! i = x2 ! i \<and> y1 ! i = y2 ! i"
  apply(induct "length \<alpha> - Suc i" arbitrary: i rule: less_induct)
  apply(rename_tac i)(*strict*)
  apply(clarify)
  apply(simp)
  apply(subgoal_tac "foldl (@) [] (take (length x1 - Suc i) (rev x1)) = foldl (@) [] (take (length x1 - Suc i) (rev x2))")
   apply(rename_tac i)(*strict*)
   apply(thin_tac "\<And>ia. length \<alpha> - Suc ia < length \<alpha> - Suc i \<Longrightarrow> ia < length \<alpha> \<Longrightarrow> x1 ! ia = x2 ! ia \<and> y1 ! ia = y2 ! ia")
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "prefix (x1!i) (x2!i) \<or> prefix (x2!i) (x1!i)")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule_tac
      t="x1 ! i"
      and s="(rev x1)!(length x1 - (Suc i))"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(rule nth_rev)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="x2 ! i"
      and s="(rev x2)!(length x2 - (Suc i))"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(rule nth_rev)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      b="foldl (@) [] (drop (Suc (length x1 - Suc i)) (rev x1))"
      and d="foldl (@) [] (drop (Suc (length x1 - Suc i)) (rev x2))"
      in mutual_prefix_prefix)
    apply(rule_tac
      w="foldl (@) [] (take (length x1 - Suc i) (rev x1))"
      and v="foldl (@) [] (take (length x2 - Suc i) (rev x2))"
      in append_injective2)
     apply(rename_tac i)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(thin_tac "foldl (@) [] (take (length x1 - Suc i) (rev x1)) = foldl (@) [] (take (length x1 - Suc i) (rev x2))")
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="foldl (@) [] (take (length x1 - Suc i) (rev x1)) @ rev x1 ! (length x1 - Suc i) @ foldl (@) [] (drop (Suc (length x1 - Suc i)) (rev x1))"
      and s="foldl (@) [] (rev x1)"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply (metis diff_Suc_less diff_self_eq_0 epdaS.AX_join_scheduler_fragments_foldl_split foldl_drop_head less_imp_diff_less mutual_prefix_from_reversed_continuation_hlp)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="length x1"
      and s="length x2"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="foldl (@) [] (take (length x2 - Suc i) (rev x2)) @ rev x2 ! (length x2 - Suc i) @ foldl (@) [] (drop (Suc (length x2 - Suc i)) (rev x2))"
      and s="foldl (@) [] (rev x2)"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply (metis diff_Suc_less diff_self_eq_0 epdaS.AX_join_scheduler_fragments_foldl_split foldl_drop_head less_imp_diff_less mutual_prefix_from_reversed_continuation_hlp)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(thin_tac "foldl (@) [] (take (length x1 - Suc i) (rev x1)) = foldl (@) [] (take (length x1 - Suc i) (rev x2))")
   apply(rename_tac i)(*strict*)
   apply(thin_tac "foldl (@) [] (rev x1) = map the (get_labels d n)")
   apply(thin_tac "foldl (@) [] (rev x2) = map the (get_labels d n)")
   apply(thin_tac "cfgRM.derivation G d")
   apply(thin_tac "cfgLM.belongs G d")
   apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)")
   apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = liftB (foldl (@) [] y1)\<rparr>)")
   apply(thin_tac "foldl (@) [] y2 = foldl (@) [] y1")
   apply(erule disjE)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      \<alpha>="\<alpha>"
      in lemma_4_7_uniqueness_hlp2)
           apply(rename_tac i)(*strict*)
           apply(force)
          apply(rename_tac i)(*strict*)
          apply(force)
         apply(rename_tac i)(*strict*)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(rule_tac
      t="length x1"
      and s="length \<alpha>"
      in ssubst)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "x2 ! i = x1 ! i \<and> y2 ! i = y1 ! i")
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      \<alpha>="\<alpha>"
      in lemma_4_7_uniqueness_hlp2)
          apply(rename_tac i)(*strict*)
          apply(force)
         apply(rename_tac i)(*strict*)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(rule_tac
      t="length x1"
      and s="length \<alpha>"
      in ssubst)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(thin_tac "\<forall>i<length \<alpha>. \<exists>d'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and> (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y1 ! i)\<rparr>)) \<and> x1 ! i = map the (get_labels d' n'))")
  apply(rename_tac i)(*strict*)
  apply(thin_tac "\<forall>i<length \<alpha>. \<exists>d'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and> (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y2 ! i)\<rparr>)) \<and> x2 ! i = map the (get_labels d' n'))")
  apply(rename_tac i)(*strict*)
  apply(rule lemma_4_7_uniqueness_hlp3)
    apply(rename_tac i ia)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma lemma_4_7_uniqueness: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi> = map the (get_labels d n)
  \<Longrightarrow> foldl (@) [] (rev x1) = \<pi> \<and>
        length x1 = length \<alpha> \<and>
        foldl (@) [] y1 = w \<and>
        length y1 = length \<alpha> \<and>
        (\<forall>i<length x1.
            \<exists>d' n' e'.
               cfgRM.derivation G d' \<and>
               cfgLM.belongs G d' \<and>
               d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
               d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y1 ! i)\<rparr>) \<and>
               x1 ! i = map the (get_labels d' n'))
  \<Longrightarrow> foldl (@) [] (rev x2) = \<pi> \<and>
        length x2 = length \<alpha> \<and>
        foldl (@) [] y2 = w \<and>
        length y2 = length \<alpha> \<and>
        (\<forall>i<length x2.
            \<exists>d' n' e'.
               cfgRM.derivation G d' \<and>
               cfgLM.belongs G d' \<and>
               d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
               d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y2 ! i)\<rparr>) \<and>
               x2 ! i = map the (get_labels d' n'))
  \<Longrightarrow> x1 = x2 \<and> y1 = y2"
  apply(clarsimp)
  apply(subgoal_tac "\<forall>i<(length \<alpha>). x1!i = x2!i \<and> y1!i=y2!i")
   apply(rule conjI)
    apply(rule listEqI)
     apply(erule_tac
      x="i"
      in allE)+
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rule listEqI)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rule allI)
  apply(rename_tac i)(*strict*)
  apply(rule impI)
  apply(rule_tac
      d="d"
      and n="n"
      in lemma_4_7_uniqueness_hlp1)
          apply(rename_tac i)(*strict*)
          apply(force)+
  done

lemma lemma_4_7: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> \<exists>!\<pi>s. \<exists>!ws.
  foldl (@) [] (rev \<pi>s) = \<pi>
  \<and> length \<pi>s = length \<alpha>
  \<and> foldl (@) [] ws = w
  \<and> length ws = length \<alpha>
  \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'.
  cfgRM.derivation G d'
  \<and> cfgRM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=\<alpha>!i\<rparr>)
  \<and> d' n' = Some (pair e' \<lparr>cfg_conf=liftB (ws!i)\<rparr>)
  \<and> \<pi>s!i = map the (get_labels d' n'))"
  apply(rule ex_ex1I_double)
   apply(rule lemma_4_7_existence)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac x1 y1 x2 y2)(*strict*)
  apply(rule lemma_4_7_uniqueness)
         apply(rename_tac x1 y1 x2 y2)(*strict*)
         apply(force)+
  done

lemma lemma_4_9_hlp: "
  (\<And>y d e A w \<pi>. y < Suc (Suc n) \<Longrightarrow> cfgLM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> d y = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> \<pi> = map the (get_labels d y) \<Longrightarrow> \<exists>d'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<and> (\<exists>e'. d' y = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>)) \<and> CFGlm2rm G (map the (get_labels d y)) = map the (get_labels d' y))
  \<Longrightarrow> valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)
  \<Longrightarrow> d (Suc (Suc n)) = Some (pair e \<lparr>cfg_conf = liftB (foldl (@) [] ws)\<rparr>)
  \<Longrightarrow> d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>) \<lparr>cfg_conf = v\<rparr>)
  \<Longrightarrow> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G
  \<Longrightarrow> nat_seq (Suc 0) (Suc (Suc n)) = Suc 0 # nat_seq (Suc (Suc 0)) (Suc (Suc n))
  \<Longrightarrow> foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))
  \<Longrightarrow> length \<pi>s = length ws
  \<Longrightarrow> length v = length ws
  \<Longrightarrow> \<forall>k<length ws. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (v ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>)) \<and> \<pi>s ! k = map the (get_labels d n))
  \<Longrightarrow> k \<le> length ws
  \<Longrightarrow> let m = foldl (+) 0 (map length (take k \<pi>s)) in \<exists>d'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = take k v\<rparr>) \<and> (\<exists>e'. d' m = Some (pair e' \<lparr>cfg_conf = liftB (foldl (@) [] (take k ws))\<rparr>)) \<and> foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s))) = map the (get_labels d' m)"
  apply(induct k)
   apply(clarsimp)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rule cfgRM.der1_is_derivation)
   apply(rule conjI)
    apply(rule cfgRM.der1_belongs)
    apply(simp add: cfg_configurations_def)
   apply(rule conjI)
    apply(simp add: der1_def)
   apply(rule conjI)
    apply(simp add: der1_def)
   apply(simp add: get_labels_def)
   apply (metis nat_seqEmpty zero_less_Suc)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(simp add: Let_def)
  apply(erule_tac
      x="k"
      in allE)
  apply(erule impE)
   apply(rename_tac k)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k d' da na e' ea)(*strict*)
  apply(simp add: option_to_list_def)
  apply(erule_tac
      x="na"
      in meta_allE)
  apply(erule_tac
      x="da"
      in meta_allE)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="v!k"
      in meta_allE)
  apply(erule_tac
      x="ws!k"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="map the (get_labels da na)"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac k d' da na e' ea)(*strict*)
   apply(rule_tac
      t="na"
      and s="length(\<pi>s!k)"
      in ssubst)
    apply(rename_tac k d' da na e' ea)(*strict*)
    apply(clarsimp)
    apply(simp add: get_labels_def)
    apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac k d' da na e' ea)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac k d' da na e' ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac k d' da na e' ea)(*strict*)
   apply(rule_tac
      t="Suc n"
      and s="length(foldl (@) [] \<pi>s)"
      in ssubst)
    apply(rename_tac k d' da na e' ea)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc(Suc n))) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac k d' da na e' ea)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac k d' da na e' ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac k d' da na e' ea)(*strict*)
   apply(subgoal_tac "length (\<pi>s ! k) \<le> (length (foldl (@) [] \<pi>s))")
    apply(rename_tac k d' da na e' ea)(*strict*)
    apply(force)
   apply(rename_tac k d' da na e' ea)(*strict*)
   apply(rule length_shorter_than_in_composition)
   apply(force)
  apply(rename_tac k d' da na e' ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(subgoal_tac "cfgRM.derivation_from_to SSG (derivation_append (derivation_map SSd2 (\<lambda>v. \<lparr>cfg_conf = SSw1 @ cfg_conf v\<rparr>)) (derivation_map SSd1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ SSw2'\<rparr>)) SSm2) {pair None \<lparr>cfg_conf = SSw1 @ SSw2\<rparr>} ({ y. (\<exists>xa. y = pair xa \<lparr>cfg_conf = SSw1' @ SSw2'\<rparr>)})" for SSG SSd2 SSd1 SSm2 SSw1 SSw2 SSw1' SSw2')
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   prefer 2
   apply(rule_tac
      ?d2.0="derivation_take d'a na"
      and ?d1.0="derivation_take d' (foldl (+) 0 (map length (take k \<pi>s)))"
      and ?w1.0="take k v"
      and w1'="liftB (foldl (@) [] (take k ws))"
      and w2'="liftB (ws ! k)"
      and ?w2.0="[v ! k]"
      in cfgRM_concatExtendIsFromToBoth)
        apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
        apply(force)
       apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
       apply(simp add: cfgRM.derivation_from_to_def)
       apply(simp add: cfgRM.derivation_from_def)
       apply(simp add: cfgRM.derivation_to_def)
       apply(rule context_conjI)
        apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
        apply(rule cfgRM.derivation_take_preserves_derivation)
        apply(force)
       apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
       apply(clarsimp)
       apply(simp add: derivation_take_def)
       apply(rule_tac
      x="foldl (+) 0 (map length (take k \<pi>s))"
      in exI)
       apply(clarsimp)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(simp add: cfgRM.derivation_from_to_def)
      apply(simp add: cfgRM.derivation_from_def)
      apply(simp add: cfgRM.derivation_to_def)
      apply(rule context_conjI)
       apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
       apply(rule cfgRM.derivation_take_preserves_derivation)
       apply(force)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(clarsimp)
      apply(simp add: derivation_take_def)
      apply(rule_tac
      x="na"
      in exI)
      apply(clarsimp)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_map (derivation_take d'a na) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>)) (derivation_map (derivation_take d' (foldl (+) 0 (map length (take k \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws ! k)\<rparr>)) na"
      in exI)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule conjI)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(simp add: cfgRM.derivation_from_to_def)
   apply(simp add: cfgRM.derivation_from_def)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(subgoal_tac "take k v @ [v ! k] = take (Suc k) v")
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   prefer 2
   apply(subgoal_tac "k<length v")
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply (metis take_Suc_conv_app_nth)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(rule cfgRM.derivation_belongs)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(force)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = v\<rparr> \<in> cfg_configurations G")
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(rule conjI)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(rule_tac
      B="setA v"
      in subset_trans)
       apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
       apply (metis setATake)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(force)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(rule_tac
      B="setB v"
      in subset_trans)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply (metis setBTakeIndexSubset2)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(rule_tac
      d="d"
      and i="Suc 0"
      in cfgLM.belongs_configurations)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(simp add: cfgRM.derivation_from_to_def)
   apply(simp add: cfgRM.derivation_from_def)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule conjI)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(case_tac "na")
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(clarsimp)
    apply(rename_tac k d' da e' d'a)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
   apply(rule_tac
      t="derivation_append (derivation_map (derivation_take d'a na) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>)) (derivation_map (derivation_take d' (foldl (+) 0 (map length (take k \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws ! k)\<rparr>)) na 0"
      and s=" (derivation_map (derivation_take d'a na) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>)) 0 "
      in ssubst)
    apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
   apply(rule_tac
      t="derivation_map (derivation_take d'a na) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>) 0"
      and s="derivation_map (d'a) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>) 0"
      in ssubst)
    apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule conjI)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(rule_tac
      x="if (foldl (+) 0 (map length (take k \<pi>s)))=0 then e'a else e'"
      in exI)
   apply(case_tac "(foldl (+) 0 (map length (take k \<pi>s)))")
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(clarsimp)
    apply(rename_tac k d' da na ea d'a e'a)(*strict*)
    apply(subgoal_tac "(foldl (+) 0 (map length (take (Suc k) \<pi>s)))=na")
     apply(rename_tac k d' da na ea d'a e'a)(*strict*)
     apply(clarsimp)
     apply(rename_tac k d' da ea d'a e'a)(*strict*)
     apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
     apply(rule_tac
      t="foldl (@) [] (take (Suc k) ws)"
      and s="foldl (@) [] (take k ws) @ (ws!k)"
      in ssubst)
      apply(rename_tac k d' da ea d'a e'a)(*strict*)
      apply(rule sym)
      apply(rule foldl_tail)
      apply(force)
     apply(rename_tac k d' da ea d'a e'a)(*strict*)
     apply(simp add: liftB_commutes_over_concat)
    apply(rename_tac k d' da na ea d'a e'a)(*strict*)
    apply(rule_tac
      t="take (Suc k) \<pi>s"
      and s="take k \<pi>s @ [\<pi>s!k]"
      in ssubst)
     apply(rename_tac k d' da na ea d'a e'a)(*strict*)
     apply(rule sym)
     apply(subgoal_tac "k<length \<pi>s")
      apply(rename_tac k d' da na ea d'a e'a)(*strict*)
      apply (metis take_Suc_conv_app_nth)
     apply(rename_tac k d' da na ea d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac k d' da na ea d'a e'a)(*strict*)
    apply(rule_tac
      t="foldl (+) 0 (map length (take k \<pi>s @ [\<pi>s ! k]))"
      and s=" (foldl (+) 0 (map length (take k \<pi>s))) +(length(\<pi>s!k)) "
      in ssubst)
     apply(rename_tac k d' da na ea d'a e'a)(*strict*)
     prefer 2
     apply(rule_tac
      t="foldl (+) 0 (map length (take k \<pi>s))"
      and s="0"
      in ssubst)
      apply(rename_tac k d' da na ea d'a e'a)(*strict*)
      prefer 2
      apply(clarsimp)
      apply(simp add: get_labels_def)
      apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSm + 1 - SSn" for SSm SSn)
       apply(rename_tac k d' da na ea d'a e'a)(*strict*)
       prefer 2
       apply(rule nat_seq_length_prime)
      apply(rename_tac k d' da na ea d'a e'a)(*strict*)
      apply(clarsimp)
     apply(rename_tac k d' da na ea d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac k d' da na ea d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rule_tac
      t="take (Suc k) \<pi>s"
      and s="take k \<pi>s @ [\<pi>s!k]"
      in ssubst)
    apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
    apply(rule sym)
    apply (rule take_nth_split)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
   apply(rule_tac
      t="foldl (+) 0 (map length (take k \<pi>s @ [\<pi>s ! k]))"
      and s=" (foldl (+) 0 (map length (take k \<pi>s))) +(length(\<pi>s!k)) "
      in ssubst)
    apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
   apply(rule_tac
      t="length (\<pi>s ! k)"
      and s="na"
      in ssubst)
    apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
    apply(clarsimp)
    apply(simp add: get_labels_def)
    apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="take (Suc k) ws"
      and s="take k ws @ [ws!k]"
      in ssubst)
    apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
    apply(rule sym)
    apply (rule take_nth_split)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a nat)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="take (Suc k) \<pi>s"
      and s="take k \<pi>s @ [\<pi>s!k]"
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(rule sym)
   apply (rule take_nth_split)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="foldl (+) 0 (map length (take k \<pi>s @ [\<pi>s ! k]))"
      and s=" (foldl (+) 0 (map length (take k \<pi>s))) +(length(\<pi>s!k)) "
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="length (\<pi>s ! k)"
      and s="na"
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="foldl (+) 0 (map length (take k \<pi>s)) + na"
      and s="na+foldl (+) 0 (map length (take k \<pi>s))"
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append (derivation_map (derivation_take d'a na) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>)) (derivation_map (derivation_take d' (foldl (+) 0 (map length (take k \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws ! k)\<rparr>)) na) (na + foldl (+) 0 (map length (take k \<pi>s)))"
      and s="(get_labels (derivation_map (derivation_take d'a na) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>)) na) @(get_labels (derivation_map (derivation_take d' (foldl (+) 0 (map length (take k \<pi>s)))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws ! k)\<rparr>)) (foldl (+) 0 (map length (take k \<pi>s)))) "
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(rule cfgRM.get_labels_derivation_append)
       apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
       apply(force)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(rule cfgRM.derivation_map_preserves_derivation2)
       apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
       apply(rule cfgRM.derivation_take_preserves_derivation)
       apply(force)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(clarsimp)
      apply(rename_tac k d' da na e' ea d'a e'a a eaa b)(*strict*)
      apply(simp add: cfgRM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac k d' da na e' ea d'a e'a a eaa b l r)(*strict*)
      apply(rule_tac
      x="take k v @ l"
      in exI)
      apply(clarsimp)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(rule cfgRM.derivation_map_preserves_derivation2)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(rule cfgRM.derivation_take_preserves_derivation)
      apply(force)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(clarsimp)
     apply(rename_tac k d' da na e' ea d'a e'a a eaa b)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac k d' da na e' ea d'a e'a a eaa b l r)(*strict*)
     apply(rule_tac
      x="l"
      in exI)
     apply(clarsimp)
     apply(simp add: setAConcat)
     apply(rule setA_liftB)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(simp add: derivation_map_def derivation_take_def)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(simp add: derivation_map_def derivation_take_def)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="rev (take k \<pi>s @ [\<pi>s ! k])"
      and s="[\<pi>s ! k] @ (rev (take k \<pi>s))"
      in subst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply (metis ConsApp insert_Nil kPrefix_def rev.simps(2) rev_swap rotate_simps)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="map (CFGlm2rm G) ([\<pi>s ! k] @ rev (take k \<pi>s))"
      and s=" (map (CFGlm2rm G) ([\<pi>s ! k])) @(map (CFGlm2rm G) (rev (take k \<pi>s))) "
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="map (CFGlm2rm G) [\<pi>s ! k]"
      and s="[(CFGlm2rm G) (\<pi>s ! k)]"
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="foldl (@) [] ([CFGlm2rm G (\<pi>s ! k)] @ map (CFGlm2rm G) (rev (take k \<pi>s)))"
      and s=" CFGlm2rm G (\<pi>s ! k) @ (foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s)))) "
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply (metis (erased, hide_lams) append.simps(1) append.simps(2) foldl_drop_head)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule_tac
      t="CFGlm2rm G (\<pi>s ! k)"
      and s="map the (get_labels (derivation_map (derivation_take d'a na) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>)) na)"
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(rule_tac
      t="get_labels (derivation_map (derivation_take d'a na) (\<lambda>va. \<lparr>cfg_conf = take k v @ cfg_conf va\<rparr>)) na"
      and s="get_labels (derivation_take d'a na) na"
      in ssubst)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(simp add: get_labels_def)
    apply(clarsimp)
    apply(rename_tac k d' da na e' ea d'a e'a x)(*strict*)
    apply(simp add: derivation_map_def derivation_take_def get_label_def)
    apply(clarsimp)
    apply(case_tac "d'a x")
     apply(rename_tac k d' da na e' ea d'a e'a x)(*strict*)
     apply(clarsimp)
    apply(rename_tac k d' da na e' ea d'a e'a x a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac k d' da na e' ea d'a e'a x a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(rule_tac
      t="get_labels (derivation_take d'a na) na"
      and s="get_labels d'a na"
      in subst)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(rule cfgRM.get_labels_derivation_take)
      apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
      apply(force)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      f="\<lambda>x. map the x"
      in HOL.arg_cong)
  apply(rule_tac
      t="get_labels d' (foldl (+) 0 (map length (take k \<pi>s)))"
      and s="get_labels (derivation_take d' (foldl (+) 0 (map length (take k \<pi>s)))) (foldl (+) 0 (map length (take k \<pi>s)))"
      in ssubst)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(rule cfgRM.get_labels_derivation_take)
     apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac k d' da na e' ea d'a e'a)(*strict*)
  apply(rule sym)
  apply(rule get_labels_derivation_map)
  done

lemma lemma_4_10: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> (\<exists>d' e'. cfgLM.derivation G d'
  \<and> cfgLM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>)
  \<and> d' n = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>)
  \<and> \<pi>=CFGlm2rm G (map the (get_labels d' n)))"
  apply(induct n arbitrary: d e A w \<pi> rule: less_induct)
  apply(rename_tac x d e A w \<pi>)(*strict*)
  apply(case_tac x)
   apply(rename_tac x d e A w \<pi>)(*strict*)
   apply(thin_tac "\<And>y d e A w \<pi>. y < x \<Longrightarrow> valid_cfg G \<Longrightarrow> cfgRM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> d y = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> \<pi> = map the (get_labels d y) \<Longrightarrow> \<exists>d' e'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<and> d' y = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>) \<and> \<pi> = CFGlm2rm G (map the (get_labels d' y))")
   apply(rename_tac x d e A w \<pi>)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A w)(*strict*)
   apply(case_tac w)
    apply(rename_tac d A w)(*strict*)
    apply(force)
   apply(rename_tac d A w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac d a list)(*strict*)
    prefer 2
    apply(rename_tac d a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac d a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d a)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teB a]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac d a)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac d a)(*strict*)
   apply(rule conjI)
    apply(rename_tac d a)(*strict*)
    apply(rule cfgLM.der1_belongs)
    apply (metis cfgLM.belongs_configurations)
   apply(rename_tac d a)(*strict*)
   apply(rule conjI)
    apply(rename_tac d a)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac d a)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "nat_seq (Suc 0) 0=[]")
    apply(rename_tac d a)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac d a)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d a)(*strict*)
    apply(rule sym)
    apply(rule CFGlm2rm.psimps)
    apply(rule CFGlm2rm.domintros)
   apply(rename_tac d a)(*strict*)
   apply (metis nat_seqEmpty zero_less_Suc)
  apply(rename_tac x d e A w \<pi> nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e A w nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d e A w n)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac d e A w n)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac d e A w n)(*strict*)
     apply(force)
    apply(rename_tac d e A w n)(*strict*)
    apply(force)
   apply(rename_tac d e A w n)(*strict*)
   apply(force)
  apply(rename_tac d e A w n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e A w n e2 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d e A w n e2 c2 l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac d e A w n e2 c2 l r)(*strict*)
   prefer 2
   apply(rename_tac d e A w n e2 c2 l r a list)(*strict*)
   apply(force)
  apply(rename_tac d e A w n e2 c2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w n e2 c2)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d e w n e2 c2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w n e2)(*strict*)
  apply(rename_tac r)
  apply(rename_tac d e w n r)(*strict*)
  apply(rule_tac
      t="(map the (get_labels d (Suc n)))"
      and s="(map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc n)))"
      in ssubst)
   apply(rename_tac d e w n r)(*strict*)
   apply(simp add: get_labels_def)
  apply(rename_tac d e w n r)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = Suc 0 # nat_seq (Suc (Suc 0)) ((Suc n))")
   apply(rename_tac d e w n r)(*strict*)
   prefer 2
   apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
  apply(rename_tac d e w n r)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="(the (get_label (Some (pair (Some r) \<lparr>cfg_conf = prod_rhs r\<rparr>))))"
      and s="r"
      in ssubst)
   apply(rename_tac d e w n r)(*strict*)
   apply(simp add: get_label_def)
  apply(rename_tac d e w n r)(*strict*)
  apply(case_tac n)
   apply(rename_tac d e w n r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w r)(*strict*)
   apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (prod_lhs r)]\<rparr> r \<lparr>cfg_conf = prod_rhs r\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac d w r)(*strict*)
    apply(rule cfgLM.der2_is_derivation)
    apply(simp add: cfgLM_step_relation_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac d w r)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac d w r)(*strict*)
    apply(rule cfgLM.derivation_belongs)
       apply(rename_tac d w r)(*strict*)
       apply(force)
      apply(rename_tac d w r)(*strict*)
      apply(simp add: der2_def)
     apply(rename_tac d w r)(*strict*)
     apply(rule cfgLM.belongs_configurations)
      apply(rename_tac d w r)(*strict*)
      apply(force)
     apply(rename_tac d w r)(*strict*)
     apply(force)
    apply(rename_tac d w r)(*strict*)
    apply(force)
   apply(rename_tac d w r)(*strict*)
   apply(simp add: der2_def)
   apply(subgoal_tac "nat_seq (Suc (Suc 0)) (Suc 0) = []")
    apply(rename_tac d w r)(*strict*)
    prefer 2
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac d w r)(*strict*)
   apply(clarsimp)
   apply(simp add: get_labels_def)
   apply(simp add: get_label_def)
   apply(rule_tac
      t="CFGlm2rm SSG (SSr # SSpiPrime)"
      and s="(let \<pi>s = SOME \<pi>s. foldl (@) [] \<pi>s = renPIprime \<and> length \<pi>s = length (prod_rhs SSr) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators SSG (Some (prod_rhs SSr ! i))) in SSr # foldl (@) [] (map (CFGlm2rm SSG) (rev \<pi>s)))" for SSG SSr SSpiPrime renPIprime
      in ssubst)
    apply(rename_tac d w r)(*strict*)
    apply(rule CFGlm2rm.psimps)
    apply(rule_tac
      d="(\<lambda>n. if n = 0 then Some (pair None \<lparr>cfg_conf = [teA (prod_lhs r)]\<rparr>) else if n = Suc 0 then Some (pair (Some r) \<lparr>cfg_conf = liftB w\<rparr>) else None)"
      in CFGlm2rm_terminates)
          apply(rename_tac d w r)(*strict*)
          apply(force)
         apply(rename_tac d w r)(*strict*)
         apply(force)
        apply(rename_tac d w r)(*strict*)
        apply(force)
       apply(rename_tac d w r)(*strict*)
       apply(force)
      apply(rename_tac d w r)(*strict*)
      apply(force)
     apply(rename_tac d w r)(*strict*)
     apply(force)
    apply(rename_tac d w r)(*strict*)
    apply(simp add: get_labels_def)
    apply(simp add: get_label_def)
   apply(rename_tac d w r)(*strict*)
   apply(simp add: Let_def)
   apply(rule sym)
   apply(rule foldl_empty)
   apply(rename_tac d w r a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w r x)(*strict*)
   apply(case_tac "x")
    apply(rename_tac d w r x)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w r)(*strict*)
    apply(rule CFGlm2rm.psimps)
    apply(rule CFGlm2rm.domintros)
   apply(rename_tac d w r x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w r a list)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d w r a list)(*strict*)
    apply(force)
   apply(rename_tac d w r a list)(*strict*)
   apply(thin_tac "\<And>y d e A w \<pi>. y = 0 \<Longrightarrow> cfgRM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> None = e \<and> [A] = liftB w \<Longrightarrow> \<pi> = map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i))) (nat_seq (Suc 0) 0) \<Longrightarrow> \<exists>d'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = liftB w\<rparr>) \<and> (\<exists>e'. d' 0 = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>)) \<and> map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i))) (nat_seq (Suc 0) 0) = CFGlm2rm G (map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d' i))) (nat_seq (Suc 0) 0))")
   apply(rename_tac d w r a list)(*strict*)
   apply(subgoal_tac "\<exists>\<pi>s. (\<pi>s= (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (liftB w ! i))))) \<and> foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (liftB w ! i)))")
    apply(rename_tac d w r a list)(*strict*)
    prefer 2
    apply(rule_tac
      x="map (\<lambda>x. []) w"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac d w r a list)(*strict*)
     apply(rule sym)
     apply(rule_tac
      a="map (\<lambda>x. []) w"
      in someI2)
      apply(rename_tac d w r a list)(*strict*)
      apply(clarsimp)
      apply(rule conjI)
       apply(rename_tac d w r a list)(*strict*)
       apply(rule foldl_empty)
       apply(rename_tac d w r a list aa)(*strict*)
       apply(clarsimp)
      apply(rename_tac d w r a list)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w r a list)(*strict*)
       apply (simp add: liftB_reflects_length)
      apply(rename_tac d w r a list)(*strict*)
      apply(clarsimp)
      apply(rename_tac d w r a list i)(*strict*)
      apply(simp add: CFGlmEliminators_def)
      apply(thin_tac "a # list \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (liftB w ! i))\<rparr>) \<and> (\<exists>n. (\<exists>e w. d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)) \<and> \<pi>s ! i = map the (get_labels d n))))")
      apply(rename_tac d w r a list i)(*strict*)
      apply(rule_tac
      x="der1 \<lparr>cfg_conf = option_to_list (Some (liftB w ! i))\<rparr>"
      in exI)
      apply(rule conjI)
       apply(rename_tac d w r a list i)(*strict*)
       apply(rule cfgLM.der1_is_derivation)
      apply(rename_tac d w r a list i)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w r a list i)(*strict*)
       apply(rule cfgLM.der1_belongs)
       apply(simp add: option_to_list_def)
       apply(rename_tac d w r i)(*strict*)
       apply(rule hlp3)
        apply(rename_tac d w r i)(*strict*)
        apply(rule cfgLM.belongs_configurations)
         apply(rename_tac d w r i)(*strict*)
         apply(force)
        apply(rename_tac d w r i)(*strict*)
        apply(force)
       apply (simp add: liftB_length)
      apply(rename_tac d w r a list i)(*strict*)
      apply(simp add: der1_def)
      apply(rename_tac d w r i)(*strict*)
      apply(simp add: option_to_list_def)
      apply(rule conjI)
       apply(rename_tac d w r i)(*strict*)
       apply(rule_tac
      x="[w!i]"
      in exI)
       apply(rule distrib_nth_liftB)
       apply (simp add: liftB_length)
      apply(rename_tac d w r i)(*strict*)
      apply(simp add: get_labels_def)
      apply (metis nat_seqEmpty zero_less_Suc)
     apply(rename_tac d w r a list x)(*strict*)
     apply(clarsimp)
     apply(rule listEqI)
      apply(rename_tac d w r a list x)(*strict*)
      apply(clarsimp)
      apply (simp add: liftB_length)
     apply(rename_tac d w r a list x i)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="map (\<lambda>x. []) w ! i"
      and s="(\<lambda>x. []) (w ! i)"
      in ssubst)
      apply(rename_tac d w r a list x i)(*strict*)
      apply(rule nth_map)
      apply (simp add: liftB_length)
     apply(rename_tac d w r a list x i)(*strict*)
     apply(rule foldl_empty2)
      apply(rename_tac d w r a list x i)(*strict*)
      apply(force)
     apply(rename_tac d w r a list x i)(*strict*)
     apply(force)
    apply(rename_tac d w r a list)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w r a list)(*strict*)
     apply(rule foldl_empty)
     apply(rename_tac d w r a list aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w r a list)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w r a list)(*strict*)
     apply (simp add: liftB_length)
    apply(rename_tac d w r a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w r a list i)(*strict*)
    apply(simp add: CFGlmEliminators_def)
    apply(thin_tac "a # list \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (liftB w ! i))\<rparr>) \<and> (\<exists>n. (\<exists>e w. d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)) \<and> \<pi>s ! i = map the (get_labels d n))))")
    apply(rename_tac d w r a list i)(*strict*)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf = option_to_list (Some (liftB w ! i))\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d w r a list i)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d w r a list i)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w r a list i)(*strict*)
     apply(rule cfgLM.der1_belongs)
     apply(simp add: option_to_list_def)
     apply(rename_tac d w r i)(*strict*)
     apply(rule hlp3)
      apply(rename_tac d w r i)(*strict*)
      apply(rule cfgLM.belongs_configurations)
       apply(rename_tac d w r i)(*strict*)
       apply(force)
      apply(rename_tac d w r i)(*strict*)
      apply(force)
     apply(rename_tac d w r i)(*strict*)
     apply (simp add: liftB_length)
    apply(rename_tac d w r a list i)(*strict*)
    apply(simp add: der1_def)
    apply(rename_tac d w r i)(*strict*)
    apply(simp add: option_to_list_def)
    apply(rule conjI)
     apply(rename_tac d w r i)(*strict*)
     apply(rule_tac
      x="[w!i]"
      in exI)
     apply(rule distrib_nth_liftB)
     apply (simp add: liftB_length)
    apply(rename_tac d w r i)(*strict*)
    apply(simp add: get_labels_def)
    apply (metis nat_seqEmpty zero_less_Suc)
   apply(rename_tac d w r a list)(*strict*)
   apply(erule exE)
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(subgoal_tac "a#list \<in> set (\<pi>s)")
    apply(rename_tac d w r a list \<pi>s)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(thin_tac "a # list \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (liftB w ! i))))")
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(erule conjE)+
   apply(thin_tac "\<pi>s = (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (liftB w ! i))))")
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(subgoal_tac "\<exists>i<length \<pi>s. \<pi>s!i = a#list")
    apply(rename_tac d w r a list \<pi>s)(*strict*)
    prefer 2
    apply (simp add: in_set_conv_nth)
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w r a list \<pi>s i)(*strict*)
   apply(subgoal_tac "\<pi>s!i=[]")
    apply(rename_tac d w r a list \<pi>s i)(*strict*)
    apply(force)
   apply(rename_tac d w r a list \<pi>s i)(*strict*)
   apply(rule foldl_empty2)
    apply(rename_tac d w r a list \<pi>s i)(*strict*)
    apply(force)
   apply(rename_tac d w r a list \<pi>s i)(*strict*)
   apply(force)
  apply(rename_tac d e w n r nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w r nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d e w r n)(*strict*)
  apply(subgoal_tac "\<exists>\<pi>s ws. foldl (@) [] (rev \<pi>s) = SSrenPI \<and> length \<pi>s = length SSrenALPHA \<and> foldl (@) [] ws = SSw \<and> length ws = length SSrenALPHA \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSrenALPHA ! i\<rparr>) \<and> d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>s ! i = map the (get_labels d' n'))" for SSrenPI SSw SSG SSrenALPHA)
   apply(rename_tac d e w r n)(*strict*)
   prefer 2
   apply(rule_tac
      e="e"
      and n="Suc n"
      and d="derivation_drop d (Suc 0)"
      and \<alpha>="map (\<lambda>x. [x]) (prod_rhs r)"
      in lemma_4_7_existence)
        apply(rename_tac d e w r n)(*strict*)
        apply(force)
       apply(rename_tac d e w r n)(*strict*)
       apply(rule cfgRM.derivation_drop_preserves_derivation_prime)
        apply(rename_tac d e w r n)(*strict*)
        apply(force)
       apply(rename_tac d e w r n)(*strict*)
       apply(force)
      apply(rename_tac d e w r n)(*strict*)
      apply(rule cfgRM.derivation_drop_preserves_belongs)
        apply(rename_tac d e w r n)(*strict*)
        apply(force)
       apply(rename_tac d e w r n)(*strict*)
       apply(force)
      apply(rename_tac d e w r n)(*strict*)
      apply(force)
     apply(rename_tac d e w r n)(*strict*)
     apply(simp add: derivation_drop_def)
     apply(rule sym)
     apply(rule split_string_into_single_item_strings)
    apply(rename_tac d e w r n)(*strict*)
    apply(simp add: derivation_drop_def)
   apply(rename_tac d e w r n)(*strict*)
   apply(force)
  apply(rename_tac d e w r n)(*strict*)
  apply(erule exE)+
  apply(rename_tac d e w r n \<pi>s ws)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      t="map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
      and s="foldl (@) [] (rev \<pi>s)"
      in ssubst)
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   apply(rule_tac
      t="foldl (@) [] (rev \<pi>s)"
      and s="map the (get_labels (derivation_drop d (Suc 0)) (Suc n))"
      in ssubst)
    apply(rename_tac d e w r n \<pi>s ws)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   apply(simp add: get_labels_def derivation_drop_def get_label_def)
   apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e w r n \<pi>s ws)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e w r n \<pi>s ws)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   apply(rule listEqI)
    apply(rename_tac d e w r n \<pi>s ws)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws i)(*strict*)
   apply(rule impI)
   apply(clarsimp)
   apply(rename_tac d e r n \<pi>s ws i)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc n) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d e r n \<pi>s ws i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d e r n \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d e r n \<pi>s ws i)(*strict*)
    apply(force)
   apply(rename_tac d e r n \<pi>s ws i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d e r n \<pi>s ws i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d e r n \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d e r n \<pi>s ws i)(*strict*)
    apply(force)
   apply(rename_tac d e r n \<pi>s ws i)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e w r n \<pi>s ws)(*strict*)
  apply(subgoal_tac "Suc n = length (foldl (@) [] \<pi>s)")
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   prefer 2
   apply(rule_tac
      t="length (foldl (@) [] \<pi>s)"
      and s="length (foldl (@) [] (rev \<pi>s))"
      in ssubst)
    apply(rename_tac d e w r n \<pi>s ws)(*strict*)
    apply (metis length_foldl_rev)
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   apply(rule_tac
      t="foldl (@) [] (rev \<pi>s)"
      and s="map the (get_labels (derivation_drop d (Suc 0)) (Suc n))"
      in ssubst)
    apply(rename_tac d e w r n \<pi>s ws)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   apply(simp (no_asm) add: get_labels_def)
   apply (metis nat_seq_length_Suc0 zero_less_Suc)
  apply(rename_tac d e w r n \<pi>s ws)(*strict*)
  apply(subgoal_tac "\<exists>d e \<pi>sX. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = prod_rhs r\<rparr>) \<and> d (length(foldl (@) [] \<pi>s)) = Some (pair e \<lparr>cfg_conf = liftB (foldl (@) [] ws)\<rparr>) \<and> length \<pi>sX = length (prod_rhs r) \<and> map the (get_labels d (length(foldl (@) [] (\<pi>s)))) = foldl (@) [] \<pi>sX \<and> map (CFGlm2rm G) \<pi>sX = \<pi>s \<and> (\<forall>i<length (prod_rhs r). \<exists>d e. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r!i]\<rparr>) \<and> d (length(\<pi>sX!i)) = Some (pair e \<lparr>cfg_conf = liftB (ws!i)\<rparr>) \<and> \<pi>sX!i = map the (get_labels d (length(\<pi>sX!i))))")
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>d e \<pi>sX. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = take (length (prod_rhs r)) (prod_rhs r)\<rparr>) \<and> d (length(foldl (@) [] (take (length (prod_rhs r)) \<pi>s))) = Some (pair e \<lparr>cfg_conf = liftB (foldl (@) [] (take (length (prod_rhs r)) ws))\<rparr>) \<and> length \<pi>sX = (length (prod_rhs r)) \<and> map the (get_labels d (length(foldl (@) [] (take (length (prod_rhs r)) \<pi>s)))) = foldl (@) [] \<pi>sX \<and> map (CFGlm2rm G) \<pi>sX = take (length (prod_rhs r)) \<pi>s \<and> (\<forall>i<length (prod_rhs r). \<exists>d e. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r!i]\<rparr>) \<and> d (length(\<pi>sX!i)) = Some (pair e \<lparr>cfg_conf = liftB (ws!i)\<rparr>) \<and> \<pi>sX!i = map the (get_labels d (length(\<pi>sX!i))))")
    apply(rename_tac d e w r n \<pi>s ws)(*strict*)
    apply(erule exE)+
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
    apply(erule conjE)+
    apply(rule_tac
      x="da"
      in exI)
    apply(rule_tac
      x="ea"
      in exI)
    apply(rule_tac
      x="\<pi>sX"
      in exI)
    apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   apply(rule_tac
      n="n"
      in lemma_4_10_combine)
          apply(rename_tac d e w r n \<pi>s ws)(*strict*)
          apply(force)
         apply(rename_tac d e w r n \<pi>s ws y da ea A wa \<pi>)(*strict*)
         apply(force)
        apply(rename_tac d e w r n \<pi>s ws)(*strict*)
        apply(force)
       apply(rename_tac d e w r n \<pi>s ws)(*strict*)
       apply(force)
      apply(rename_tac d e w r n \<pi>s ws)(*strict*)
      apply(force)
     apply(rename_tac d e w r n \<pi>s ws)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s ws)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws)(*strict*)
  apply(erule exE)+
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = [teA (prod_lhs r)]\<rparr> r \<lparr>cfg_conf = prod_rhs r\<rparr>) da (Suc 0)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="[]"
      in exI)
     apply(rule_tac
      x="[]"
      in exI)
     apply(clarsimp)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
      apply(force)
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
  apply(rule_tac
      t="(map the (get_labels (derivation_append (der2 \<lparr>cfg_conf = [teA (prod_lhs r)]\<rparr> r \<lparr>cfg_conf = prod_rhs r\<rparr>) da (Suc 0)) (Suc (Suc n))))"
      and s="r#(foldl (@) [] \<pi>sX)"
      in ssubst)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule conjI)
    apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
    apply(simp add: get_label_def derivation_append_def der2_def)
   apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
   apply(rule_tac
      t="foldl (@) [] \<pi>sX"
      and s="map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX))))"
      in ssubst)
    apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
    apply(force)
   apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
   apply(rule listEqI)
    apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) ((Suc (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX)))))) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="foldl (@) [] \<pi>sX"
      and s="map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX))))"
      in ssubst)
     apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
     apply(force)
    apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX)))) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d e r n ws da ea \<pi>sX)(*strict*)
    apply (metis One_nat_def Suc_eq_plus1 diff_Suc_1 distrib_add_apppend_with_map length_map nat_seq_length_prime)
   apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX)))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) ((Suc (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX)))))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc (Suc 0)) (Suc (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX)))) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
     apply(force)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    apply(force)
   apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def derivation_append_def der2_def)
   apply(rule_tac
      t="foldl (@) [] \<pi>sX"
      and s="map (the \<circ> (\<lambda>i. case da i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e)) (nat_seq (Suc 0) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX))))"
      in ssubst)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    apply(force)
   apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
   apply(rule_tac
      t="map (the \<circ> (\<lambda>i. case da i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e)) (nat_seq (Suc 0) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX)))) ! i"
      and s="(the \<circ> (\<lambda>i. case da i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e)) ((nat_seq (Suc 0) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX)))) ! i)"
      in ssubst)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    apply(rule nth_map)
    apply(subgoal_tac "length (nat_seq (Suc 0) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX)))) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    apply(force)
   apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) (length (foldl (@) [] (map (CFGlm2rm G) \<pi>sX))) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
     apply(force)
    apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
    apply(force)
   apply(rename_tac d e r n ws da ea \<pi>sX i)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
  apply(rule sym)
  apply(rule_tac
      t="foldl (@) [] \<pi>sX"
      and s="map the (get_labels da (length (foldl (@) [] \<pi>s)))"
      in ssubst)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
  apply(subgoal_tac "\<exists>\<pi>s. (\<pi>s=(SOME \<pi>s. SSP \<pi>s)) \<and> SSP \<pi>s" for SSP)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   prefer 2
   apply(rule_tac
      P="\<lambda>\<pi>sa. foldl (@) [] \<pi>sa = map the (get_labels da (length (foldl (@) [] \<pi>s))) \<and> length \<pi>sa = length (prod_rhs r) \<and> (\<forall>i<length \<pi>sa. \<pi>sa ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i)))"
      in someI_existence)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(rule_tac
      x="\<pi>sX"
      in exI)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
   apply(rule allI)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i)(*strict*)
   apply(rule impI)
   apply(simp (no_asm) add: CFGlmEliminators_def)
   apply(erule_tac
      x="i"
      and P="\<lambda>i. i < length (prod_rhs r) \<longrightarrow> (\<exists>d e. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r ! i]\<rparr>) \<and> d (length (\<pi>sX ! i)) = Some (pair e \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>sX ! i = map the (get_labels d (length (\<pi>sX ! i))))"
      in allE)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i)(*strict*)
   apply(erule impE)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i)(*strict*)
   apply(erule exE)+
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
   apply(erule conjE)+
   apply(rule_tac
      x="db"
      in exI)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
    apply(simp add: option_to_list_def)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
   apply(rule_tac
      x="(length (\<pi>sX ! i))"
      in exI)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
    apply(rule_tac
      x="eb"
      in exI)
    apply(rule_tac
      x="ws!i"
      in exI)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX i db eb)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX)(*strict*)
  apply(erule exE)+
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      t="CFGlm2rm SSG (SSr # SSpiPrime)"
      and s="(let \<pi>s = SOME \<pi>s. foldl (@) [] \<pi>s = SSrenPIprime \<and> length \<pi>s = length (prod_rhs SSr) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators SSG (Some (prod_rhs SSr ! i))) in SSr # foldl (@) [] (map (CFGlm2rm SSG) (rev \<pi>s)))" for SSG SSr SSrenPIprime SSpiPrime
      in ssubst)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
   apply(rule CFGlm2rm.psimps)
   apply(rule CFGlm2rm.domintros)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
   apply(subgoal_tac "xa \<in> set \<pi>sa")
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
   apply(thin_tac "\<pi>sa = (SOME \<pi>sa. foldl (@) [] \<pi>sa = map the (get_labels da (length (foldl (@) [] \<pi>s))) \<and> length \<pi>sa = length (prod_rhs r) \<and> (\<forall>i<length \<pi>sa. \<pi>sa ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
   apply(thin_tac "xa \<in> set (SOME \<pi>sa. foldl (@) [] \<pi>sa = map the (get_labels da (length (foldl (@) [] \<pi>s))) \<and> length \<pi>sa = length (prod_rhs r) \<and> (\<forall>i<length \<pi>sa. \<pi>sa ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
   apply(subgoal_tac "\<exists>i<length \<pi>sa. \<pi>sa!i = xa")
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
    prefer 2
    apply(rule_tac
      s="xa \<in> set \<pi>sa"
      in subst)
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
     apply (rule in_set_conv_nth)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
    apply (metis)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa)(*strict*)
   apply(erule exE)+
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa i)(*strict*)
   apply(rule_tac
      t="xa"
      and s="\<pi>sa ! i"
      in ssubst)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa i)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa i)(*strict*)
   apply(thin_tac "xa \<in> set \<pi>sa")
   apply(erule conjE)+
   apply(thin_tac "\<pi>sa ! i = xa")
   apply(erule_tac
      x="i"
      and P="\<lambda>i. i < length \<pi>sa \<longrightarrow> \<pi>sa ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))"
      in allE)
   apply(erule impE)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa i)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa xa i)(*strict*)
   apply(simp add: CFGlmEliminators_def)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i)(*strict*)
   apply(erule exE)+
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db)(*strict*)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na)(*strict*)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na eb wa)(*strict*)
   apply(case_tac "na")
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na eb wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db wa)(*strict*)
    apply(rule_tac
      t="map the (get_labels db 0)"
      and s="[]"
      in ssubst)
     apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db wa)(*strict*)
     apply(simp add: get_labels_def)
     apply (metis nat_seqEmpty zero_less_Suc)
    apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db wa)(*strict*)
    apply(rule CFGlm2rm.domintros)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na eb wa nat)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. db 0 = Some (pair e1 c1) \<and> SSd (Suc SSi) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSi)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na eb wa nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="na"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na eb wa nat)(*strict*)
      apply(force)
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na eb wa nat)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na eb wa nat)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa i db na eb wa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 c2)(*strict*)
   apply(simp add: option_to_list_def)
   apply(case_tac c2)
   apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 c2 cfg_conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 cfg_conf)(*strict*)
   apply(rule_tac
      d="db"
      in CFGlm2rm_terminates)
         apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 cfg_conf)(*strict*)
         apply(force)
        apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 cfg_conf)(*strict*)
        apply(force)
       apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 cfg_conf)(*strict*)
       apply(force)
      apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 cfg_conf)(*strict*)
      apply(force)
     apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 cfg_conf)(*strict*)
     apply(force)
    apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac d e r n ws da ea \<pi>sX \<pi>sa i db eb wa nat e2 cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
  apply(rule_tac
      t="SOME \<pi>sa. foldl (@) [] \<pi>sa = map the (get_labels da (length (foldl (@) [] \<pi>s))) \<and> length \<pi>sa = length (prod_rhs r) \<and> (\<forall>i<length \<pi>sa. \<pi>sa ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i)))"
      and s="\<pi>sa"
      in ssubst)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
  apply(thin_tac "\<pi>sa = (SOME \<pi>sa. foldl (@) [] \<pi>sa = map the (get_labels da (length (foldl (@) [] \<pi>s))) \<and> length \<pi>sa = length (prod_rhs r) \<and> (\<forall>i<length \<pi>sa. \<pi>sa ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
  apply(simp (no_asm))
  apply(rule_tac
      t="\<pi>s"
      and s="map (CFGlm2rm G) \<pi>sX"
      in ssubst)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
  apply(rule_tac
      t="rev (map (CFGlm2rm G) \<pi>sX)"
      and s="map (CFGlm2rm G) (rev \<pi>sX)"
      in ssubst)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
   apply(rule rev_map)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
  apply(subgoal_tac "\<pi>sa=\<pi>sX")
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
  apply(subgoal_tac "\<exists>ws. length \<pi>sa = length ws \<and> (\<forall>k<length \<pi>sa. \<exists>d n e. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some ((prod_rhs r) ! k))\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>) \<and> \<pi>sa ! k = map the (get_labels d n))")
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
   prefer 2
   apply(rule existence_of_elimination_string_list)
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa)(*strict*)
  apply(erule exE)+
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "foldl (@) [] wsa = foldl (@) [] ws")
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>s="\<pi>sa"
      and d="da"
      and n="Suc n"
      in unique_elimination)
           apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
           apply(force)
          apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
          apply(force)
         apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
         apply(force)
        apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
        apply(force)
       apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
       apply(force)
      apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
      apply(simp add: get_labels_def)
      apply(rule sym)
      apply(rule_tac
      t="map (\<lambda>a. the (get_label (da a))) (nat_seq (Suc 0) (length (foldl (@) [] \<pi>s)))"
      and s="map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) (length (foldl (@) [] \<pi>s)))"
      in ssubst)
       apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(subgoal_tac "\<pi>sa=\<pi>sX \<and> wsa = ws")
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(rule_tac
      \<pi>="map the (get_labels da (length (foldl (@) [] \<pi>s)))"
      and w="foldl (@) [] ws"
      and G="G"
      and e="ea"
      and n="(length (foldl (@) [] \<pi>s))"
      and d="da"
      and \<alpha>="map (\<lambda>x. [x]) (prod_rhs r)"
      in lemma_4_6_uniqueness)
         apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
         apply(force)
        apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
        apply(force)
       apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
       apply(force)
      apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
      apply(rule_tac
      t="foldl (@) [] (map (\<lambda>x. [x]) (prod_rhs r))"
      and s="prod_rhs r"
      in ssubst)
       apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
       apply (metis split_string_into_single_item_strings)
      apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
      apply(force)
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
    apply(rule_tac
      t="length (map (\<lambda>x. [x]) (prod_rhs r))"
      and s="length (prod_rhs r)"
      in ssubst)
     apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
     apply (metis length_map)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(rule conjI)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(rule conjI)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa)(*strict*)
  apply(rule allI)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa i)(*strict*)
  apply(rule impI)
  apply(erule_tac
    x="i"
    and P="\<lambda>i. i < length (prod_rhs r) \<longrightarrow> (\<exists>d e. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = [prod_rhs r ! i]\<rparr>) \<and> d (length (\<pi>sX ! i)) = Some (pair e \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>sX ! i = map the (get_labels d (length (\<pi>sX ! i))))"
    in allE)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa i)(*strict*)
  apply(erule impE)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa i)(*strict*)
  apply(force)
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa i)(*strict*)
  apply(erule exE)+
  apply(rename_tac d e w r n \<pi>s ws da ea \<pi>sX \<pi>sa wsa i db eb)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
    x="db"
    in exI)
  apply(rule_tac
    x="(length (\<pi>sX ! i))"
    in exI)
  apply(rule_tac
    x="eb"
    in exI)
  apply(clarsimp)
  done

lemma lemma_4_12_2: "
  valid_cfg G
  \<Longrightarrow> CFGlm_unambiguous G
  \<Longrightarrow> CFGrm_unambiguous G"
  apply(simp add: CFGrm_unambiguous_def CFGlm_unambiguous_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
  apply(subgoal_tac "\<exists>d' e'. cfgLM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> SSrenPI = CFGlm2rm SSG (map the (get_labels d' SSn))" for SSA SSw SSrenPI SSG SSn)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
   prefer 2
   apply(rule_tac
      A="teA (cfg_initial G)"
      and d="d1"
      in lemma_4_10)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
       apply(rule cfgRM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(rule cfgRM.derivation_initial_belongs)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
     apply(simp add: cfgRM.derivation_initial_def)
     apply(case_tac "d1 0")
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w a)(*strict*)
     apply(case_tac a)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w b)(*strict*)
     apply(simp add: cfg_initial_configurations_def)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
  apply(subgoal_tac "\<exists>d' e'. cfgLM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> SSrenPI = CFGlm2rm SSG (map the (get_labels d' SSn))" for SSA SSw SSrenPI SSG SSn)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
   prefer 2
   apply(rule_tac
      A="teA (cfg_initial G)"
      and d="d2"
      in lemma_4_10)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
       apply(rule cfgRM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(rule cfgRM.derivation_initial_belongs)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
     apply(simp add: cfgRM.derivation_initial_def)
     apply(case_tac "d2 0")
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w a)(*strict*)
     apply(case_tac a)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w b d' e')(*strict*)
     apply(simp add: cfg_initial_configurations_def)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
  apply(erule_tac
      x="d'"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
   apply(rule cfgLM.derivation_initialI)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
  apply(erule_tac
      x="d'a"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
   apply(rule cfgLM.derivation_initialI)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
  apply(erule_tac
      x="n1"
      in allE)
  apply(erule_tac
      x="n2"
      in allE)
  apply(erule_tac
      x="e'"
      in allE)
  apply(erule_tac
      x="e'a"
      in allE)
  apply(erule_tac
      x="w"
      in allE)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
  apply(subgoal_tac "n1=n2")
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e')(*strict*)
   apply(rule ext)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
   apply(case_tac "x\<le>n2")
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(rule_tac
      n="n2"
      and ?m1.0="0"
      and ?m2.0="0"
      in equal_labels_implies_equal_cfgRMderivation)
           apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
           apply(force)
          apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
          apply(rule cfgRM.derivation_initial_is_derivation)
          apply(force)
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
         apply(rule cfgRM.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
        apply(simp add: cfgRM.derivation_initial_def)
        apply(clarsimp)
        apply(case_tac "d1 0")
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
         apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a)(*strict*)
        apply(case_tac "d2 0")
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a)(*strict*)
         apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a aa)(*strict*)
        apply(case_tac a)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a aa option b)(*strict*)
        apply(case_tac aa)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a aa option b optiona ba)(*strict*)
        apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x b ba)(*strict*)
        apply(simp add: cfg_initial_configurations_def)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
   apply(rule_tac
      t="d1 x"
      and s="None"
      in ssubst)
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(rule_tac
      n="n2"
      in cfgRM_no_step_from_no_nonterminal)
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
        apply(rule cfgRM.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(rule cfgRM.derivation_initial_belongs)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
     apply(clarsimp)
     apply(rule setA_liftB)
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
   apply(rule sym)
   apply(rule_tac
      n="n2"
      in cfgRM_no_step_from_no_nonterminal)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(rule cfgRM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
      apply(rule cfgRM.derivation_initial_belongs)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(clarsimp)
    apply(rule setA_liftB)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
  apply(case_tac "n1<n2")
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(subgoal_tac "d'a n2 = None")
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(rule_tac
      n="n1"
      in cfgLM_no_step_from_no_nonterminal)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(clarsimp)
    apply(rule setA_liftB)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
  apply(case_tac "n2<n1")
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(subgoal_tac "d'a n1 = None")
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(rule_tac
      n="n2"
      in cfgLM_no_step_from_no_nonterminal)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(clarsimp)
    apply(rule setA_liftB)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
  apply(force)
  done

lemma lemma_4_9: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> (\<exists>d' e'. cfgRM.derivation G d'
  \<and> cfgRM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>)
  \<and> d' n = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>)
  \<and> CFGlm2rm G \<pi>=map the (get_labels d' n))"
  apply(induct n arbitrary: d e A w \<pi> rule: less_induct)
  apply(rename_tac x d e A w \<pi>)(*strict*)
  apply(case_tac x)
   apply(rename_tac x d e A w \<pi>)(*strict*)
   apply(thin_tac "\<And>y d e A w \<pi>. y < x \<Longrightarrow> valid_cfg G \<Longrightarrow> cfgLM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> d y = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> \<pi> = map the (get_labels d y) \<Longrightarrow> \<exists>d' e'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<and> d' y = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>) \<and> CFGlm2rm G \<pi> = map the (get_labels d' y)")
   apply(rename_tac x d e A w \<pi>)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A w)(*strict*)
   apply(case_tac w)
    apply(rename_tac d A w)(*strict*)
    apply(force)
   apply(rename_tac d A w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac d a list)(*strict*)
    prefer 2
    apply(rename_tac d a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac d a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d a)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teB a]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac d a)(*strict*)
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac d a)(*strict*)
   apply(rule conjI)
    apply(rename_tac d a)(*strict*)
    apply(rule cfgRM.der1_belongs)
    apply (metis cfgLM.belongs_configurations)
   apply(rename_tac d a)(*strict*)
   apply(rule conjI)
    apply(rename_tac d a)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac d a)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "nat_seq (Suc 0) 0=[]")
    apply(rename_tac d a)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac d a)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d a)(*strict*)
    apply(rule CFGlm2rm.psimps)
    apply(rule CFGlm2rm.domintros)
   apply(rename_tac d a)(*strict*)
   apply (metis nat_seqEmpty zero_less_Suc)
  apply(rename_tac x d e A w \<pi> nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e A w nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d e A w n)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac d e A w n)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d e A w n)(*strict*)
     apply(force)
    apply(rename_tac d e A w n)(*strict*)
    apply(force)
   apply(rename_tac d e A w n)(*strict*)
   apply(force)
  apply(rename_tac d e A w n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e A w n e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d e A w n e2 c2 l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac d e A w n e2 c2 l r)(*strict*)
   prefer 2
   apply(rename_tac d e A w n e2 c2 l r a list)(*strict*)
   apply(force)
  apply(rename_tac d e A w n e2 c2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w n e2 c2)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d e w n e2 c2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w n e2)(*strict*)
  apply(rename_tac r)
  apply(rename_tac d e w n r)(*strict*)
  apply(rule_tac
      t="(map the (get_labels d (Suc n)))"
      and s="(map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc n)))"
      in ssubst)
   apply(rename_tac d e w n r)(*strict*)
   apply(simp add: get_labels_def)
  apply(rename_tac d e w n r)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = Suc 0 # nat_seq (Suc (Suc 0)) ((Suc n))")
   apply(rename_tac d e w n r)(*strict*)
   prefer 2
   apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
  apply(rename_tac d e w n r)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="(the (get_label (Some (pair (Some r) \<lparr>cfg_conf = prod_rhs r\<rparr>))))"
      and s="r"
      in ssubst)
   apply(rename_tac d e w n r)(*strict*)
   apply(simp add: get_label_def)
  apply(rename_tac d e w n r)(*strict*)
  apply(case_tac n)
   apply(rename_tac d e w n r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w r)(*strict*)
   apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (prod_lhs r)]\<rparr> r \<lparr>cfg_conf = prod_rhs r\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac d w r)(*strict*)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac d w r)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w r)(*strict*)
    apply(rule cfgRM.derivation_belongs)
       apply(rename_tac d w r)(*strict*)
       apply(force)
      apply(rename_tac d w r)(*strict*)
      apply(simp add: der2_def)
     apply(rename_tac d w r)(*strict*)
     apply(rule cfgLM.belongs_configurations)
      apply(rename_tac d w r)(*strict*)
      apply(force)
     apply(rename_tac d w r)(*strict*)
     apply(force)
    apply(rename_tac d w r)(*strict*)
    apply(force)
   apply(rename_tac d w r)(*strict*)
   apply(simp add: der2_def)
   apply(subgoal_tac "nat_seq (Suc (Suc 0)) (Suc 0) = []")
    apply(rename_tac d w r)(*strict*)
    prefer 2
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac d w r)(*strict*)
   apply(clarsimp)
   apply(simp add: get_labels_def)
   apply(simp add: get_label_def)
   apply(rule_tac
      t="CFGlm2rm SSG (SSr # SSpiPrime)"
      and s="(let \<pi>s = SOME \<pi>s. foldl (@) [] \<pi>s = SSrenPIprime \<and> length \<pi>s = length (prod_rhs SSr) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators SSG (Some (prod_rhs SSr ! i))) in SSr # foldl (@) [] (map (CFGlm2rm SSG) (rev \<pi>s)))" for SSG SSr SSrenPIprime SSpiPrime
      in ssubst)
    apply(rename_tac d w r)(*strict*)
    apply(rule CFGlm2rm.psimps)
    apply(rule CFGlm2rm_terminates)
          apply(rename_tac d w r)(*strict*)
          apply(force)
         apply(rename_tac d w r)(*strict*)
         apply(force)
        apply(rename_tac d w r)(*strict*)
        apply(force)
       apply(rename_tac d w r)(*strict*)
       apply(force)
      apply(rename_tac d w r)(*strict*)
      apply(force)
     apply(rename_tac d w r)(*strict*)
     apply(force)
    apply(rename_tac d w r)(*strict*)
    apply(simp add: get_labels_def)
    apply(simp add: get_label_def)
   apply(rename_tac d w r)(*strict*)
   apply(simp add: Let_def)
   apply(rule foldl_empty)
   apply(rename_tac d w r a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w r x)(*strict*)
   apply(case_tac "x")
    apply(rename_tac d w r x)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w r)(*strict*)
    apply(rule CFGlm2rm.psimps)
    apply(rule CFGlm2rm.domintros)
   apply(rename_tac d w r x a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w r a list)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d w r a list)(*strict*)
    apply(force)
   apply(rename_tac d w r a list)(*strict*)
   apply(thin_tac "\<And>y d e A w \<pi>. y = 0 \<Longrightarrow> cfgLM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> None = e \<and> [A] = liftB w \<Longrightarrow> \<pi> = map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i))) (nat_seq (Suc 0) 0) \<Longrightarrow> \<exists>d'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = liftB w\<rparr>) \<and> (\<exists>e'. d' 0 = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>)) \<and> CFGlm2rm G (map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i))) (nat_seq (Suc 0) 0)) = map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d' i))) (nat_seq (Suc 0) 0)")
   apply(rename_tac d w r a list)(*strict*)
   apply(subgoal_tac "\<exists>\<pi>s. (\<pi>s= (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (liftB w ! i))))) \<and> foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (liftB w ! i)))")
    apply(rename_tac d w r a list)(*strict*)
    prefer 2
    apply(rule_tac
      x="map (\<lambda>x. []) w"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac d w r a list)(*strict*)
     apply(rule sym)
     apply(rule_tac
      a="map (\<lambda>x. []) w"
      in someI2)
      apply(rename_tac d w r a list)(*strict*)
      apply(clarsimp)
      apply(rule conjI)
       apply(rename_tac d w r a list)(*strict*)
       apply(rule foldl_empty)
       apply(rename_tac d w r a list aa)(*strict*)
       apply(clarsimp)
      apply(rename_tac d w r a list)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w r a list)(*strict*)
       apply (simp add: liftB_length)
      apply(rename_tac d w r a list)(*strict*)
      apply(clarsimp)
      apply(rename_tac d w r a list i)(*strict*)
      apply(simp add: CFGlmEliminators_def)
      apply(thin_tac "a # list \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (liftB w ! i))\<rparr>) \<and> (\<exists>n. (\<exists>e w. d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)) \<and> \<pi>s ! i = map the (get_labels d n))))")
      apply(rename_tac d w r a list i)(*strict*)
      apply(rule_tac
      x="der1 \<lparr>cfg_conf = option_to_list (Some (liftB w ! i))\<rparr>"
      in exI)
      apply(rule conjI)
       apply(rename_tac d w r a list i)(*strict*)
       apply(rule cfgLM.der1_is_derivation)
      apply(rename_tac d w r a list i)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w r a list i)(*strict*)
       apply(rule cfgLM.der1_belongs)
       apply(simp add: option_to_list_def)
       apply(rename_tac d w r i)(*strict*)
       apply(rule hlp3)
        apply(rename_tac d w r i)(*strict*)
        apply(rule cfgLM.belongs_configurations)
         apply(rename_tac d w r i)(*strict*)
         apply(force)
        apply(rename_tac d w r i)(*strict*)
        apply(force)
       apply(rename_tac d w r i)(*strict*)
       apply (simp add: liftB_length)
      apply(rename_tac d w r a list i)(*strict*)
      apply(simp add: der1_def)
      apply(rename_tac d w r i)(*strict*)
      apply(simp add: option_to_list_def)
      apply(rule conjI)
       apply(rename_tac d w r i)(*strict*)
       apply(rule_tac
      x="[w!i]"
      in exI)
       apply(rule distrib_nth_liftB)
       apply (simp add: liftB_length)
      apply(rename_tac d w r i)(*strict*)
      apply(simp add: get_labels_def)
      apply (metis nat_seqEmpty zero_less_Suc)
     apply(rename_tac d w r a list x)(*strict*)
     apply(clarsimp)
     apply(rule listEqI)
      apply(rename_tac d w r a list x)(*strict*)
      apply(clarsimp)
      apply (simp add: liftB_length)
     apply(rename_tac d w r a list x i)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="map (\<lambda>x. []) w ! i"
      and s="(\<lambda>x. []) (w ! i)"
      in ssubst)
      apply(rename_tac d w r a list x i)(*strict*)
      apply(rule nth_map)
      apply (simp add: liftB_length)
     apply(rename_tac d w r a list x i)(*strict*)
     apply(rule foldl_empty2)
      apply(rename_tac d w r a list x i)(*strict*)
      apply(force)
     apply(rename_tac d w r a list x i)(*strict*)
     apply(force)
    apply(rename_tac d w r a list)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w r a list)(*strict*)
     apply(rule foldl_empty)
     apply(rename_tac d w r a list aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w r a list)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w r a list)(*strict*)
     apply (simp add: liftB_length)
    apply(rename_tac d w r a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w r a list i)(*strict*)
    apply(simp add: CFGlmEliminators_def)
    apply(thin_tac "a # list \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (liftB w ! i))\<rparr>) \<and> (\<exists>n. (\<exists>e w. d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)) \<and> \<pi>s ! i = map the (get_labels d n))))")
    apply(rename_tac d w r a list i)(*strict*)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf = option_to_list (Some (liftB w ! i))\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d w r a list i)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d w r a list i)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w r a list i)(*strict*)
     apply(rule cfgLM.der1_belongs)
     apply(simp add: option_to_list_def)
     apply(rename_tac d w r i)(*strict*)
     apply(rule hlp3)
      apply(rename_tac d w r i)(*strict*)
      apply(rule cfgLM.belongs_configurations)
       apply(rename_tac d w r i)(*strict*)
       apply(force)
      apply(rename_tac d w r i)(*strict*)
      apply(force)
     apply(rename_tac d w r i)(*strict*)
     apply (simp add: liftB_length)
    apply(rename_tac d w r a list i)(*strict*)
    apply(simp add: der1_def)
    apply(rename_tac d w r i)(*strict*)
    apply(simp add: option_to_list_def)
    apply(rule conjI)
     apply(rename_tac d w r i)(*strict*)
     apply(rule_tac
      x="[w!i]"
      in exI)
     apply(rule distrib_nth_liftB)
     apply (simp add: liftB_length)
    apply(rename_tac d w r i)(*strict*)
    apply(simp add: get_labels_def)
    apply (metis nat_seqEmpty zero_less_Suc)
   apply(rename_tac d w r a list)(*strict*)
   apply(erule exE)
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(subgoal_tac "a#list \<in> set (\<pi>s)")
    apply(rename_tac d w r a list \<pi>s)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(thin_tac "a # list \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (liftB w ! i))))")
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(erule conjE)+
   apply(thin_tac "\<pi>s = (SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (liftB w) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (liftB w ! i))))")
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(subgoal_tac "\<exists>i<length \<pi>s. \<pi>s!i = a#list")
    apply(rename_tac d w r a list \<pi>s)(*strict*)
    prefer 2
    apply (simp add: in_set_conv_nth)
   apply(rename_tac d w r a list \<pi>s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w r a list \<pi>s i)(*strict*)
   apply(subgoal_tac "\<pi>s!i=[]")
    apply(rename_tac d w r a list \<pi>s i)(*strict*)
    apply(force)
   apply(rename_tac d w r a list \<pi>s i)(*strict*)
   apply(rule foldl_empty2)
    apply(rename_tac d w r a list \<pi>s i)(*strict*)
    apply(force)
   apply(rename_tac d w r a list \<pi>s i)(*strict*)
   apply(force)
  apply(rename_tac d e w n r nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w r nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d e w r n)(*strict*)
  apply(subgoal_tac "\<exists>\<pi>s. (\<pi>s=(SOME \<pi>s. foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))) \<and> (foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
   apply(rename_tac d e w r n)(*strict*)
   prefer 2
   apply(rule someI_existence)
   apply(subgoal_tac "\<exists>\<pi>s ws. foldl (@) [] \<pi>s = SSrenPI \<and> length \<pi>s = length SSrenALPHA \<and> foldl (@) [] ws = SSw \<and> length ws = length SSrenALPHA \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'. cfgLM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSrenALPHA ! i\<rparr>) \<and> d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>s ! i = map the (get_labels d' n'))" for SSrenPI SSw SSG SSrenALPHA)
    apply(rename_tac d e w r n)(*strict*)
    prefer 2
    apply(rule_tac
      e="e"
      and n="Suc n"
      and d="derivation_drop d (Suc 0)"
      and \<alpha>="map (\<lambda>x. [x]) (prod_rhs r)"
      in lemma_4_6_existence)
         apply(rename_tac d e w r n)(*strict*)
         apply(force)
        apply(rename_tac d e w r n)(*strict*)
        apply(rule cfgLM.derivation_drop_preserves_derivation_prime)
         apply(rename_tac d e w r n)(*strict*)
         apply(force)
        apply(rename_tac d e w r n)(*strict*)
        apply(force)
       apply(rename_tac d e w r n)(*strict*)
       apply(rule cfgLM.derivation_drop_preserves_belongs)
         apply(rename_tac d e w r n)(*strict*)
         apply(force)
        apply(rename_tac d e w r n)(*strict*)
        apply(force)
       apply(rename_tac d e w r n)(*strict*)
       apply(force)
      apply(rename_tac d e w r n)(*strict*)
      apply(simp add: derivation_drop_def)
      apply(rule sym)
      apply(rule split_string_into_single_item_strings)
     apply(rename_tac d e w r n)(*strict*)
     apply(simp add: derivation_drop_def)
    apply(rename_tac d e w r n)(*strict*)
    apply(force)
   apply(rename_tac d e w r n)(*strict*)
   apply(erule exE)
   apply(rename_tac d e w r n \<pi>s)(*strict*)
   apply(rule_tac
      x="\<pi>s"
      in exI)
   apply(clarsimp)
   apply(rename_tac d e r n \<pi>s ws)(*strict*)
   apply(rule conjI)
    apply(rename_tac d e r n \<pi>s ws)(*strict*)
    apply(simp add: get_labels_def)
    apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d e r n \<pi>s ws)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d e r n \<pi>s ws)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d e r n \<pi>s ws)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d e r n \<pi>s ws)(*strict*)
    apply(rule listEqI)
     apply(rename_tac d e r n \<pi>s ws)(*strict*)
     apply(clarsimp)
    apply(rename_tac d e r n \<pi>s ws i)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
     apply(rename_tac d e r n \<pi>s ws i)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac d e r n \<pi>s ws i)(*strict*)
      apply(force)
     apply(rename_tac d e r n \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d e r n \<pi>s ws i)(*strict*)
    apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
     apply(rename_tac d e r n \<pi>s ws i)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac d e r n \<pi>s ws i)(*strict*)
      apply(force)
     apply(rename_tac d e r n \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d e r n \<pi>s ws i)(*strict*)
    apply(simp add: derivation_drop_def)
   apply(rename_tac d e r n \<pi>s ws)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e r n \<pi>s ws i)(*strict*)
   apply(simp add: CFGlmEliminators_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac d e r n \<pi>s ws i d' n' e')(*strict*)
   apply(rule_tac
      x="d'"
      in exI)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      x="n'"
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d e w r n)(*strict*)
  apply(erule exE)+
  apply(rename_tac d e w r n \<pi>s)(*strict*)
  apply(rule_tac
      t="CFGlm2rm SSG (SSr # SSpiPrime)"
      and s="(let \<pi>s = SOME \<pi>s. foldl (@) [] \<pi>s = SSrenPIprime \<and> length \<pi>s = length (prod_rhs SSr) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators SSG (Some (prod_rhs SSr ! i))) in SSr # foldl (@) [] (map (CFGlm2rm SSG) (rev \<pi>s)))" for SSG SSr SSrenPIprime SSpiPrime
      in ssubst)
   apply(rename_tac d e w r n \<pi>s)(*strict*)
   apply(rule CFGlm2rm.psimps)
   apply(rule CFGlm2rm.domintros)
   apply(rename_tac d e w r n \<pi>s xa)(*strict*)
   apply(subgoal_tac "xa\<in> set \<pi>s")
    apply(rename_tac d e w r n \<pi>s xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d e w r n \<pi>s xa)(*strict*)
   apply(thin_tac "xa \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
   apply(rename_tac d e w r n \<pi>s xa)(*strict*)
   apply(erule conjE)+
   apply(thin_tac "\<pi>s = (SOME \<pi>s. foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
   apply(rename_tac d e w r n \<pi>s xa)(*strict*)
   apply(subgoal_tac "\<exists>k<length \<pi>s. \<pi>s!k = xa")
    apply(rename_tac d e w r n \<pi>s xa)(*strict*)
    prefer 2
    apply (metis in_set_conv_nth)
   apply(rename_tac d e w r n \<pi>s xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s k)(*strict*)
   apply(erule_tac
      x="k"
      in allE)
   apply(clarsimp)
   apply(simp add: CFGlmEliminators_def)
   apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s k da na ea wa)(*strict*)
   apply(case_tac na)
    apply(rename_tac d e w r n \<pi>s k da na ea wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e w r n \<pi>s k da wa)(*strict*)
    apply(simp add: get_labels_def)
    apply(subgoal_tac "nat_seq (Suc 0) 0=[]")
     apply(rename_tac d e w r n \<pi>s k da wa)(*strict*)
     apply(clarsimp)
     apply(rule CFGlm2rm.domintros)
    apply(rename_tac d e w r n \<pi>s k da wa)(*strict*)
    apply (metis nat_seqEmpty zero_less_Suc)
   apply(rename_tac d e w r n \<pi>s k da na ea wa nat)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. da 0 = Some (pair e1 c1) \<and> SSd (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd)
    apply(rename_tac d e w r n \<pi>s k da na ea wa nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d e w r n \<pi>s k da na ea wa nat)(*strict*)
      apply(force)
     apply(rename_tac d e w r n \<pi>s k da na ea wa nat)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s k da na ea wa nat)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s k da na ea wa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s k da ea wa nat e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s k da ea wa nat e2 c2 l ra)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d e w r n \<pi>s k da ea wa nat e2 c2 l ra cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s k da ea wa nat e2 l ra)(*strict*)
   apply(simp add: option_to_list_def)
   apply(case_tac l)
    apply(rename_tac d e w r n \<pi>s k da ea wa nat e2 l ra)(*strict*)
    prefer 2
    apply(rename_tac d e w r n \<pi>s k da ea wa nat e2 l ra a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s k da ea wa nat e2 l ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s k da ea wa nat e2)(*strict*)
   apply(rule_tac
      n="nat"
      and d="da"
      in CFGlm2rm_terminates)
         apply(rename_tac d e w r n \<pi>s k da ea wa nat e2)(*strict*)
         apply(force)
        apply(rename_tac d e w r n \<pi>s k da ea wa nat e2)(*strict*)
        apply(force)
       apply(rename_tac d e w r n \<pi>s k da ea wa nat e2)(*strict*)
       apply(force)
      apply(rename_tac d e w r n \<pi>s k da ea wa nat e2)(*strict*)
      apply(simp add: option_to_list_def)
     apply(rename_tac d e w r n \<pi>s k da ea wa nat e2)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s k da ea wa nat e2)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s k da ea wa nat e2)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s)(*strict*)
  apply(erule conjE)+
  apply(simp (no_asm) add: Let_def)
  apply(rule_tac
      t="SOME \<pi>s. foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i)))"
      and s="\<pi>s"
      in ssubst)
   apply(rename_tac d e w r n \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s)(*strict*)
  apply(thin_tac "\<pi>s = (SOME \<pi>s. foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
  apply(rename_tac d e w r n \<pi>s)(*strict*)
  apply(subgoal_tac "\<exists>d'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = prod_rhs r\<rparr>) \<and> (\<exists>e'. d' (Suc n) = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>)) \<and> foldl (@) [] (map (CFGlm2rm G) (rev \<pi>s)) = map the (get_labels d' (Suc n))")
   apply(rename_tac d e w r n \<pi>s)(*strict*)
   apply(erule exE)
   apply(rename_tac d e w r n \<pi>s d')(*strict*)
   apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = [teA (prod_lhs r)]\<rparr> r \<lparr>cfg_conf = prod_rhs r\<rparr>) d' (Suc 0)"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac d e w r n \<pi>s d')(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation)
      apply(rename_tac d e w r n \<pi>s d')(*strict*)
      apply(rule cfgRM.der2_is_derivation)
      apply(simp add: cfgRM_step_relation_def)
      apply(rule_tac
      x="[]"
      in exI)
      apply(rule_tac
      x="[]"
      in exI)
      apply(force)
     apply(rename_tac d e w r n \<pi>s d')(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s d')(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac d e w r n \<pi>s d')(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s d')(*strict*)
    apply(rule cfgRM.derivation_belongs)
       apply(rename_tac d e w r n \<pi>s d')(*strict*)
       apply(force)
      apply(rename_tac d e w r n \<pi>s d')(*strict*)
      prefer 3
      apply(force)
     apply(rename_tac d e w r n \<pi>s d')(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac d e w r n \<pi>s d')(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac d e w r n \<pi>s d')(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s d')(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s d')(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s d')(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac d e w r n \<pi>s d')(*strict*)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s d')(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac d e w r n \<pi>s d')(*strict*)
   apply(simp add: get_labels_def)
   apply(rule conjI)
    apply(rename_tac d e w r n \<pi>s d')(*strict*)
    apply(simp add: get_label_def derivation_append_def der2_def)
   apply(rename_tac d e w r n \<pi>s d')(*strict*)
   apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s d' e')(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e w r n \<pi>s d' e')(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e w r n \<pi>s d' e')(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d e w r n \<pi>s d' e')(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d e w r n \<pi>s d' e')(*strict*)
   apply(rule listEqI)
    apply(rename_tac d e w r n \<pi>s d' e')(*strict*)
    apply(clarsimp)
   apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
    apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
   apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
    apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s d' e' i)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d e w r n \<pi>s)(*strict*)
  apply(subgoal_tac "\<exists>!ws. length \<pi>s = length ws \<and> (\<forall>k<length \<pi>s. \<exists>d n e. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some ((prod_rhs r) ! k))\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>) \<and> \<pi>s ! k = map the (get_labels d n))")
   apply(rename_tac d e w r n \<pi>s)(*strict*)
   prefer 2
   apply(rule unique_existence_of_elimination_string_list)
     apply(rename_tac d e w r n \<pi>s)(*strict*)
     apply(force)
    apply(rename_tac d e w r n \<pi>s)(*strict*)
    apply(force)
   apply(rename_tac d e w r n \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac d e w r n \<pi>s)(*strict*)
  apply(thin_tac "\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))")
  apply(clarsimp)
  apply(rename_tac d e w r n \<pi>s ws)(*strict*)
  apply(case_tac r)
  apply(rename_tac d e w r n \<pi>s ws prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A v)
  apply(rename_tac d e w r n \<pi>s ws A v)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
  apply(subgoal_tac "foldl (@) [] ws = w")
   apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>s="\<pi>s"
      and n="Suc n"
      and G="G"
      and d="derivation_drop d (Suc 0)"
      in unique_elimination)
           apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
           apply(force)
          apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
          apply(rule cfgLM.derivation_drop_preserves_derivation_prime)
           apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
           apply(force)
          apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
          apply(force)
         apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
         apply(rule cfgLM.derivation_drop_preserves_belongs)
           apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
           apply(force)
          apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
          apply(force)
         apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
         apply(force)
        apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
        apply(simp add: derivation_drop_def)
       apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
       apply(simp add: derivation_drop_def)
      apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
      apply(rule_tac
      t="foldl (@) [] \<pi>s"
      and s="map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
      in ssubst)
       apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
       apply(force)
      apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
      apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSm + 1 - SSn" for SSm SSn)
       apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
       prefer 2
       apply(rule nat_seq_length_prime)
      apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
      apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
       apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
       prefer 2
       apply(rule nat_seq_length_prime)
      apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
      apply(rule listEqI)
       apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
       apply(force)
      apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
       apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
       apply(rule nat_seq_nth_compute)
        apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
        apply(force)
       apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
       apply(force)
      apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
      apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
       apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
       apply(rule nat_seq_nth_compute)
        apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
        apply(force)
       apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
       apply(force)
      apply(rename_tac d e w n \<pi>s ws A v i)(*strict*)
      apply(simp add: derivation_drop_def get_label_def)
     apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
     apply(force)
    apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
    apply(force)
   apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
   apply(force)
  apply(rename_tac d e w n \<pi>s ws A v)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n \<pi>s ws A v)(*strict*)
  apply(thin_tac "\<forall>y y'. length ws = length y \<and> (\<forall>k<length ws. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (v ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (y ! k)\<rparr>)) \<and> \<pi>s ! k = map the (get_labels d n))) \<and> length ws = length y' \<and> (\<forall>k<length ws. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (v ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (y' ! k)\<rparr>)) \<and> \<pi>s ! k = map the (get_labels d n))) \<longrightarrow> y = y'")
  apply(rename_tac d e n \<pi>s ws A v)(*strict*)
  apply(subgoal_tac "\<forall>k\<le>length ws. (let m=foldl (+) 0 (map length (take k (\<pi>s))) in (\<exists>d'. cfgRM.derivation G d' \<and>cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = take k v\<rparr>) \<and> (\<exists>e'. d' m = Some (pair e' \<lparr>cfg_conf = liftB (foldl (@) [] (take k ws))\<rparr>)) \<and> foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s))) = map the (get_labels d' m)))")
   apply(rename_tac d e n \<pi>s ws A v)(*strict*)
   apply(subgoal_tac "foldl (+) 0 (map length \<pi>s) = Suc n")
    apply(rename_tac d e n \<pi>s ws A v)(*strict*)
    apply(erule_tac
      x="length ws"
      and P="\<lambda>k. k\<le>length ws \<longrightarrow> (let m = foldl (+) 0 (map length (take k \<pi>s)) in \<exists>d'. cfgRM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = take k v\<rparr>) \<and> (\<exists>e'. d' m = Some (pair e' \<lparr>cfg_conf = liftB (foldl (@) [] (take k ws))\<rparr>)) \<and> foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s))) = map the (get_labels d' m))"
      in allE)
    apply(rename_tac d e n \<pi>s ws A v)(*strict*)
    apply(simp add: Let_def)
   apply(rename_tac d e n \<pi>s ws A v)(*strict*)
   apply(rule_tac
      t="foldl (+) 0 (map length \<pi>s)"
      and s="length (foldl (@) [] \<pi>s)"
      in ssubst)
    apply(rename_tac d e n \<pi>s ws A v)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d e n \<pi>s ws A v)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d e n \<pi>s ws A v)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e n \<pi>s ws A v)(*strict*)
   apply(rule distrib_add_apppend_with_map)
  apply(rename_tac d e n \<pi>s ws A v)(*strict*)
  apply(rule allI)
  apply(rename_tac d e n \<pi>s ws A v k)(*strict*)
  apply(rule impI)
  apply(rule lemma_4_9_hlp)
               apply(rename_tac d e n \<pi>s ws A v k y da ea Aa w \<pi>)(*strict*)
               apply(force)
              apply(rename_tac d e n \<pi>s ws A v k)(*strict*)
              apply(force)+
  done

lemma CFGlm2rm_preserves_length: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=[A]\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=liftB w\<rparr>)
  \<Longrightarrow> length (CFGlm2rm G (map the (get_labels d n))) = n"
  apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
   prefer 2
   apply(rule lemma_4_9)
        apply(force)+
  apply(clarsimp)
  apply(rename_tac d' e')(*strict*)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac d' e')(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac d' e')(*strict*)
  apply(force)
  done

lemma lemma_4_11_hlp: "
  valid_cfg G
  \<Longrightarrow> \<forall>k<length ws1.
           \<exists>d. cfgLM.derivation G d \<and>
               cfgLM.belongs G d \<and>
               d 0 =
               Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! k))\<rparr>) \<and>
               (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws1 ! k)\<rparr>)) \<and>
                    \<pi>s1 ! k = map the (get_labels d n))
  \<Longrightarrow> r \<in> cfg_productions G
  \<Longrightarrow> length (prod_rhs r) = length ws1
  \<Longrightarrow> length (prod_rhs r) = length \<pi>s1
  \<Longrightarrow> k\<le>length ws1
  \<Longrightarrow> \<exists>dx ex.
             cfgRM.derivation G dx \<and>
             cfgLM.belongs G dx \<and>
             dx 0 =
             Some (pair None
                    \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r)))\<rparr>) \<and>
             dx (length (foldl (@) [] (rev(take k \<pi>s1)))) = Some (pair ex \<lparr>cfg_conf = liftB (foldl (@) [] (take k ws1))\<rparr>) \<and>
             map the (get_labels dx (length (foldl (@) [] (rev(take k \<pi>s1))))) =
             foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s1)))"
  apply(induct k)
   apply(clarsimp)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rule cfgRM.der1_is_derivation)
   apply(rule conjI)
    apply(rule cfgRM.der1_belongs)
    apply(simp add: cfg_configurations_def)
   apply(rule conjI)
    apply(simp add: der1_def)
   apply(rule conjI)
    apply(rule_tac
      x="None"
      in exI)
    apply(simp add: der1_def)
   apply(simp add: get_labels_def)
   apply (metis nat_seqEmpty zero_less_Suc)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k dx ex)(*strict*)
  apply(erule_tac x="k" in allE')
  apply(erule impE)
   apply(rename_tac k dx ex)(*strict*)
   apply(force)
  apply(rename_tac k dx ex)(*strict*)
  apply(erule exE)+
  apply(rename_tac k dx ex d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac k dx ex d n)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac k dx ex d n e)(*strict*)
  apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
   apply(rename_tac k dx ex d n e)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in lemma_4_9)
        apply(rename_tac k dx ex d n e)(*strict*)
        apply(force)+
     apply(rename_tac k dx ex d n e)(*strict*)
     apply(simp add: option_to_list_def)
    apply(rename_tac k dx ex d n e)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(subgoal_tac "cfgRM.derivation_from_to SSG (derivation_append (derivation_map SSd2 (\<lambda>v. \<lparr>cfg_conf = SSw1 @ cfg_conf v\<rparr>)) (derivation_map SSd1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ SSw2'\<rparr>)) SSm2) {pair None \<lparr>cfg_conf = SSw1 @ SSw2\<rparr>} ({ y. (\<exists>xa. y = pair xa \<lparr>cfg_conf = SSw1' @ SSw2'\<rparr>)})" for SSG SSd2 SSd1 SSm2 SSw1 SSw2 SSw1' SSw2')
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   prefer 2
   apply(rule_tac
      ?d2.0="derivation_take d' n"
      and ?d1.0="derivation_take dx ((length (foldl (@) [] (rev (take k \<pi>s1)))))"
      and ?w1.0="foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r)))"
      and w1'="liftB (foldl (@) [] (take k ws1))"
      and w2'="liftB (ws1 ! k)"
      and ?w2.0="option_to_list (Some (prod_rhs r ! k))"
      in cfgRM_concatExtendIsFromToBoth)
        apply(rename_tac k dx ex d n e d' e')(*strict*)
        apply(force)
       apply(rename_tac k dx ex d n e d' e')(*strict*)
       apply(simp add: cfgRM.derivation_from_to_def)
       apply(simp add: cfgRM.derivation_from_def)
       apply(simp add: cfgRM.derivation_to_def)
       apply(rule context_conjI)
        apply(rename_tac k dx ex d n e d' e')(*strict*)
        apply(rule cfgRM.derivation_take_preserves_derivation)
        apply(force)
       apply(rename_tac k dx ex d n e d' e')(*strict*)
       apply(clarsimp)
       apply(simp add: derivation_take_def)
       apply(rule_tac
      x="length (foldl (@) [] (rev (take k \<pi>s1)))"
      in exI)
       apply(clarsimp)
      apply(rename_tac k dx ex d n e d' e')(*strict*)
      apply(simp add: cfgRM.derivation_from_to_def)
      apply(simp add: cfgRM.derivation_from_def)
      apply(simp add: cfgRM.derivation_to_def)
      apply(rule context_conjI)
       apply(rename_tac k dx ex d n e d' e')(*strict*)
       apply(rule cfgRM.derivation_take_preserves_derivation)
       apply(force)
      apply(rename_tac k dx ex d n e d' e')(*strict*)
      apply(clarsimp)
      apply(simp add: derivation_take_def)
      apply(simp add: option_to_list_def)
      apply(rule_tac
      x="n"
      in exI)
      apply(clarsimp)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(rule_tac
      x="(derivation_append (derivation_map (derivation_take d' n) (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>)) (derivation_map (derivation_take dx (length (foldl (@) [] (rev (take k \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws1 ! k)\<rparr>)) n)"
      in exI)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(rule conjI)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(simp add: cfgRM.derivation_from_to_def)
   apply(simp add: cfgRM.derivation_from_def)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(subgoal_tac "liftB (foldl (@) [] (take k ws1)) @ liftB (ws1 ! k) = liftB (foldl (@) [] (take (Suc k) ws1))")
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   prefer 2
   apply(rule_tac
      t="liftB (foldl (@) [] (take k ws1)) @ liftB (ws1 ! k)"
      and s="liftB ((foldl (@) [] (take k ws1)) @ (ws1 ! k))"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="foldl (@) [] (take k ws1) @ ws1 ! k"
      and s="foldl (@) [] (take (Suc k) ws1)"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply (metis Suc_le_lessD foldl_tail)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(subgoal_tac "foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ [prod_rhs r ! k]= foldl (@) [] (take (Suc k) (map (\<lambda>x. [x]) (prod_rhs r)))")
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   prefer 2
   apply(rule rhs_hlp)
   apply(force)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(rule conjI)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule cfgRM.derivation_belongs)
      apply(rename_tac k dx ex d n e d' e')(*strict*)
      apply(force)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule_tac
      t="foldl (@) [] (take (Suc k) (map (\<lambda>x. [x]) (prod_rhs r)))"
      and s="take (Suc k) (prod_rhs r)"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply(rule take_split)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="r"
      in ballE)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(clarsimp)
    apply(simp add: cfg_configurations_def)
    apply(rule conjI)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply(rule_tac
      B="setA (prod_rhs r)"
      in subset_trans)
      apply(rename_tac k dx ex d n e d' e')(*strict*)
      apply(rule set_subset_to_setA_subset)
      apply(rule List.set_take_subset)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule_tac
      B="setB (prod_rhs r)"
      in subset_trans)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply(rule set_subset_to_setB_subset)
     apply(rule List.set_take_subset)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(simp add: cfgRM.derivation_from_to_def)
   apply(simp add: cfgRM.derivation_from_def)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(rule conjI)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(case_tac "n")
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(clarsimp)
    apply(rename_tac k dx ex d d')(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rename_tac k dx ex d n e d' e' nat)(*strict*)
   apply(rule_tac
      t="derivation_append (derivation_map (derivation_take d' n) (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>)) (derivation_map (derivation_take dx (length (foldl (@) [] (rev (take k \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws1 ! k)\<rparr>)) n 0"
      and s=" derivation_map (derivation_take d' n) (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>) 0 "
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' nat)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rename_tac k dx ex d n e d' e' nat)(*strict*)
   apply(rule_tac
      t="derivation_map (derivation_take d' n) (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>) 0"
      and s="derivation_map (d') (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>) 0"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' nat)(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rename_tac k dx ex d n e d' e' nat)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(subgoal_tac " length (foldl (@) [] (rev (take (Suc k) \<pi>s1))) = length (foldl (@) [] (rev (take k \<pi>s1))) + n ")
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   prefer 2
   apply(rule_tac
      t="take (Suc k) \<pi>s1"
      and s="take k \<pi>s1 @ [\<pi>s1!k]"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule sym)
    apply(rule take_nth_split)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="rev (take k \<pi>s1 @ [\<pi>s1 ! k])"
      and s=" [\<pi>s1 ! k] @ (rev (take k \<pi>s1))"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="foldl (@) [] ([\<pi>s1 ! k] @ rev (take k \<pi>s1))"
      and s=" (foldl (@) [] ([\<pi>s1 ! k])) @(foldl (@) [] (rev (take k \<pi>s1))) "
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule foldl_distrib_append)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="length (foldl (@) [] [\<pi>s1 ! k] @ foldl (@) [] (rev (take k \<pi>s1)))"
      and s=" (length (foldl (@) [] [\<pi>s1 ! k])) + (length (foldl (@) [] (rev (take k \<pi>s1)))) "
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(subgoal_tac "length (foldl (@) [] [\<pi>s1 ! k]) = n")
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="\<pi>s1 ! k"
      and s="map the (get_labels d n)"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(rule conjI)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      x="if (length (foldl (@) [] (rev (take k \<pi>s1))))=0 then e' else ex"
      in exI)
   apply(case_tac "(length (foldl (@) [] (rev (take k \<pi>s1))))")
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(clarsimp)
    apply(rename_tac k dx d e d' e')(*strict*)
    apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
   apply(rename_tac k dx ex d n e d' e' nat)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def derivation_map_def derivation_take_def)
  apply(rename_tac k dx ex d n e d' e')(*strict*)
  apply(rule listEqI)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(clarsimp)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="take (Suc k) \<pi>s1"
      and s="take k \<pi>s1 @ [\<pi>s1!k]"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule sym)
    apply(rule take_nth_split)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="rev (take k \<pi>s1 @ [\<pi>s1 ! k])"
      and s=" [\<pi>s1 ! k] @ (rev (take k \<pi>s1))"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="foldl (@) [] ([\<pi>s1 ! k] @ rev (take k \<pi>s1))"
      and s=" (foldl (@) [] ([\<pi>s1 ! k])) @(foldl (@) [] (rev (take k \<pi>s1))) "
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule foldl_distrib_append)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="length (foldl (@) [] (map (CFGlm2rm G) ([\<pi>s1 ! k] @ rev (take k \<pi>s1))))"
      and s="length (foldl (@) [] (([\<pi>s1 ! k] @ rev (take k \<pi>s1))))"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule length_foldl_map)
    apply(rename_tac k dx ex d n e d' e' a)(*strict*)
    apply(rule sym)
    apply(subgoal_tac "\<exists>i<length \<pi>s1. a=\<pi>s1!i")
     apply(rename_tac k dx ex d n e d' e' a)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(erule disjE)
      apply(rename_tac k dx ex d n e d' e' a)(*strict*)
      apply(rule_tac
      x="k"
      in exI)
      apply(force)
     apply(rename_tac k dx ex d n e d' e' a)(*strict*)
     apply(subgoal_tac "\<exists>i<length(take k \<pi>s1). (take k \<pi>s1)!i=a")
      apply(rename_tac k dx ex d n e d' e' a)(*strict*)
      prefer 2
      apply (metis in_set_conv_nth)
     apply(rename_tac k dx ex d n e d' e' a)(*strict*)
     apply(erule exE)+
     apply(rename_tac k dx ex d n e d' e' a i)(*strict*)
     apply(rule_tac
      x="i"
      in exI)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' a)(*strict*)
    apply(clarsimp)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(erule_tac
      x="i"
      in allE)
    apply(erule impE)
     apply(rename_tac k dx ex d n e d' e' i)(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(erule exE)+
    apply(rename_tac k dx ex d n e d' e' i da)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac k dx ex d n e d' e' i da na)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
    apply(rule_tac
      t="\<pi>s1!i"
      and s="(map the (get_labels da na))"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
     apply(simp add: get_labels_def)
    apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
    apply(rule_tac
      t="length (CFGlm2rm G (map the (get_labels da na)))"
      and s="na"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
     apply(rule CFGlm2rm_preserves_length)
         apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
         apply(force)
        apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
        apply(force)
       apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
       apply(force)
      apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
      apply(simp add: option_to_list_def)
     apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac k dx ex d n e d' e' i da na ea)(*strict*)
    apply(simp add: get_labels_def)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="foldl (@) [] ([\<pi>s1 ! k] @ rev (take k \<pi>s1))"
      and s=" (foldl (@) [] ([\<pi>s1 ! k])) @(foldl (@) [] (rev (take k \<pi>s1))) "
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule foldl_distrib_append)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="length (foldl (@) [] [\<pi>s1 ! k] @ foldl (@) [] (rev (take k \<pi>s1)))"
      and s="length (foldl (@) [] [\<pi>s1 ! k]) + length (foldl (@) [] (rev (take k \<pi>s1)))"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(rule_tac
      t="length (foldl (@) [] [\<pi>s1 ! k])"
      and s="n"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule_tac
      t="foldl (@) [] [\<pi>s1 ! k]"
      and s="\<pi>s1 ! k"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule_tac
      t="\<pi>s1!k"
      and s="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n)"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n))"
      and s="length (nat_seq (Suc 0) n)"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac k dx ex d n e d' e')(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) ((length (foldl (@) [] (rev (take k \<pi>s1))) + n))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac k dx ex d n e d' e')(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac k dx ex d n e d' e')(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) ((length (foldl (@) [] (rev (take k \<pi>s1))) + n))) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(subgoal_tac "length (get_labels (derivation_append (derivation_map (derivation_take d' n) (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>)) (derivation_map (derivation_take dx (length (foldl (@) [] (rev (take k \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws1 ! k)\<rparr>)) n) (length (foldl (@) [] (rev (take k \<pi>s1))) + n)) = (length (foldl (@) [] (rev (take k \<pi>s1))) + n)")
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(simp add: get_labels_def)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(clarsimp)
  apply(thin_tac "length (get_labels (derivation_append (derivation_map (derivation_take d' n) (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>)) (derivation_map (derivation_take dx (length (foldl (@) [] (rev (take k \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws1 ! k)\<rparr>)) n) (length (foldl (@) [] (rev (take k \<pi>s1))) + n)) = length (foldl (@) [] (rev (take k \<pi>s1))) + n")
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(simp add: get_labels_def)
  apply(rule_tac
      t="map (\<lambda>i. get_label (derivation_append (derivation_map (derivation_take d' n) (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>)) (derivation_map (derivation_take dx (length (foldl (@) [] (rev (take k \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws1 ! k)\<rparr>)) n i)) (nat_seq (Suc 0) (length (foldl (@) [] (rev (take k \<pi>s1))) + n)) ! i"
      and s=" (\<lambda>i. get_label (derivation_append (derivation_map (derivation_take d' n) (\<lambda>v. \<lparr>cfg_conf = foldl (@) [] (take k (map (\<lambda>x. [x]) (prod_rhs r))) @ cfg_conf v\<rparr>)) (derivation_map (derivation_take dx (length (foldl (@) [] (rev (take k \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws1 ! k)\<rparr>)) n i)) ((nat_seq (Suc 0) (length (foldl (@) [] (rev (take k \<pi>s1))) + n)) ! i)"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(rule nth_map)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) ((length (foldl (@) [] (rev (take k \<pi>s1))) + n)) ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(clarsimp)
  apply(thin_tac "nat_seq (Suc 0) (length (foldl (@) [] (rev (take k \<pi>s1))) + n) ! i = Suc i")
  apply(rule_tac
      t="take (Suc k) \<pi>s1"
      and s="take k \<pi>s1 @ [\<pi>s1!k]"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(rule sym)
   apply(rule take_nth_split)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(rule_tac
      t="rev (take k \<pi>s1 @ [\<pi>s1 ! k])"
      and s=" [\<pi>s1 ! k] @ (rev (take k \<pi>s1))"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(rule_tac
      t="map (CFGlm2rm G) ([\<pi>s1 ! k] @ rev (take k \<pi>s1))"
      and s=" (map (CFGlm2rm G) ([\<pi>s1 ! k])) @ (map (CFGlm2rm G) (rev (take k \<pi>s1)))"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (map (CFGlm2rm G) [\<pi>s1 ! k] @ map (CFGlm2rm G) (rev (take k \<pi>s1)))"
      and s=" (foldl (@) [] (map (CFGlm2rm G) [\<pi>s1 ! k])) @ (foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s1))))"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(rule foldl_distrib_append)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (map (CFGlm2rm G) [\<pi>s1 ! k])"
      and s="CFGlm2rm G (\<pi>s1!k)"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(subgoal_tac "length (foldl (@) [] (rev (take (Suc k) \<pi>s1))) = n + (length (foldl (@) [] (rev (take k \<pi>s1))))")
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   prefer 2
   apply(rule_tac
      t="take (Suc k) \<pi>s1"
      and s="take k \<pi>s1 @ [\<pi>s1!k]"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(rule sym)
    apply(rule take_nth_split)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(rule_tac
      t="rev (take k \<pi>s1 @ [\<pi>s1 ! k])"
      and s=" [\<pi>s1 ! k] @ (rev (take k \<pi>s1))"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(rule_tac
      t="map (CFGlm2rm G) ([\<pi>s1 ! k] @ rev (take k \<pi>s1))"
      and s=" (map (CFGlm2rm G) ([\<pi>s1 ! k])) @ (map (CFGlm2rm G) (rev (take k \<pi>s1)))"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(rule_tac
      t="foldl (@) [] ([\<pi>s1 ! k] @ rev (take k \<pi>s1))"
      and s=" (foldl (@) [] ([\<pi>s1 ! k])) @(foldl (@) [] (rev (take k \<pi>s1))) "
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(rule foldl_distrib_append)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(rule_tac
      t="length (foldl (@) [] [\<pi>s1 ! k] @ foldl (@) [] (rev (take k \<pi>s1)))"
      and s="length (foldl (@) [] [\<pi>s1 ! k]) + length (foldl (@) [] (rev (take k \<pi>s1)))"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(rule_tac
      t="length (foldl (@) [] [\<pi>s1 ! k])"
      and s="n"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(rule_tac
      t="foldl (@) [] [\<pi>s1 ! k]"
      and s="\<pi>s1 ! k"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e' i)(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(rule_tac
      t="\<pi>s1!k"
      and s="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n)"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e' i)(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n))"
      and s="length (nat_seq (Suc 0) n)"
      in ssubst)
     apply(rename_tac k dx ex d n e d' e' i)(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac k dx ex d n e d' e' i)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac k dx ex d n e d' e' i)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i)(*strict*)
  apply(clarsimp)
  apply(case_tac "(length (foldl (@) [] (rev (take k \<pi>s1))))")
   apply(rename_tac k dx ex d n e d' e' i)(*strict*)
   apply(clarsimp)
   apply(rename_tac k dx d e d' e' i)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) 0 = []")
    apply(rename_tac k dx d e d' e' i)(*strict*)
    prefer 2
    apply (metis nat_seqEmpty zero_less_Suc)
   apply(rename_tac k dx d e d' e' i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(derivation_append (derivation_map (derivation_take d' (length (foldl (@) [] (rev (take (Suc k) \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take k ws1)) @ cfg_conf v\<rparr>)) (derivation_map (derivation_take dx 0) (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB (ws1 ! k)\<rparr>)) (length (foldl (@) [] (rev (take (Suc k) \<pi>s1)))) (Suc i))"
      and s="derivation_map (derivation_take d' (length (foldl (@) [] (rev (take (Suc k) \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take k ws1)) @ cfg_conf v\<rparr>) (Suc i)"
      in ssubst)
    apply(rename_tac k dx d e d' e' i)(*strict*)
    apply(simp add: derivation_append_def)
   apply(rename_tac k dx d e d' e' i)(*strict*)
   apply(rule_tac
      t="get_label (derivation_map (derivation_take d' (length (foldl (@) [] (rev (take (Suc k) \<pi>s1))))) (\<lambda>v. \<lparr>cfg_conf = liftB (foldl (@) [] (take k ws1)) @ cfg_conf v\<rparr>) (Suc i))"
      and s="get_label ((derivation_take d' (length (foldl (@) [] (rev (take (Suc k) \<pi>s1))))) (Suc i))"
      in ssubst)
    apply(rename_tac k dx d e d' e' i)(*strict*)
    apply(simp add: derivation_map_def derivation_take_def get_label_def)
    apply(case_tac "d' (Suc i)")
     apply(rename_tac k dx d e d' e' i)(*strict*)
     apply(force)
    apply(rename_tac k dx d e d' e' i a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac k dx d e d' e' i a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac k dx d e d' e' i)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) (length (foldl (@) [] (rev (take (Suc k) \<pi>s1)))) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac k dx d e d' e' i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac k dx d e d' e' i)(*strict*)
     apply(force)
    apply(rename_tac k dx d e d' e' i)(*strict*)
    apply(force)
   apply(rename_tac k dx d e d' e' i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def derivation_take_def get_label_def)
  apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "Suc i\<le>n")
   apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: derivation_map_def derivation_take_def get_label_def)
   apply(subgoal_tac "\<exists>e c. d' (Suc i) = Some(pair (Some e) c)")
    apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="n"
      in cfgRM.pre_some_position_is_some_position_prime)
       apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
       apply(force)
      apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
      apply(force)
     apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="(map (the \<circ> (\<lambda>i. case d' i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e)) (nat_seq (Suc 0) n) @ foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s1)))) ! i"
      and s="(map (the \<circ> (\<lambda>i. case d' i of None \<Rightarrow> None | Some (pair e c) \<Rightarrow> e)) (nat_seq (Suc 0) n)) ! i"
      in ssubst)
    apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) n ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' i nat ea c)(*strict*)
   apply(clarsimp)
  apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSm + 1 - SSn" for SSm SSn)
   apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
  apply(rule_tac
      t="(map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) n) @ foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s1)))) ! i"
      and s="(foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s1)))) ! (i-length(map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) n)))"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def)
  apply(simp add: derivation_map_def derivation_take_def get_label_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>k. n+Suc k=Suc i")
   apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
   prefer 2
   apply(rule_tac
      x="Suc i-n-Suc 0"
      in exI)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac k dx ex d n e d' e' nat ka)(*strict*)
  apply(subgoal_tac "\<exists>k. ka+Suc k=Suc nat")
   apply(rename_tac k dx ex d n e d' e' nat ka)(*strict*)
   prefer 2
   apply(rule_tac
      x="Suc nat-ka-Suc 0"
      in exI)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' nat ka)(*strict*)
  apply(clarsimp)
  apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
  apply(rule_tac
      t="foldl (@) [] (map (CFGlm2rm G) (rev (take k \<pi>s1)))"
      and s="map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (dx i))) (nat_seq (Suc 0) (Suc (ka + kb)))"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
  apply(rule_tac
      t="map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (dx i))) (nat_seq (Suc 0) (Suc (ka + kb))) ! ka"
      and s="((the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (dx i))) ((nat_seq (Suc 0) (Suc (ka + kb))) ! ka))"
      in ssubst)
   apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
   apply(rule nth_map)
   apply(subgoal_tac "length (nat_seq (Suc 0) (Suc (ka + kb))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc(ka+kb)) ! ka = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dx (Suc ka) = Some(pair (Some e) c)")
   apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (ka + kb)"
      in cfgRM.pre_some_position_is_some_position_prime)
      apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
      apply(force)
     apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
     apply(force)
    apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
    apply(force)
   apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
   apply(force)
  apply(rename_tac k dx ex d n e d' e' ka kb)(*strict*)
  apply(clarsimp)
  done

lemma lemma_4_11: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d1
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> cfgLM.belongs G d1
  \<Longrightarrow> cfgLM.belongs G d2
  \<Longrightarrow> d1 0 = Some (pair None \<lparr>cfg_conf=[A]\<rparr>)
  \<Longrightarrow> d2 0 = Some (pair None \<lparr>cfg_conf=[A]\<rparr>)
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=liftB w\<rparr>)
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=liftB w\<rparr>)
  \<Longrightarrow> CFGlm2rm G (map the (get_labels d1 n1)) = CFGlm2rm G (map the (get_labels d2 n2))
  \<Longrightarrow> map the (get_labels d1 n1) = map the (get_labels d2 n2)"
  apply(subgoal_tac "n1=n2")
   prefer 2
   apply(rule_tac
      t="n1"
      and s="length(CFGlm2rm G (map the (get_labels d1 n1)))"
      in subst)
    apply(rule CFGlm2rm_preserves_length)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rule_tac
      t="n2"
      and s="length(CFGlm2rm G (map the (get_labels d2 n2)))"
      in subst)
    apply(rule CFGlm2rm_preserves_length)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
   prefer 2
   apply(rule_tac
      d="d1"
      in lemma_4_9)
        apply(force)+
  apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
   prefer 2
   apply(rule_tac
      d="d2"
      in lemma_4_9)
        apply(force)+
  apply(clarsimp)
  apply(rename_tac d' e')(*strict*)
  apply(induct n2 arbitrary: d1 d2 e1 e2 w A rule: less_induct)
  apply(rename_tac x d' e' d1 d2 e1 e2 w A)(*strict*)
  apply(case_tac x)
   apply(rename_tac x d' e' d1 d2 e1 e2 w A)(*strict*)
   apply(thin_tac "\<And>y d' e' d1 d2 e1 e2 w A. y < x \<Longrightarrow> valid_cfg G \<Longrightarrow> cfgLM.derivation G d1 \<Longrightarrow> cfgLM.derivation G d2 \<Longrightarrow> cfgLM.belongs G d1 \<Longrightarrow> cfgLM.belongs G d2 \<Longrightarrow> d1 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> d2 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> d1 y = Some (pair e1 \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> d2 y = Some (pair e2 \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> CFGlm2rm G (map the (get_labels d1 y)) = map the (get_labels d' y) \<Longrightarrow> cfgRM.derivation G d' \<Longrightarrow> cfgLM.belongs G d' \<Longrightarrow> d' 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> CFGlm2rm G (map the (get_labels d2 y)) = map the (get_labels d' y) \<Longrightarrow> d' y = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> map the (get_labels d1 y) = map the (get_labels d2 y)")
   apply(rename_tac x d' e' d1 d2 e1 e2 w A)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' d1 d2 w A)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "nat_seq (Suc 0) 0 = []")
    apply(rename_tac d' d1 d2 w A)(*strict*)
    apply(clarsimp)
   apply(rename_tac d' d1 d2 w A)(*strict*)
   apply (metis nat_seqEmpty zero_less_Suc)
  apply(rename_tac x d' e' d1 d2 e1 e2 w A nat)(*strict*)
  apply(rename_tac n2)
  apply(rename_tac x d' e' d1 d2 e1 e2 w A n2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 0 = Some (pair e1 c1) \<and> SSd (Suc SSi) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSi)
   apply(rename_tac x d' e' d1 d2 e1 e2 w A n2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n2"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x d' e' d1 d2 e1 e2 w A n2)(*strict*)
     apply(force)
    apply(rename_tac x d' e' d1 d2 e1 e2 w A n2)(*strict*)
    apply(force)
   apply(rename_tac x d' e' d1 d2 e1 e2 w A n2)(*strict*)
   apply(force)
  apply(rename_tac x d' e' d1 d2 e1 e2 w A n2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 0 = Some (pair e1 c1) \<and> SSd (Suc SSi) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSi)
   apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n2"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r e2b c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r e2b c2a la ra)(*strict*)
  apply(case_tac la)
   apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r e2b c2a la ra)(*strict*)
   prefer 2
   apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r e2b c2a la ra a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w A n2 e2a c2 l r e2b c2a la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a c2 l r e2b c2a)(*strict*)
  apply(case_tac l)
   apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a c2 l r e2b c2a)(*strict*)
   prefer 2
   apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a c2 l r e2b c2a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a c2 l r e2b c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a c2 e2b c2a)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a c2 e2b c2a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a c2 e2b)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a c2 e2b cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 e2a e2b)(*strict*)
  apply(rename_tac r1 r2)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 r1 r2)(*strict*)
  apply(case_tac n2)
   apply(rename_tac d' e' d1 d2 e1 e2 w n2 r1 r2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' e' d1 d2 w r1 r2)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc 0) = [Suc 0]")
    apply(rename_tac d' e' d1 d2 w r1 r2)(*strict*)
    apply(clarsimp)
    apply(simp add: get_label_def)
   apply(rename_tac d' e' d1 d2 w r1 r2)(*strict*)
   apply (metis natUptTo_n_n)
  apply(rename_tac d' e' d1 d2 e1 e2 w n2 r1 r2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n)(*strict*)
  apply(simp add: get_labels_def)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc (Suc n)) = Suc 0 # (nat_seq (Suc (Suc 0)) (Suc (Suc n)))")
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   prefer 2
   apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(the (get_label (Some (pair (Some r1) \<lparr>cfg_conf = prod_rhs r1\<rparr>)))) = r1")
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   prefer 2
   apply(simp add: get_label_def)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(clarsimp)
  apply(thin_tac "the (get_label (Some (pair (Some r1) \<lparr>cfg_conf = prod_rhs r1\<rparr>))) = r1 ")
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(subgoal_tac "(the (get_label (Some (pair (Some r2) \<lparr>cfg_conf = prod_rhs r2\<rparr>)))) = r2")
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   prefer 2
   apply(simp add: get_label_def)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(clarsimp)
  apply(thin_tac "the (get_label (Some (pair (Some r2) \<lparr>cfg_conf = prod_rhs r2\<rparr>))) = r2 ")
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(subgoal_tac "CFGlm2rm SSG (r1 # SSrenPIprime) = (let \<pi>s = SOME \<pi>s. foldl (@) [] \<pi>s = SSrenPIprime \<and> length \<pi>s = length (prod_rhs SSr) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators SSG (Some (prod_rhs SSr ! i))) in SSr # foldl (@) [] (map (CFGlm2rm SSG) (rev \<pi>s)))" for SSrenPIprime SSr SSG)
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   prefer 2
   apply(rule CFGlm2rm.psimps)
   apply(rule CFGlm2rm_terminates)
         apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
    apply(simp add: get_label_def)
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(subgoal_tac "CFGlm2rm SSG (r2 # SSrenPIprime) = (let \<pi>s = SOME \<pi>s. foldl (@) [] \<pi>s = SSrenPIprime \<and> length \<pi>s = length (prod_rhs SSr) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators SSG (Some (prod_rhs SSr ! i))) in SSr # foldl (@) [] (map (CFGlm2rm SSG) (rev \<pi>s)))" for SSrenPIprime SSr SSG)
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   prefer 2
   apply(rule CFGlm2rm.psimps)
   apply(rule CFGlm2rm_terminates)
         apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
        apply(thin_tac "cfgLM.derivation G d1")
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
    apply(simp add: get_label_def)
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(simp add: Let_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d' 0 = Some (pair e1 c1) \<and> SSd (Suc SSi) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSi)
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (Suc n)"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w r1 r2 n x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2 l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2 l r)(*strict*)
   prefer 2
   apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2 l r a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2)(*strict*)
  apply(thin_tac "prod_lhs (the (get_label (Some (pair (Some e2a) c2)))) = prod_lhs e2a")
  apply(subgoal_tac "the (get_label (Some (pair (Some e2a) c2))) = e2a")
   apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2)(*strict*)
   prefer 2
   apply(simp add: get_label_def)
  apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "the (get_label (Some (pair (Some e2a) c2))) = e2a")
  apply(case_tac x)
   apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2 nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2 nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n x e2a c2 nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n e2a c2 nata)(*strict*)
  apply(rename_tac r c2 m)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r c2 m)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r c2 m cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
  apply(subgoal_tac "Suc (Suc 0) \<le> Suc (Suc m) \<and> Suc (Suc m) \<le> Suc (Suc n)")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
   prefer 2
   apply (metis less_eq_Suc_le_raw nat_seq_in_interval)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>\<pi>s. (\<pi>s=(SOME \<pi>s. SSP \<pi>s)) \<and> SSP \<pi>s" for SSP)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
   prefer 2
   apply(rule_tac
      P="\<lambda>\<pi>s. foldl (@) [] \<pi>s = map (the \<circ> (\<lambda>i. get_label (d1 i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i)))"
      in someI_existence)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
   apply(subgoal_tac "\<exists>\<pi>s ws. foldl (@) [] \<pi>s = SSrenPI \<and> length \<pi>s = length SSrenALPHA \<and> foldl (@) [] ws = SSw \<and> length ws = length SSrenALPHA \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'. cfgLM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSrenALPHA ! i\<rparr>) \<and> d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>s ! i = map the (get_labels d' n'))" for SSrenPI SSrenALPHA SSw SSG)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
    prefer 2
    apply(rule_tac
      e="e1"
      and n="Suc n"
      and d="derivation_drop d1 (Suc 0)"
      and \<alpha>="map (\<lambda>x. [x]) (prod_rhs r)"
      in lemma_4_6_existence)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
        apply(rule cfgLM.derivation_drop_preserves_derivation_prime)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
       apply(rule cfgLM.derivation_drop_preserves_belongs)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
      apply(simp add: derivation_drop_def)
      apply(rule sym)
      apply(rule split_string_into_single_item_strings)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
     apply(simp add: derivation_drop_def)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
   apply(erule exE)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s)(*strict*)
   apply(rule_tac
      x="\<pi>s"
      in exI)
   apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws)(*strict*)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws)(*strict*)
    apply(simp add: get_labels_def)
    apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws)(*strict*)
    apply(rule listEqI)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws)(*strict*)
     apply(clarsimp)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
    apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
    apply(simp add: derivation_drop_def)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i)(*strict*)
   apply(simp add: CFGlmEliminators_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s ws i d'a n' e'a)(*strict*)
   apply(rule_tac
      x="d'a"
      in exI)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      x="n'"
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m)(*strict*)
  apply(erule exE)+
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s)(*strict*)
  apply(subgoal_tac "foldl (@) [] (map (CFGlm2rm G) (rev \<pi>s)) = map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s)(*strict*)
  apply(thin_tac "foldl (@) [] (map (CFGlm2rm G) (rev (SOME \<pi>s. foldl (@) [] \<pi>s = map (the \<circ> (\<lambda>i. get_label (d1 i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i)))))) = map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s)(*strict*)
  apply(erule conjE)+
  apply(thin_tac "\<pi>s = (SOME \<pi>s. foldl (@) [] \<pi>s = map (the \<circ> (\<lambda>i. get_label (d1 i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s)(*strict*)
  apply(rename_tac \<pi>s1)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
  apply(subgoal_tac "\<exists>\<pi>s. (\<pi>s=(SOME \<pi>s. SSP \<pi>s)) \<and> SSP \<pi>s" for SSP)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
   prefer 2
   apply(rule_tac
      P="\<lambda>\<pi>s. foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d2 a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i)))"
      in someI_existence)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
   apply(subgoal_tac "\<exists>\<pi>s ws. foldl (@) [] \<pi>s = SSrenPI \<and> length \<pi>s = length SSrenALPHA \<and> foldl (@) [] ws = SSw \<and> length ws = length SSrenALPHA \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'. cfgLM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSrenALPHA ! i\<rparr>) \<and> d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>s ! i = map the (get_labels d' n'))" for SSrenPI SSrenALPHA SSw SSG)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
    prefer 2
    apply(rule_tac
      e="e2"
      and n="Suc n"
      and d="derivation_drop d2 (Suc 0)"
      and \<alpha>="map (\<lambda>x. [x]) (prod_rhs r)"
      in lemma_4_6_existence)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
        apply(rule cfgLM.derivation_drop_preserves_derivation_prime)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
       apply(rule cfgLM.derivation_drop_preserves_belongs)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
      apply(simp add: derivation_drop_def)
      apply(rule sym)
      apply(rule split_string_into_single_item_strings)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
     apply(simp add: derivation_drop_def)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
   apply(erule exE)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s)(*strict*)
   apply(rule_tac
      x="\<pi>s"
      in exI)
   apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws)(*strict*)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws)(*strict*)
    apply(simp add: get_labels_def)
    apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws)(*strict*)
    apply(rule listEqI)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws)(*strict*)
     apply(clarsimp)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
    apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
    apply(simp add: derivation_drop_def)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i)(*strict*)
   apply(simp add: CFGlmEliminators_def)
   apply(erule_tac
      x="i"
      in allE)+
   apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s ws i d d'a na n' e w e'a)(*strict*)
   apply(rule_tac
      x="d'a"
      in exI)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(rule_tac
      x="n'"
      in exI)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1)(*strict*)
  apply(erule exE)+
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s)(*strict*)
  apply(subgoal_tac "foldl (@) [] (map (CFGlm2rm G) (rev \<pi>s)) = map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s)(*strict*)
  apply(thin_tac "foldl (@) [] (map (CFGlm2rm G) (rev (SOME \<pi>s. foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d2 a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i)))))) = map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s)(*strict*)
  apply(erule conjE)+
  apply(thin_tac "\<pi>s = (SOME \<pi>s. foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d2 a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs r) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))))")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s)(*strict*)
  apply(rename_tac \<pi>s2)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
  apply(subgoal_tac "\<exists>k\<le>(length \<pi>s1). (\<forall>i<k. \<not> SSP i) \<and> SSP k" for SSP)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
   prefer 2
   apply(rule_tac
      P="\<lambda>n. Suc m \<le> length (foldl (@) [] (take n \<pi>s1))"
      in ex_least_nat_le_prime)
   apply(rule_tac
      t="take (length \<pi>s1) \<pi>s1"
      and s="\<pi>s1"
      in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
   apply(rule_tac
      t="foldl (@) [] \<pi>s1"
      and s="map (the \<circ> (\<lambda>i. get_label (d1 i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
      in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
  apply(case_tac k)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 nat)(*strict*)
  apply(rename_tac k)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
  apply(erule_tac
      x="k"
      and P="\<lambda>x. x < Suc k \<longrightarrow> \<not> Suc m \<le> length (foldl (@) [] (take x \<pi>s1))"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>!ws. length \<pi>s1 = length ws \<and> (\<forall>k<length \<pi>s1. \<exists>d n e. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some ((prod_rhs r) ! k))\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>) \<and> \<pi>s1 ! k = map the (get_labels d n))")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
   prefer 2
   apply(rule unique_existence_of_elimination_string_list)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
  apply(subgoal_tac "\<exists>!ws. length \<pi>s2 = length ws \<and> (\<forall>k<length \<pi>s2. \<exists>d n e. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some ((prod_rhs r) ! k))\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>) \<and> \<pi>s2 ! k = map the (get_labels d n))")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
   prefer 2
   apply(rule unique_existence_of_elimination_string_list)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k)(*strict*)
  apply(thin_tac "\<forall>i<length (prod_rhs r). \<pi>s1 ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))")
  apply(thin_tac "\<forall>i<length (prod_rhs r). \<pi>s2 ! i \<in> CFGlmEliminators G (Some (prod_rhs r ! i))")
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws wsa)(*strict*)
  apply(rename_tac ws1 ws2)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(subgoal_tac "foldl (@) [] ws1 = w")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>s="\<pi>s1"
      and n="Suc n"
      and G="G"
      and d="derivation_drop d1 (Suc 0)"
      in unique_elimination)
           apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
           apply(force)
          apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
          apply(rule cfgLM.derivation_drop_preserves_derivation_prime)
           apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
           apply(force)
          apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
          apply(force)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
         apply(rule cfgLM.derivation_drop_preserves_belongs)
           apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
           apply(force)
          apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
          apply(force)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
        apply(simp add: derivation_drop_def)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       apply(simp add: derivation_drop_def)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(rule_tac
      t="foldl (@) [] \<pi>s1"
      and s="map (\<lambda>a. the (get_label (d1 a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
      in ssubst)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSm + 1 - SSn" for SSm SSn)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       prefer 2
       apply(rule nat_seq_length_prime)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       prefer 2
       apply(rule nat_seq_length_prime)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(rule listEqI)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
       apply(rule nat_seq_nth_compute)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
      apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
       apply(rule nat_seq_nth_compute)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
      apply(simp add: derivation_drop_def get_label_def)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(subgoal_tac "foldl (@) [] ws2 = w")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>s="\<pi>s2"
      and n="Suc n"
      and G="G"
      and d="derivation_drop d2 (Suc 0)"
      in unique_elimination)
           apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
           apply(force)
          apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
          apply(rule cfgLM.derivation_drop_preserves_derivation_prime)
           apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
           apply(force)
          apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
          apply(force)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
         apply(rule cfgLM.derivation_drop_preserves_belongs)
           apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
           apply(force)
          apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
          apply(force)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
        apply(simp add: derivation_drop_def)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       apply(simp add: derivation_drop_def)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(rule_tac
      t="foldl (@) [] \<pi>s2"
      and s="map (\<lambda>a. the (get_label (d2 a))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
      in ssubst)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSm + 1 - SSn" for SSm SSn)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       prefer 2
       apply(rule nat_seq_length_prime)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       prefer 2
       apply(rule nat_seq_length_prime)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(rule listEqI)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
      apply(clarsimp)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
      apply(rule_tac
      t="nat_seq (Suc 0) (Suc n) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
       apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
       apply(rule nat_seq_nth_compute)
        apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
      apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
       apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
       apply(rule nat_seq_nth_compute)
        apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
      apply(simp add: derivation_drop_def get_label_def)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(thin_tac "\<forall>y y'. length ws1 = length y \<and> (\<forall>k<length ws1. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (y ! k)\<rparr>)) \<and> \<pi>s1 ! k = map the (get_labels d n))) \<and> length ws1 = length y' \<and> (\<forall>k<length ws1. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (y' ! k)\<rparr>)) \<and> \<pi>s1 ! k = map the (get_labels d n))) \<longrightarrow> y = y'")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(thin_tac "\<forall>y y'. length ws1 = length y \<and> (\<forall>k<length ws1. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (y ! k)\<rparr>)) \<and> \<pi>s2 ! k = map the (get_labels d n))) \<and> length ws1 = length y' \<and> (\<forall>k<length ws1. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (y' ! k)\<rparr>)) \<and> \<pi>s2 ! k = map the (get_labels d n))) \<longrightarrow> y = y'")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(subgoal_tac "\<pi>s1=\<pi>s2")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(subgoal_tac "foldl (@) [] (map (\<lambda>x. CFGlm2rm G x) (rev \<pi>s1)) = foldl (@) [] (map (\<lambda>x. CFGlm2rm G x) (rev \<pi>s2))")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(subgoal_tac "\<exists>dx ex. cfgRM.derivation G dx \<and> cfgRM.belongs G dx \<and> dx 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] (map (\<lambda>x. [x]) (prod_rhs r))\<rparr>) \<and> dx (Suc n) = Some (pair ex \<lparr>cfg_conf = liftB w\<rparr>) \<and> map the (get_labels dx (Suc n)) = foldl (@) [] (map (CFGlm2rm G) (rev \<pi>s1)) ")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>dx ex. cfgRM.derivation G dx \<and> cfgLM.belongs G dx \<and> dx 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] (take SSk (map (\<lambda>x. [x]) (prod_rhs r)))\<rparr>) \<and> dx (length (foldl (@) [] (rev(take SSk \<pi>s1)))) = Some (pair ex \<lparr>cfg_conf = liftB (foldl (@) [] (take SSk ws1))\<rparr>) \<and> map the (get_labels dx (length (foldl (@) [] (rev(take SSk \<pi>s1))))) = foldl (@) [] (map (CFGlm2rm G) (rev (take SSk \<pi>s1)))" for SSk)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
    prefer 2
    apply(rule_tac
      k="length \<pi>s1"
      in lemma_4_11_hlp)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   apply(erule exE)+
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule_tac
      x="dx"
      in exI)
   apply(rule_tac
      x="ex"
      in exI)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(subgoal_tac "take (length \<pi>s1) ws1 = ws1")
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(subgoal_tac "foldl (@) [] (map (\<lambda>x. [x]) (prod_rhs r)) = prod_rhs r")
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    prefer 2
    apply(metis split_string_into_single_item_strings)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(clarsimp)
   apply(thin_tac "foldl (@) [] (map (\<lambda>x. [x]) (prod_rhs r)) = prod_rhs r")
   apply(subgoal_tac "Suc n=length (foldl (@) [] (rev \<pi>s1))")
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule_tac
      t="length (foldl (@) [] (rev \<pi>s1))"
      and s="length (foldl (@) [] (\<pi>s1))"
      in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply (metis length_foldl_rev)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule_tac
      t="(foldl (@) [] \<pi>s1)"
      and s="map (the \<circ> (\<lambda>i. get_label (d1 i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
      in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(subgoal_tac "map (CFGlm2rm G) (\<pi>s1) = map (CFGlm2rm G) (\<pi>s2) \<and> ws1=ws2")
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
   prefer 2
   apply(erule exE)+
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(erule conjE)+
   apply(rule_tac
      G="G"
      and d="dx"
      and \<alpha>="map (\<lambda>x. [x]) (prod_rhs r)"
      and n="Suc n"
      and e="ex"
      and w="w"
      in lemma_4_7_uniqueness)
          apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
          apply(force)
         apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(rule_tac
      t="rev (map (CFGlm2rm G) (\<pi>s1))"
      and s="map (CFGlm2rm G) (rev (\<pi>s1))"
      in ssubst)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
     apply(rule rev_map)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(rule conjI)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(rule conjI)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(rule conjI)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(rule conjI)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(rule_tac
      t="length (map (CFGlm2rm G) \<pi>s1)"
      and s="length (\<pi>s1)"
      in ssubst)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(rule allI)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i)(*strict*)
    apply(rule impI)
    apply(erule_tac
      x="i"
      and P="\<lambda>i. i < length ws1 \<longrightarrow> (\<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! i))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws1 ! i)\<rparr>)) \<and> \<pi>s1 ! i = map the (get_labels d n)))"
      in allE)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
    apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
     prefer 2
     apply(rule_tac
      w="ws1 ! i"
      and e="e"
      and n="na"
      and A="prod_rhs r ! i"
      and d="d"
      in lemma_4_9)
          apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
          apply(force)
         apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
         apply(force)
        apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
        apply(force)
       apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
       apply(rule_tac
      t="[prod_rhs r ! i]"
      and s="option_to_list (Some (prod_rhs r ! i))"
      in ssubst)
        apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
        apply(simp (no_asm) add: option_to_list_def)
       apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
    apply(erule exE)+
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e d'a e'a)(*strict*)
    apply(erule conjE)+
    apply(simp add: option_to_list_def)
    apply(rule_tac
      x="d'a"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="na"
      in exI)
    apply(clarsimp)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule_tac
      t="rev (map (CFGlm2rm G) (\<pi>s2))"
      and s="map (CFGlm2rm G) (rev (\<pi>s2))"
      in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(rule rev_map)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule conjI)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule_tac
      t="length (map (CFGlm2rm G) \<pi>s2)"
      and s="length (\<pi>s2)"
      in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex)(*strict*)
   apply(rule allI)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i)(*strict*)
   apply(rule impI)
   apply(erule_tac
      x="i"
      and P="\<lambda>i. i < length ws1 \<longrightarrow> (\<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! i))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws2 ! i)\<rparr>)) \<and> \<pi>s2 ! i = map the (get_labels d n)))"
      in allE)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
  apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
  apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
  prefer 2
  apply(rule_tac
    w="ws2 ! i"
    and e="e"
    and n="na"
    and A="prod_rhs r ! i"
    and d="d"
    in lemma_4_9)
       apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
       apply(force)
      apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
    apply(rule_tac
    t="[prod_rhs r ! i]"
    and s="option_to_list (Some (prod_rhs r ! i))"
    in ssubst)
     apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
     apply(simp (no_asm) add: option_to_list_def)
    apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e)(*strict*)
  apply(erule exE)+
  apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws1 ws2 dx ex i d na e d'a e'a)(*strict*)
  apply(erule conjE)+
  apply(simp add: option_to_list_def)
  apply(rule_tac
    x="d'a"
    in exI)
  apply(clarsimp)
  apply(rule_tac
    x="na"
    in exI)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(rule listEqI)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(rule impI)
  apply(subgoal_tac "CFGlm2rm G (\<pi>s1!i) = CFGlm2rm G (\<pi>s2!i)")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  prefer 2
  apply(rule_tac
    t="CFGlm2rm G (\<pi>s1!i)"
    and s="(map (CFGlm2rm G) \<pi>s1)!i"
    in subst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(rule nth_map)
  apply(rule_tac
    t="CFGlm2rm G (\<pi>s2!i)"
    and s="(map (CFGlm2rm G) \<pi>s2)!i"
    in subst)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
   apply(rule nth_map)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(subgoal_tac "ws1!i=ws2!i")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  prefer 2
  apply(rule_tac
    f="\<lambda>x. x!i"
    in arg_cong)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(erule_tac
    x="i"
    and P="\<lambda>i. i < length ws1 \<longrightarrow> (\<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! i))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws1 ! i)\<rparr>)) \<and> \<pi>s1 ! i = map the (get_labels d n)))"
    in allE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(erule_tac
    x="i"
    in allE)
  apply(erule_tac
    Q="(\<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (prod_rhs r ! i))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws1 ! i)\<rparr>)) \<and> \<pi>s1 ! i = map the (get_labels d n)))"
    and P="i < length ws1"
    in impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(erule impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i)(*strict*)
  apply(erule exE)+
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i dx d da ex)(*strict*)
  apply(rename_tac d xd1 xd2 ex)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex na nb)(*strict*)
  apply(erule conjE)+
  apply(rename_tac n1 n2)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2)(*strict*)
  apply(erule exE)+
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 e ea)(*strict*)
  apply(rename_tac ex1 ex2)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
  apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
  prefer 2
  apply(rule_tac
    w="ws1 ! i"
    and e="ex1"
    and n="n1"
    and A="prod_rhs r ! i"
    and d="xd1"
    in lemma_4_9)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
   apply(rule_tac
    t="[prod_rhs r ! i]"
    and s="option_to_list (Some (prod_rhs r ! i))"
    in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
    apply(simp (no_asm) add: option_to_list_def)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2)(*strict*)
  apply(erule exE)+
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "n1=n2")
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  prefer 2
  apply(rule_tac
    t="n1"
    and s="length (CFGlm2rm G (map the (get_labels xd1 n1)))"
    in subst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    e="ex1"
    and w="ws1!i"
    and A="prod_rhs r ! i"
    in CFGlm2rm_preserves_length)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply(rule_tac
    t="[prod_rhs r ! i]"
    and s="option_to_list (Some (prod_rhs r ! i))"
    in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
    apply(simp (no_asm) add: option_to_list_def)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="n2"
    and s="length (CFGlm2rm G (map the (get_labels xd2 n2)))"
    in subst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    e="ex2"
    and w="ws2!i"
    and A="prod_rhs r ! i"
    in CFGlm2rm_preserves_length)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply(rule_tac
    t="[prod_rhs r ! i]"
    and s="option_to_list (Some (prod_rhs r ! i))"
    in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
    apply(simp (no_asm) add: option_to_list_def)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="map the (get_labels xd1 n1)"
    and s="\<pi>s1!i"
    in ssubst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="CFGlm2rm G (\<pi>s1!i)"
    and s="(map (CFGlm2rm G) \<pi>s1)!i"
    in subst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule nth_map)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="map the (get_labels xd2 n2)"
    and s="\<pi>s2!i"
    in ssubst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="CFGlm2rm G (\<pi>s2!i)"
    and s="(map (CFGlm2rm G) \<pi>s2)!i"
    in subst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule nth_map)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(clarify)
  apply(erule_tac
    x="n2"
    in meta_allE)
  apply(erule_tac
    x="d'a"
    in meta_allE)
  apply(erule_tac
    x="e'a"
    in meta_allE)
  apply(erule_tac
    x="xd1"
    in meta_allE)
  apply(erule_tac
    x="xd2"
    in meta_allE)
  apply(erule_tac
    x="ex1"
    in meta_allE)
  apply(erule_tac
    x="ex2"
    in meta_allE)
  apply(erule_tac
    x="ws2!i"
    in meta_allE)
  apply(erule_tac
    x="prod_rhs r ! i"
    in meta_allE)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="n2"
    and s="length (CFGlm2rm G (map the (get_labels xd2 n2)))"
    in subst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    e="ex2"
    and w="ws2!i"
    and A="prod_rhs r ! i"
    in CFGlm2rm_preserves_length)
      apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
      apply(force)
     apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
     apply(force)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
    apply(force)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply(rule_tac
    t="[prod_rhs r ! i]"
    and s="option_to_list (Some (prod_rhs r ! i))"
    in ssubst)
    apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
    apply(simp (no_asm) add: option_to_list_def)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="map the (get_labels xd2 n2)"
    and s="\<pi>s2!i"
    in ssubst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    y="length(foldl (@) [] (map (CFGlm2rm G) (rev \<pi>s2)))"
    in le_less_trans)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="map (CFGlm2rm G) (rev \<pi>s2)"
    and s="rev(map (CFGlm2rm G) (\<pi>s2))"
    in subst)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply(rule rev_map)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="length (foldl (@) [] (rev (map (CFGlm2rm G) \<pi>s2)))"
    and s="length (foldl (@) [] ((map (CFGlm2rm G) \<pi>s2)))"
    in ssubst)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply (metis length_foldl_rev)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="CFGlm2rm G (\<pi>s2 ! i)"
    and s="(map (CFGlm2rm G) \<pi>s2)!i"
    in ssubst)
   apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
   apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply (rule length_shorter_than_in_composition)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="foldl (@) [] (map (CFGlm2rm G) (rev \<pi>s2))"
    and s="map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
    in ssubst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc n))) = SSm + 1 - SSn" for SSm SSn)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  prefer 2
  apply(rule nat_seq_length_prime)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="[prod_rhs r ! i]"
    and s="option_to_list (Some (prod_rhs r ! i))"
    in ssubst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(simp (no_asm) add: option_to_list_def)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule_tac
    t="[prod_rhs r ! i]"
    and s="option_to_list (Some (prod_rhs r ! i))"
    in ssubst)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(simp (no_asm) add: option_to_list_def)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(simp add: get_labels_def)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(simp add: get_labels_def)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(force)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(rule listEqI)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a)(*strict*)
  apply(simp add: get_labels_def)
  apply(rename_tac d' e' d1 d2 e1 e2 w n r m \<pi>s1 \<pi>s2 k ws1 ws2 i d xd1 xd2 ex n1 n2 ex1 ex2 d'a e'a ia)(*strict*)
  apply(clarsimp)
  apply(rename_tac d' e' d1 d2 e1 e2 n r m \<pi>s1 \<pi>s2 k ws2 i d xd1 xd2 ex n2 ex1 ex2 d'a e'a ia)(*strict*)
  apply(simp add: get_labels_def)
  done

lemma lemma_4_12_1: "
  valid_cfg G
  \<Longrightarrow> CFGrm_unambiguous G
  \<Longrightarrow> CFGlm_unambiguous G"
  apply(simp add: CFGrm_unambiguous_def CFGlm_unambiguous_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
  apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
   prefer 2
   apply(rule_tac
      A="teA (cfg_initial G)"
      and d="d1"
      in lemma_4_9)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
       apply(rule cfgLM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(rule cfgLM.derivation_initial_belongs)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
     apply(clarsimp)
     apply(case_tac "d1 0")
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w b)(*strict*)
     apply(simp add: cfg_initial_configurations_def)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
  apply(subgoal_tac "\<exists>d' e'. cfgRM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSA]\<rparr>) \<and> d' SSn = Some (pair e' \<lparr>cfg_conf = liftB SSw\<rparr>) \<and> CFGlm2rm SSG SSrenPI = map the (get_labels d' SSn)" for SSA SSw SSG SSrenPI SSn)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
   prefer 2
   apply(rule_tac
      A="teA (cfg_initial G)"
      and d="d2"
      in lemma_4_9)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
       apply(rule cfgLM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(rule cfgLM.derivation_initial_belongs)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
     apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d' e')(*strict*)
     apply(case_tac "d2 0")
      apply(rename_tac d1 d2 n1 n2 e1 e2 w d' e')(*strict*)
      apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d' e' a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d' e' a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d' e' b)(*strict*)
     apply(simp add: cfg_initial_configurations_def)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
  apply(erule_tac
      x="d'"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
   apply(rule cfgRM.derivation_initialI)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
  apply(erule_tac
      x="d'a"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
   apply(rule cfgRM.derivation_initialI)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d' d'a e' e'a)(*strict*)
  apply(erule_tac
      x="n1"
      in allE)
  apply(erule_tac
      x="n2"
      in allE)
  apply(erule_tac
      x="e'"
      in allE)
  apply(erule_tac
      x="e'a"
      in allE)
  apply(erule_tac
      x="w"
      in allE)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
  apply(subgoal_tac "n1=n2")
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(subgoal_tac "map the (get_labels d1 n1) = map the (get_labels d2 n2)")
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    prefer 2
    apply(rule_tac
      A="teA (cfg_initial G)"
      in lemma_4_11)
             apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
             apply(force)
            apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
            apply(rule cfgLM.derivation_initial_is_derivation)
            apply(force)
           apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
           apply(rule cfgLM.derivation_initial_is_derivation)
           apply(force)
          apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
          apply(rule cfgLM.derivation_initial_belongs)
           apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
           apply(force)
          apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
          apply(force)
         apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
         apply(rule cfgLM.derivation_initial_belongs)
          apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
          apply(force)
         apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
        apply(simp add: cfgLM.derivation_initial_def)
        apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e')(*strict*)
        apply(case_tac "d1 0")
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e')(*strict*)
         apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' a)(*strict*)
        apply(clarsimp)
        apply(case_tac a)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' a option b)(*strict*)
        apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' b)(*strict*)
        apply(simp add: cfg_initial_configurations_def)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
       apply(simp add: cfgLM.derivation_initial_def)
       apply(clarsimp)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e')(*strict*)
       apply(case_tac "d2 0")
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e')(*strict*)
        apply(clarsimp)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' a)(*strict*)
       apply(clarsimp)
       apply(case_tac a)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' a option b)(*strict*)
       apply(clarsimp)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' b)(*strict*)
       apply(simp add: cfg_initial_configurations_def)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e')(*strict*)
   apply(rule ext)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
   apply(case_tac "x\<le>n2")
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(rule_tac
      n="n2"
      and ?m1.0="0"
      and ?m2.0="0"
      in equal_labels_implies_equal_cfgLMderivation)
           apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
           apply(force)
          apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
          apply(rule cfgLM.derivation_initial_is_derivation)
          apply(force)
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
         apply(rule cfgLM.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
        apply(simp add: cfgLM.derivation_initial_def)
        apply(clarsimp)
        apply(case_tac "d1 0")
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
         apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a)(*strict*)
        apply(case_tac "d2 0")
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a)(*strict*)
         apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a aa)(*strict*)
        apply(case_tac a)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a aa option b)(*strict*)
        apply(case_tac aa)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x a aa option b optiona ba)(*strict*)
        apply(clarsimp)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x b ba)(*strict*)
        apply(simp add: cfg_initial_configurations_def)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
   apply(rule_tac
      t="d1 x"
      and s="None"
      in ssubst)
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(rule_tac
      n="n2"
      in cfgLM_no_step_from_no_nonterminal)
         apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
         apply(force)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
        apply(rule cfgLM.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(rule cfgLM.derivation_initial_belongs)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
     apply(clarsimp)
     apply(rule setA_liftB)
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
   apply(rule sym)
   apply(rule_tac
      n="n2"
      in cfgLM_no_step_from_no_nonterminal)
        apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(rule cfgLM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
      apply(rule cfgLM.derivation_initial_belongs)
       apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
    apply(clarsimp)
    apply(rule setA_liftB)
   apply(rename_tac d1 d2 n2 e1 e2 w d'a e' x)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
  apply(case_tac "n1<n2")
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(subgoal_tac "d'a n2 = None")
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(rule_tac
      n="n1"
      in cfgRM_no_step_from_no_nonterminal)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(clarsimp)
    apply(rule setA_liftB)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
  apply(case_tac "n2<n1")
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(subgoal_tac "d'a n1 = None")
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(rule_tac
      n="n2"
      in cfgRM_no_step_from_no_nonterminal)
        apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
        apply(force)
       apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
       apply(force)
      apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
    apply(clarsimp)
    apply(rule setA_liftB)
   apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 n2 e1 e2 w d'a e' e'a)(*strict*)
  apply(force)
  done

lemma lemma_4_12: "
  valid_cfg G
  \<Longrightarrow> CFGlm_unambiguous G \<longleftrightarrow> CFGrm_unambiguous G"
  apply(metis lemma_4_12_1 lemma_4_12_2)
  done

end
