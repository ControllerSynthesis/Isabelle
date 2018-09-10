section {*I\_cfgSTD\_cfgLM*}
theory
  I_cfgSTD_cfgLM

imports
  I_cfgSTD
  I_cfgLM_misc

begin

lemma CFG_CFGLM_StepRelation: "
  cfgLM_step_relation M ca ea c
  \<Longrightarrow> cfgSTD_step_relation M ca ea c"
  apply(simp add: cfgSTD_step_relation_def cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(force)
  done

lemma cfgLM_derivations_are_cfg_derivations: "
  cfgLM.derivation G d
  \<Longrightarrow> cfgSTD.derivation G d"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule cfgLM.some_position_has_details_at_0)
   apply(blast)
  apply(simp add: cfgSTD.derivation_def)
  apply(auto)
  apply(rename_tac c i)(*strict*)
  apply(case_tac i)
   apply(rename_tac c i)(*strict*)
   apply(auto)
  apply(rename_tac c nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac c nat a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>c. d(Suc nat)\<noteq>Some (pair None c)")
   apply(rename_tac c nat a)(*strict*)
   prefer 2
   apply(rule cfgLM.derivation_Always_PreEdge)
   apply(blast)
  apply(rename_tac c nat a)(*strict*)
  apply(case_tac a)
  apply(rename_tac c nat a option b)(*strict*)
  apply(auto)
  apply(rename_tac c nat b y)(*strict*)
  apply(subgoal_tac "\<exists>e c. d nat = Some (pair e c)")
   apply(rename_tac c nat b y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac c nat b y)(*strict*)
     apply(blast)
    apply(rename_tac c nat b y)(*strict*)
    apply(blast)
   apply(rename_tac c nat b y)(*strict*)
   apply(force)
  apply(rename_tac c nat b y)(*strict*)
  apply(clarsimp)
  apply(rename_tac c nat b y e ca)(*strict*)
  apply(subgoal_tac "cfgLM_step_relation G ca y b")
   apply(rename_tac c nat b y e ca)(*strict*)
   prefer 2
   apply(rule cfgLM.position_change_due_to_step_relation)
     apply(rename_tac c nat b y e ca)(*strict*)
     apply(blast)+
  apply(rename_tac c nat b y e ca)(*strict*)
  apply(simp add: cfgSTD_step_relation_def cfgLM_step_relation_def)
  apply(auto)
  done

lemma cfg_derivation_can_be_translated_to_cfgLM_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w2\<rparr>)
  \<Longrightarrow> setA w2={}
  \<Longrightarrow> \<exists>d' e.
  cfgLM.derivation G d'
  \<and> maximum_of_domain d' n
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>)
  \<and> d' n = Some (pair e \<lparr>cfg_conf=w2\<rparr>)"
  apply(induct n arbitrary: d w1 w2 e rule: nat_less_induct)
  apply(rename_tac n d w1 w2 e)(*strict*)
  apply(case_tac n)
   apply(rename_tac n d w1 w2 e)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w2)(*strict*)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = w2\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w2)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac d w2)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w2)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac d w2)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac n d w1 w2 e nat)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac n d w1 w2 e nat)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac n d w1 w2 e nat)(*strict*)
     apply(force)
    apply(rename_tac n d w1 w2 e nat)(*strict*)
    apply(force)
   apply(rename_tac n d w1 w2 e nat)(*strict*)
   apply(force)
  apply(rename_tac n d w1 w2 e nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w1 w2 e nat ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d w1 w2 e nat ea c cfg_conf)(*strict*)
  apply(rename_tac w1')
  apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> ea \<lparr>cfg_conf = w1'\<rparr>")
   apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
   prefer 2
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
    apply(force)
   apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
   apply(force)
  apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d w2 e nat ea l r)(*strict*)
  apply(rename_tac d w2 e1 n e2 l r)
  apply(rename_tac d w2 e1 n e2 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac d w2 e1 n e2 l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac d w2 e1 n e2 l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = l\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w@r\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w2 \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1 + n2 = n")
   apply(rename_tac d w2 e1 n l r A w)(*strict*)
   prefer 2
   apply(rule_tac
      d="derivation_drop d (Suc 0)"
      in derivationCanBeDecomposed2)
    apply(rename_tac d w2 e1 n l r A w)(*strict*)
    apply(rule_tac
      m = "n"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
       apply(rename_tac d w2 e1 n l r A w)(*strict*)
       apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
       apply(rule conjI)
        apply(rename_tac d w2 e1 n l r A w)(*strict*)
        apply(blast)
       apply(rename_tac d w2 e1 n l r A w)(*strict*)
       apply(rule_tac
      x="Suc n"
      in exI)
  apply(rule conjI)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(blast)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(force)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(rule derivation_drop_preserves_generates_maximum_of_domain)
  apply(blast)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa)(*strict*)
  apply(case_tac "d1 0")
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa a)(*strict*)
  apply(case_tac "d2 0")
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa)(*strict*)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = r\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w2 \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1 + n2 = na")
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  prefer 2
  apply(rule_tac
      d="d2"
      in derivationCanBeDecomposed2)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(rule_tac
      x="na"
      in exI)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(case_tac "d1a 0")
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa a)(*strict*)
  apply(case_tac "d2a 0")
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(subgoal_tac "n2=n1a+n2a")
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  prefer 2
  apply(rule_tac
      d="d2"
      in cfgSTD.maximum_of_domainUnique)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(thin_tac "cfgSTD.derivation G d")
  apply(thin_tac "maximum_of_domain d (Suc (n1 + n2))")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = l @ teA A # r\<rparr>)")
  apply(thin_tac "d (Suc (n1 + n2)) = Some (pair e1 \<lparr>cfg_conf = w1 @ w1' @ w2'\<rparr>)")
  apply(thin_tac "d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) \<lparr>cfg_conf = l @ w @ r\<rparr>)")
  apply(thin_tac "maximum_of_domain d2 n2")
  apply(thin_tac "cfgSTD.derivation G d2")
  apply(thin_tac "d2 (Suc (n1a + n2a)) = None")
  apply(thin_tac "d2 (n1a + n2a) = Some (pair e3 \<lparr>cfg_conf = w1' @ w2'\<rparr>)")
  apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = w @ r\<rparr>)")
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(subgoal_tac "na=n1a")
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  prefer 2
  apply(rule_tac
      d="d1a"
      in cfgSTD.maximum_of_domainUnique)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(subgoal_tac "nb=n2a")
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  prefer 2
  apply(rule_tac
      d="d2a"
      in cfgSTD.maximum_of_domainUnique)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(subgoal_tac "n1=n")
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  prefer 2
  apply(rule_tac
      d="d1"
      in cfgSTD.maximum_of_domainUnique)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(force)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(force)
  apply(rename_tac l r A w d1 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(thin_tac "d1 (Suc n1)=None")
  apply(thin_tac "d2 (Suc n2)=None")
  apply(thin_tac "d3 (Suc n3)=None")
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(subgoal_tac "(\<exists>d1'. cfgLM.derivation G d1' \<and> maximum_of_domain d1' n1 \<and> d1' 0 = Some (pair None \<lparr>cfg_conf = l\<rparr>) \<and> (\<exists>e1'. d1' n1 = Some (pair e1' \<lparr>cfg_conf = w1\<rparr>)))")
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  prefer 2
  apply(erule_tac
      x="n1"
      in allE)
  apply(erule impE)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(clarsimp)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(subgoal_tac "(\<exists>d2'. cfgLM.derivation G d2' \<and> maximum_of_domain d2' n2 \<and> d2' 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>) \<and> (\<exists>e2'. d2' n2 = Some (pair e2' \<lparr>cfg_conf = w2\<rparr>)))")
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  prefer 2
  apply(erule_tac
      x="n2"
      in allE)
  apply(erule impE)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3 d1' e1')(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(subgoal_tac "(\<exists>d3'. cfgLM.derivation G d3' \<and> maximum_of_domain d3' n3 \<and> d3' 0 = Some (pair None \<lparr>cfg_conf = r\<rparr>) \<and> (\<exists>e3'. d3' n3 = Some (pair e3' \<lparr>cfg_conf = w3\<rparr>)))")
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  prefer 2
  apply(erule_tac
      x="n3"
      in allE)
  apply(erule impE)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(erule_tac
      x="d3"
      in allE)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3 d1' d2' e1' e2')(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac l r A w d1 w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(thin_tac "maximum_of_domain d1 n1")
  apply(thin_tac "cfgSTD.derivation G d1")
  apply(thin_tac "d1 n1 = Some (pair e1 \<lparr>cfg_conf = w1\<rparr>)")
  apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = l\<rparr>)")
  apply(thin_tac "maximum_of_domain d2 n2")
  apply(thin_tac "maximum_of_domain d3 n3")
  apply(thin_tac "cfgSTD.derivation G d2")
  apply(thin_tac "cfgSTD.derivation G d3")
  apply(thin_tac "d2 n2 = Some (pair e2 \<lparr>cfg_conf = w2\<rparr>)")
  apply(thin_tac "d3 n3 = Some (pair e3 \<lparr>cfg_conf = w3\<rparr>)")
  apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
  apply(thin_tac "d3 0 = Some (pair None \<lparr>cfg_conf = r\<rparr>)")
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(subgoal_tac "(\<exists>d2''. cfgLM.derivation G d2'' \<and> maximum_of_domain d2'' (Suc n2) \<and> d2'' 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>) \<and> (\<exists>e2''. d2'' (Suc n2) = Some (pair e2'' \<lparr>cfg_conf = w2\<rparr>)))")
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  prefer 2
  apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr> ) d2' (Suc 0)"
      in exI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule cfgLM.derivation_concat2)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule cfgLM.der2_is_derivation)
  apply(simp add: cfgLM_step_relation_def)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule der2_maximum_of_domain)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(blast)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(simp add: der2_def)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule_tac
      t="Suc n2"
      and s="Suc 0+n2"
      in ssubst)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule_tac concat_has_max_dom)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule der2_maximum_of_domain)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(thin_tac "d2' 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
  apply(thin_tac "maximum_of_domain d2' n2")
  apply(thin_tac "cfgLM.derivation G d2'")
  apply(thin_tac "d2' n2 = Some (pair e2' \<lparr>cfg_conf = w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(subgoal_tac "(\<exists>d23. cfgLM.derivation G d23 \<and> maximum_of_domain d23 (Suc n2+n3) \<and> d23 0 = Some (pair None \<lparr>cfg_conf = [teA A]@r\<rparr>) \<and> (\<exists>e23. d23 (Suc n2+n3) = Some (pair e23 \<lparr>cfg_conf = w2@w3\<rparr>)))")
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  prefer 2
  apply(rule_tac
      x="(derivation_append (derivation_map d2'' (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ r\<rparr>)) (derivation_map d3' (\<lambda>v. \<lparr>cfg_conf = w2 @ (cfg_conf v)\<rparr>)) (Suc n2))"
      in exI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule cfgLM.from_to_is_der)
  apply(rule_tac
      w1'="w2"
      and ?w2.0="r"
      and w2'="w3"
      in cfgLM_concatExtendIsFromToBoth)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule_tac
      x="Suc n2"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
  apply(rule_tac
      x="n3"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule concat_has_max_dom)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(thin_tac "cfgLM.derivation G d3'")
  apply(thin_tac "maximum_of_domain d3' n3")
  apply(thin_tac "d3' 0 = Some (pair None \<lparr>cfg_conf = r\<rparr>)")
  apply(thin_tac "d3' n3 = Some (pair e3' \<lparr>cfg_conf = w3\<rparr>)")
  apply(thin_tac "cfgLM.derivation G d2''")
  apply(thin_tac "maximum_of_domain d2'' (Suc n2)")
  apply(thin_tac "d2'' 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
  apply(thin_tac "d2'' (Suc n2) = Some (pair e2'' \<lparr>cfg_conf = w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule_tac
      x="(derivation_append (derivation_map d1' (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ ([teA A]@r)\<rparr>)) (derivation_map d23 (\<lambda>v. \<lparr>cfg_conf = w1@ (cfg_conf v)\<rparr>)) n1)"
      in exI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule cfgLM.from_to_is_der)
  apply(rule_tac
      w1'="w1"
      and ?w2.0="[teA A]@r"
      in cfgLM_concatExtendIsFromToBoth)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule_tac
      x="n1"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
  apply(rule_tac
      x="Suc (n2 +n3)"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule conjI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule_tac
      t="Suc (n1+(n2+n3))"
      and s="n1+Suc(n2+n3)"
      in ssubst)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule concat_has_max_dom)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  done

lemma CFG_lang_lm_lang_equal1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G \<supseteq> cfgLM.marked_language G"
  apply(simp add: cfgSTD.marked_language_def cfgLM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
  apply(rename_tac x d)(*strict*)
  apply(simp add: cfgLM.derivation_initial_def cfgSTD.derivation_initial_def)
  apply(rule cfgLM_derivations_are_cfg_derivations)
  apply(force)
  apply(rename_tac x d)(*strict*)
  apply(clarsimp)
  apply(rule cfgLM_derivations_are_cfg_derivations)
  apply(force)
  done

lemma CFG_lang_lm_lang_equal2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G \<subseteq> cfgLM.marked_language G"
  apply(simp add: cfgSTD.marked_language_def cfgLM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(case_tac "d 0")
  apply(rename_tac x d)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d b)(*strict*)
  apply(subgoal_tac "cfgSTD.belongs G d")
  apply(rename_tac x d b)(*strict*)
  prefer 2
  apply(rule cfgSTD.derivation_belongs)
  apply(rename_tac x d b)(*strict*)
  apply(force)
  apply(rename_tac x d b)(*strict*)
  apply(force)
  apply(rename_tac x d b)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(force)
  apply(rename_tac x d b)(*strict*)
  apply(force)
  apply(rename_tac x d b)(*strict*)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
  apply(rename_tac x d b)(*strict*)
  prefer 2
  apply(rule CFG_AcceptingDerivation_has_maximum_of_domain)
  apply(rename_tac x d b)(*strict*)
  apply(force)
  apply(rename_tac x d b)(*strict*)
  apply(force)
  apply(rename_tac x d b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d b n)(*strict*)
  apply(case_tac b)
  apply(rename_tac x d b n cfg_conf)(*strict*)
  apply(rename_tac w1)
  apply(rename_tac x d b n w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1)(*strict*)
  apply(subgoal_tac "\<exists>e w. SSd SSn = Some (pair e \<lparr>cfg_conf = w\<rparr>) \<and> setA w = {}" for SSd SSn)
  apply(rename_tac x d n w1)(*strict*)
  prefer 2
  apply(rule CFG_AcceptingDerivation_has_no_Nonterms_at_maximum_of_domain)
  apply(rename_tac x d n w1)(*strict*)
  apply(force)
  apply(rename_tac x d n w1)(*strict*)
  apply(force)
  apply(rename_tac x d n w1)(*strict*)
  apply(force)
  apply(rename_tac x d n w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 e w)(*strict*)
  apply(subgoal_tac "liftB x=w")
  apply(rename_tac x d n w1 e w)(*strict*)
  prefer 2
  apply(rule cfg_marked_effect_is_at_maximum_of_domain)
  apply(rename_tac x d n w1 e w)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e w)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e w)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e w)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 e)(*strict*)
  apply(subgoal_tac "\<exists>d' e. cfgLM.derivation SSG d' \<and> maximum_of_domain d' SSn \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSw1\<rparr>) \<and> d' SSn = Some (pair e \<lparr>cfg_conf = SSw2\<rparr>)" for SSG SSw1 SSn SSw2)
  apply(rename_tac x d n w1 e)(*strict*)
  prefer 2
  apply(rule cfg_derivation_can_be_translated_to_cfgLM_derivation)
  apply(rename_tac x d n w1 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 e d' ea)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(simp add: cfg_marked_effect_def cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d n w1 e d' ea eb i c ec ca ia)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n w1 e d' ea eb i c ec ca ia cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 e d' ea eb i ec ca ia)(*strict*)
  apply(simp add: cfgLM.derivation_initial_def)
  apply(rule conjI)
  apply(rename_tac x d n w1 e d' ea eb i ec ca ia)(*strict*)
  apply(rule_tac
      x="ea"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = liftB x\<rparr>"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(force)
  apply(rename_tac x d n w1 e d' ea eb i ec ca ia)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule_tac
      x="ea"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = liftB x\<rparr>"
      in exI)
  apply(clarsimp)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(simp add: cfg_configurations_def)
  apply(simp add: cfgSTD.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(simp add: cfg_configurations_def)
  done

lemma CFG_lang_lm_lang_equal: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G = cfgLM.marked_language G"
  apply(rule order_antisym)
  apply(rule CFG_lang_lm_lang_equal2)
  apply(force)
  apply(rule CFG_lang_lm_lang_equal1)
  apply(force)
  done

lemma CFGLM_to_CFG_derivation_initial: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> cfgSTD.derivation_initial G d"
  apply(simp add: cfgSTD.derivation_initial_def cfgLM.derivation_initial_def)
  apply(clarsimp)
  apply(rule cfgLM_derivations_are_cfg_derivations)
  apply(force)
  done

lemma construct_elimininating_derivation_prime: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> \<exists>d n e v.
  cfgLM.derivation G d
  \<and> d 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>)
  \<and> d n = Some (pair e \<lparr>cfg_conf=liftB v\<rparr>)"
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
  prefer 2
  apply(rule canElimCombine)
  apply(force)
  apply(force)
  apply(clarsimp)
  apply(rename_tac d w')(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def)
  apply(simp add: cfgSTD.derivation_to_def)
  apply(simp add: cfgSTD.derivation_from_def)
  apply(clarsimp)
  apply(rename_tac d w' n x)(*strict*)
  apply(case_tac "d 0")
  apply(rename_tac d w' n x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' n x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' n x)(*strict*)
  apply(subgoal_tac "\<exists>d' e. cfgLM.derivation G d' \<and> maximum_of_domain d' n \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>) \<and> d' n = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
  apply(rename_tac d w' n x)(*strict*)
  prefer 2
  apply(rule cfg_derivation_can_be_translated_to_cfgLM_derivation)
  apply(rename_tac d w' n x)(*strict*)
  apply(force)
  apply(rename_tac d w' n x)(*strict*)
  apply(force)
  apply(rename_tac d w' n x)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d w' n x)(*strict*)
  apply(force)
  apply(rename_tac d w' n x)(*strict*)
  apply(force)
  apply(rename_tac d w' n x)(*strict*)
  apply(force)
  apply(rename_tac d w' n x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' n x d' e)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="filterB w'"
      in exI)
  apply (metis liftBDeConv2)
  done

corollary cfgSTD_unmarked_in_cfgLM_unmarked: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD.unmarked_language G \<subseteq> cfgLM.unmarked_language G"
  apply(simp add: cfgSTD.unmarked_language_def cfgLM.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(simp add: cfg_unmarked_effect_def cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac x d e c i z)(*strict*)
  apply(erule_tac
      x="derivation_take d i"
      in allE)
  apply(erule impE)
  apply(rename_tac x d e c i z)(*strict*)
  apply (metis cfgSTD.derivation_take_preserves_derivation_initial)
  apply(rename_tac x d e c i z)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d e c i z cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
  apply(rename_tac x d e i z)(*strict*)
  apply (metis maximum_of_domain_derivation_take not_None_eq)
  apply(rename_tac x d e i z)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c)(*strict*)
  apply(subgoal_tac "\<exists>e c. dc xa = Some (pair e c)")
  apply(rename_tac x d e i z dc xa ia ea c)(*strict*)
  prefer 2
  apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c y)(*strict*)
  apply(case_tac y)
  apply(rename_tac x d e i z dc xa ia ea c y option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  prefer 2
  apply(rule_tac
      d="derivation_append (derivation_take d i) dc i"
      and n="i+xa"
      and e="if xa=0 then e else eb"
      and ?w2.0="if xa=0 then liftB x @ z else cfg_conf ca"
      in cfg_derivation_can_be_translated_to_cfgLM_derivation)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply (metis (full_types, hide_lams) cfgSTD.derivation_append_preserves_derivation_initial_prime cfgSTD.derivation_initial_def cfgSTD.derivation_take_preserves_derivation_initial maximum_of_domain_derivation_take option.distinct(1))
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply (metis concat_has_max_dom maximum_of_domain_derivation_take option.distinct(1))
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply(simp add: derivation_append_def derivation_take_def)
  apply(simp add: cfgSTD.derivation_initial_def cfgLM.derivation_initial_def cfg_marking_configuration_def cfg_initial_configurations_def)
  apply(case_tac c)
  apply(rename_tac x d e i z dc xa ia ea c eb ca cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea eb ca cfg_conf)(*strict*)
  apply(case_tac "d 0")
  apply(rename_tac x d e i z dc xa ia ea eb ca cfg_conf)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea eb ca cfg_conf a)(*strict*)
  apply(case_tac a)
  apply(rename_tac x d e i z dc xa ia ea eb ca cfg_conf a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea eb ca cfg_conf conf)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply(case_tac xa)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca)(*strict*)
  apply(simp add: derivation_append_def derivation_take_def)
  apply(rename_tac x d e i z dc xa ia ea c eb ca nat)(*strict*)
  apply(simp add: derivation_append_def derivation_take_def derivation_append_fit_def)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply(case_tac xa)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  prefer 2
  apply(rename_tac x d e i z dc xa ia ea c eb ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(simp add: derivation_append_def derivation_take_def derivation_append_fit_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(case_tac "ia<i")
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "False")
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d e i z dc ia ea c eb ca nat cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea eb ca nat cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x d e i z dc ia ea eb ca nat w)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d e i z dc ia ea eb ca nat w)(*strict*)
  prefer 2
  apply(rule_tac
      d="d"
      and n="ia"
      and m="i"
      in cfgSTD.step_detail_before_some_position)
  apply(rename_tac x d e i z dc ia ea eb ca nat w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea eb ca nat w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea eb ca nat w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea eb ca nat w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea eb ca nat w e2 c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea eb ca nat e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x d e i z dc ia ea eb ca nat e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea eb ca nat e2 l r)(*strict*)
  apply (metis elemInsetA empty_iff)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "ia=i")
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i z dc ea eb ca nat)(*strict*)
  apply(case_tac "dc 0")
  apply(rename_tac x d i z dc ea eb ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i z dc ea eb ca nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d i z dc ea eb ca nat a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i z dc ea eb ca nat option conf)(*strict*)
  apply(case_tac option)
  apply(rename_tac x d i z dc ea eb ca nat option conf)(*strict*)
  prefer 2
  apply(rename_tac x d i z dc ea eb ca nat option conf a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i z dc ea eb ca nat option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i z dc ea eb ca nat)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d i z dc ea eb ca nat)(*strict*)
  prefer 2
  apply(rule_tac
      d="dc"
      and n="0"
      and m="Suc nat"
      in cfgSTD.step_detail_before_some_position)
  apply(rename_tac x d i z dc ea eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d i z dc ea eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d i z dc ea eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d i z dc ea eb ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i z dc ea eb ca nat e2 c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x d i z dc ea eb ca nat e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x d i z dc ea eb ca nat e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i z dc ea eb ca nat e2 l r)(*strict*)
  apply (metis elemInsetA empty_iff)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "ia>i")
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "ia-i\<le>Suc nat")
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  prefer 2
  apply(rule_tac
      d="dc"
      and n="Suc nat"
      and m="ia-i"
      in cfgSTD.no_some_beyond_maximum_of_domain)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(case_tac "ia-i=Suc nat")
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  prefer 2
  apply(rule_tac
      d="dc"
      and n="ia-i"
      and m="Suc nat"
      in cfgSTD.step_detail_before_some_position)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea c eb ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca nat e2 c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca nat e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x d e i z dc ia ea c eb ca nat e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca nat e2 l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d e i z dc ia ea c eb ca nat e2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea eb ca nat e2 l r)(*strict*)
  apply (metis elemInsetA empty_iff)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca)(*strict*)
  apply(simp add: derivation_append_def derivation_take_def derivation_append_fit_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(case_tac eb)
  apply(rename_tac x d e i z dc ia ea c eb ca)(*strict*)
  prefer 2
  apply(rename_tac x d e i z dc ia ea c eb ca a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d e i z dc ia ea c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(case_tac "ia>i")
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      d="dc"
      and n="0"
      and m="ia-i"
      in cfgSTD.no_some_beyond_maximum_of_domain)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(clarsimp)
  apply(case_tac "i=ia")
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  prefer 2
  apply(rule_tac
      d="d"
      and n="ia"
      and m="i"
      in cfgSTD.step_detail_before_some_position)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc ia ea w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea w e2 c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x d e i z dc ia ea e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea e2 l r)(*strict*)
  apply (metis elemInsetA empty_iff)
  apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(simp add: cfgLM.derivation_initial_def)
  apply(rule conjI)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(rule_tac
      x="ec"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = if xa = 0 then liftB x @ z else cfg_conf ca\<rparr>"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc ia ea c eb ca d' ec)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(simp add: derivation_append_def derivation_take_def derivation_append_fit_def cfg_marking_configuration_def)
  apply(case_tac "dc 0")
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec option conf)(*strict*)
  apply(case_tac option)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec option conf)(*strict*)
  prefer 2
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec option conf a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  prefer 2
  apply(rule_tac
      d="dc"
      and i="0"
      and j="xa"
      in cfgSTD.derivation_monotonically_inc)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(force)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(case_tac ca)
  apply(rename_tac x d e i z dc xa ia ea c eb ca d' ec w cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z dc xa ia ea c eb d' ec w cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x d e i z dc xa ia ea c eb d' ec wa w)(*strict*)
  apply (metis HeadTerminal_can_be_removed_from_derivation)
  done

lemma cfgSTD_accessible_nonterminals_ALT_contained_in_cfgLM_accessible_nonterminals_hlp: "
  valid_cfg G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G
  \<Longrightarrow> ATS.derivation_initial cfg_initial_configurations
  cfgSTD_step_relation G d
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # w2\<rparr>)
  \<Longrightarrow> \<exists>d. ATS.derivation_initial cfg_initial_configurations
  cfgLM_step_relation G d \<and>
  (\<exists>n c. get_configuration (d n) = Some c \<and>
  (\<exists>w1 w2. cfg_conf c = w1 @ teA x # w2))"
  apply(induct n arbitrary: e w1 x w2)
  apply(rename_tac e w1 x w2)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def cfg_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac w1 x w2)(*strict*)
  apply(case_tac w1)
  apply(rename_tac w1 x w2)(*strict*)
  prefer 2
  apply(rename_tac w1 x w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 x w2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in exI)
  apply(rule conjI)
  apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def der1_def)
  apply(fold der1_def)
  apply(rule cfgLM.der1_is_derivation)
  apply(rule_tac
      x="0"
      in exI)
  apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def der1_def get_configuration_def)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(force)
  apply(rename_tac n e w1 x w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n e w1 x w2)(*strict*)
  prefer 2
  apply(rule_tac
      d="d"
      and n="n"
      and m="Suc n"
      in cfgSTD.step_detail_before_some_position)
  apply(rename_tac n e w1 x w2)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(force)
  apply(rename_tac n e w1 x w2)(*strict*)
  apply(force)
  apply(rename_tac n e w1 x w2)(*strict*)
  apply(force)
  apply(rename_tac n e w1 x w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 e2 c1)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 e2 c1 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n w1 x w2 e1 e2 c1 l r cfg_confa)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n w1 x w2 e1 e2 c1 l r cfg_confa prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac n w1 x w2 e1 e2 c1 l r cfg_confa A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 l r A w)(*strict*)
  apply(case_tac "x \<in> setA w")
  apply(rename_tac n w1 x w2 e1 l r A w)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="l"
      in meta_allE)
  apply(erule_tac
      x="A"
      in meta_allE)
  apply(erule_tac
      x="r"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 l r A w da na c w1a w2a)(*strict*)
  apply(case_tac c)
  apply(rename_tac n w1 x w2 e1 l r A w da na c w1a w2a cfg_confa)(*strict*)
  apply(case_tac "da na")
  apply(rename_tac n w1 x w2 e1 l r A w da na c w1a w2a cfg_confa)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac n w1 x w2 e1 l r A w da na c w1a w2a cfg_confa a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 l r A w da na w1a w2a a)(*strict*)
  apply(case_tac a)
  apply(rename_tac n w1 x w2 e1 l r A w da na w1a w2a a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 l r A w da na w1a w2a option)(*strict*)
  apply(fold get_configuration_def)
  apply(rename_tac e)
  apply(rename_tac n w1 x w2 e1 l r A w da na w1a w2a e)(*strict*)
  apply(thin_tac "cfgSTD.derivation_initial G d")
  apply(thin_tac "d (Suc n) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) \<lparr>cfg_conf = l @ w @ r\<rparr>)")
  apply(thin_tac "d n = Some (pair e1 \<lparr>cfg_conf = l @ teA A # r\<rparr>)")
  apply(rename_tac n w1 x w2 e1 l r A w d na w1a w2a e)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac n w1 x w2 e1 l r A w d na w1a w2a e)(*strict*)
  prefer 2
  apply(rule cfgLM_Nonblockingness_branching_implies_FB_iterated_elimination)
  apply(rename_tac n w1 x w2 e1 l r A w d na w1a w2a e)(*strict*)
  apply(force)
  apply(rename_tac n w1 x w2 e1 l r A w d na w1a w2a e)(*strict*)
  apply(force)
  apply(rename_tac n w1 x w2 e1 l r A w d na w1a w2a e)(*strict*)
  apply(force)
  apply(rename_tac n w1 x w2 e1 l r A w d na w1a w2a e)(*strict*)
  apply(force)
  apply(rename_tac n w1 x w2 e1 l r A w d na w1a w2a e)(*strict*)
  apply(force)
  apply(rename_tac n w1 x w2 e1 l r A w d na w1a w2a e)(*strict*)
  apply(thin_tac "d na = Some (pair e \<lparr>cfg_conf = w1a @ teA A # w2a\<rparr>)")
  apply(thin_tac "cfgLM.derivation_initial G d")
  apply(clarsimp)
  apply(rename_tac w1 x w2 l r A w d n c w1a w2a)(*strict*)
  apply(case_tac c)
  apply(rename_tac w1 x w2 l r A w d n c w1a w2a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a)(*strict*)
  apply(case_tac "d n")
  apply(rename_tac w1 x w2 l r A w d n w1a w2a)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = liftB w1a @ teA A # w2a\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = liftB w1a @ w @ w2a\<rparr>) n"
      in exI)
  apply(rule conjI)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(rule cfgLM.derivation_append_preserves_derivation_initial)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(force)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(force)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(rule cfgLM.derivation_append_preserves_derivation)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(simp add: cfgLM.derivation_initial_def)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(rule cfgLM.der2_is_derivation)
  apply(simp add: cfgLM_step_relation_def)
  apply(rule_tac
      x="liftB w1a"
      in exI)
  apply(rule_tac
      x="w2a"
      in exI)
  apply(clarsimp)
  apply(rule setA_liftB)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = liftB w1a @ w @ w2a\<rparr>"
      in exI)
  apply(rule conjI)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(subgoal_tac "X" for X)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  prefer 2
  apply(rule setA_elem_contained)
  apply(force)
  apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 x w2 l r A d n w1a w2a e w1b w2b)(*strict*)
  apply(rule_tac
      x="liftB w1a @ w1b"
      in exI)
  apply(force)
  apply(rename_tac n w1 x w2 e1 l r A w)(*strict*)
  apply(subgoal_tac "prefix (w1@[teA x]) l \<or> prefix l (w1@[teA x])")
  apply(rename_tac n w1 x w2 e1 l r A w)(*strict*)
  prefer 2
  apply(rule mutual_prefix_prefix)
  apply(force)
  apply(rename_tac n w1 x w2 e1 l r A w)(*strict*)
  apply(erule disjE)
  apply(rename_tac n w1 x w2 e1 l r A w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 l r A w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 l r A w c)(*strict*)
  apply(rule_tac
      xs="c"
      in rev_cases)
  apply(rename_tac n w1 x w2 e1 l r A w c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n w1 x w2 e1 l r A w c ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x w2 e1 l r A w ys)(*strict*)
  apply(subgoal_tac "prefix (ys@[teA x]) w \<or> prefix w (ys@[teA x])")
  apply(rename_tac n x w2 e1 l r A w ys)(*strict*)
  prefer 2
  apply(rule mutual_prefix_prefix)
  apply(force)
  apply(rename_tac n x w2 e1 l r A w ys)(*strict*)
  apply(erule disjE)
  apply(rename_tac n x w2 e1 l r A w ys)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac n x e1 l r A ys c)(*strict*)
  apply(simp add: setAConcat)
  apply(rename_tac n x w2 e1 l r A w ys)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac n x w2 e1 l r A w ys c)(*strict*)
  apply(rule_tac
      xs="c"
      in rev_cases)
  apply(rename_tac n x w2 e1 l r A w ys c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 l r A ys)(*strict*)
  apply(simp add: setAConcat)
  apply(rename_tac n x w2 e1 l r A w ys c ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x w2 e1 l A w ysa)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x=" l @ teA A # ysa"
      in meta_allE)
  apply(clarsimp)
  done

lemma cfgSTD_accessible_nonterminals_ALT_contained_in_cfgLM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD_accessible_nonterminals_ALT G \<subseteq> cfgLM_accessible_nonterminals G"
  apply(simp add: cfgSTD_accessible_nonterminals_ALT_def cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2)(*strict*)
  apply(case_tac "d n")
  apply(rename_tac x d n w1 w2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac x d n w1 w2 a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac x d n w1 w2 a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 option)(*strict*)
  apply(thin_tac "x \<in> cfg_nonterminals G")
  apply(fold get_configuration_def)
  apply(rename_tac e)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  prefer 2
  apply(rule cfgSTD_accessible_nonterminals_ALT_contained_in_cfgLM_accessible_nonterminals_hlp)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 e da na c w1a w2a)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n w1 w2 e da na c w1a w2a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 e da na w1a w2a)(*strict*)
  apply(case_tac "da na")
  apply(rename_tac x d n w1 w2 e da na w1a w2a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac x d n w1 w2 e da na w1a w2a a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac x d n w1 w2 e da na w1a w2a a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option)(*strict*)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option)(*strict*)
  prefer 2
  apply(rule cfgLM_Nonblockingness_branching_implies_FB_iterated_elimination)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option)(*strict*)
  apply(force)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option db nb c w1b w2b)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option db nb c w1b w2b cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option db nb w1b w2b)(*strict*)
  apply(rule_tac
      x="db"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="nb"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = liftB w1b @ teA x # w2b\<rparr>"
      in exI)
  apply(clarsimp)
  apply(case_tac "db nb")
  apply(rename_tac x d n w1 w2 e da na w1a w2a option db nb w1b w2b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option db nb w1b w2b a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option db nb w1b w2b a optiona conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 e da na w1a w2a option db nb w1b w2b optiona)(*strict*)
  apply(rule_tac
      x="w1b"
      in exI)
  apply(clarsimp)
  done

lemma cfgLM_Nonblockingness_branching_to_cfgSTD_Nonblockingness_branching_hlp: "
       valid_cfg G \<Longrightarrow>
       cfgLM.Nonblockingness_branching G \<Longrightarrow>
       ATS.derivation_initial cfg_initial_configurations
        cfgSTD_step_relation G dh \<Longrightarrow>
       maximum_of_domain dh n \<Longrightarrow>
       dh n = Some (pair e \<lparr>cfg_conf = w\<rparr>) \<Longrightarrow>
       \<exists>dc. cfgSTD.derivation G dc \<and>
            cfgLM.belongs G dc \<and>
            Ex (maximum_of_domain dc) \<and>
            derivation_append_fit dh dc n \<and>
            cfg_marking_condition G (derivation_append dh dc n)"
  apply(induct "length(filterA w)" arbitrary: dh n e w)
  apply(rename_tac w dh n e)(*strict*)
  apply(subgoal_tac "\<exists>wx. liftB wx = w")
  apply(rename_tac w dh n e)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB w"
      in exI)
  apply(rule liftBDeConv2)
  apply(rule filterA_setA)
  apply(force)
  apply(rename_tac w dh n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB wx\<rparr>"
      in exI)
  apply(rule conjI)
  apply(rename_tac dh n e wx)(*strict*)
  apply (metis cfgSTD.der1_is_derivation)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule cfgSTD.der1_belongs)
  apply(rule cfgSTD.belongs_configurations)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply (metis der1_maximum_of_domain)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx)(*strict*)
  apply(simp add: derivation_append_fit_def der1_def)
  apply(rename_tac dh n e wx)(*strict*)
  apply(simp add: cfg_marking_condition_def derivation_append_def der1_def cfg_marking_configuration_def)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(simp add: setA_liftB)
  apply(rule cfgSTD.belongs_configurations)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(subgoal_tac "\<exists>wx1 A wx2. w = wx1 @[teA A]@liftB wx2")
  apply(rename_tac x w dh n e)(*strict*)
  prefer 2
  apply(rule filterA_gt_0_then_rm_nonterminal)
  apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(subgoal_tac "A \<in> cfgLM_Nonblockingness_nonterminals G")
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  prefer 2
  apply(rule_tac
      A="cfgLM_accessible_nonterminals G"
      in set_mp)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule cfgLM_Nonblockingness_branching_implies_cfgLM_accessible_nonterminals_contained_in_cfgLM_Nonblockingness_nonterminals)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule_tac
      A="cfgSTD_accessible_nonterminals_ALT G"
      in set_mp)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule cfgSTD_accessible_nonterminals_ALT_contained_in_cfgLM_accessible_nonterminals)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: cfgSTD_accessible_nonterminals_ALT_def)
  apply(subgoal_tac "\<lparr>cfg_conf = wx1 @ teA A # liftB wx2\<rparr> \<in> cfg_configurations G")
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  prefer 2
  apply(rule cfgSTD.belongs_configurations)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule conjI)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: cfg_configurations_def setAConcat)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule_tac
      x="dh"
      in exI)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: cfgLM_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
  apply(case_tac na)
  apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w' nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' nat)(*strict*)
  apply(rename_tac na)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule_tac
      x="wx1@ w' @ liftB wx2"
      in meta_allE)
  apply(erule_tac
      x="derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf=wx1@(cfg_conf c)@liftB wx2\<rparr>)) n) (n+Suc na)"
      in meta_allE)
  apply(erule_tac
      x="n+Suc na"
      in meta_allE)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(erule meta_impE)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule setA_empty_filterA_empty)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule cfgSTD.derivation_take_preserves_derivation_initial)
  apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule cfgSTD.derivation_append_preserves_derivation)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule cfgSTD.derivation_map_preserves_derivation)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply (metis cfgLM_derivations_are_cfg_derivations)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na i eb c)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2 l r)(*strict*)
  apply(rule_tac
      x="wx1 @ l"
      in exI)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule maximum_of_domain_derivation_take)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(simp add: derivation_take_def derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      x="derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf=wx1@(cfg_conf c)@liftB wx2\<rparr>)) dc (Suc na)) (Suc na+x)"
      in exI)
  apply(rule context_conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule cfgSTD.derivation_take_preserves_derivation)
  apply(rule cfgSTD.derivation_append_preserves_derivation)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule cfgSTD.derivation_map_preserves_derivation)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply (metis cfgLM_derivations_are_cfg_derivations)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x i eb c)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2 l r)(*strict*)
  apply(rule_tac
      x="wx1 @ l"
      in exI)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(simp add: derivation_map_def)
  apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
  apply(case_tac "dc 0")
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
  apply(case_tac option)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule cfgSTD.derivation_belongs)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      d="dh"
      in cfgLM.belongs_configurations)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      x="(Suc na + x)"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def derivation_append_fit_def derivation_take_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(subgoal_tac "(derivation_append (derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf = wx1 @ cfg_conf c @ liftB wx2\<rparr>)) n) (Suc (n + na))) dc (Suc (n + na))) = (derivation_append dh (derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf = wx1 @ cfg_conf c @ liftB wx2\<rparr>)) dc (Suc na)) (Suc na + x)) n)")
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule ext)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def derivation_append_fit_def derivation_take_def)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "dc (xa - Suc (n + na))")
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(rule_tac
      d="dc"
      and n="x"
      and m="(xa - Suc (n + na))"
      in cfgSTD.no_some_beyond_maximum_of_domain)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  done

corollary cfgLM_Nonblockingness_branching_to_cfgSTD_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G"
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(case_tac "dh n")
  apply(rename_tac dh n)(*strict*)
  apply(simp add: maximum_of_domain_def get_configuration_def)
  apply(rename_tac dh n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac dh n a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac dh n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e c cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac dh n e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w)(*strict*)
  apply(rule cfgLM_Nonblockingness_branching_to_cfgSTD_Nonblockingness_branching_hlp)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  done

lemma cfgLM_Nonblockingness_branching_to_cfgSTD_Nonblockingness_branching_hlp_mod: "
       valid_cfg G \<Longrightarrow>
       cfgSTD_accessible_nonterminals_ALT G \<subseteq> cfgSTD_Nonblockingness_nonterminals G \<Longrightarrow>
       ATS.derivation_initial cfg_initial_configurations
        cfgSTD_step_relation G dh \<Longrightarrow>
       maximum_of_domain dh n \<Longrightarrow>
       dh n = Some (pair e \<lparr>cfg_conf = w\<rparr>) \<Longrightarrow>
       \<exists>dc. cfgSTD.derivation G dc \<and>
            cfgLM.belongs G dc \<and>
            Ex (maximum_of_domain dc) \<and>
            derivation_append_fit dh dc n \<and>
            cfg_marking_condition G (derivation_append dh dc n)"
  apply(induct "length(filterA w)" arbitrary: dh n e w)
  apply(rename_tac w dh n e)(*strict*)
  apply(subgoal_tac "\<exists>wx. liftB wx = w")
  apply(rename_tac w dh n e)(*strict*)
  prefer 2
  apply(rule_tac
      x="filterB w"
      in exI)
  apply(rule liftBDeConv2)
  apply(rule filterA_setA)
  apply(force)
  apply(rename_tac w dh n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB wx\<rparr>"
      in exI)
  apply(rule conjI)
  apply(rename_tac dh n e wx)(*strict*)
  apply (metis cfgSTD.der1_is_derivation)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule cfgSTD.der1_belongs)
  apply(rule cfgSTD.belongs_configurations)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply (metis der1_maximum_of_domain)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx)(*strict*)
  apply(simp add: derivation_append_fit_def der1_def)
  apply(rename_tac dh n e wx)(*strict*)
  apply(simp add: cfg_marking_condition_def derivation_append_def der1_def cfg_marking_configuration_def)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(simp add: setA_liftB)
  apply(rule cfgSTD.belongs_configurations)
  apply(rename_tac dh n e wx)(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx)(*strict*)
  apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(subgoal_tac "\<exists>wx1 A wx2. w = wx1 @[teA A]@liftB wx2")
  apply(rename_tac x w dh n e)(*strict*)
  prefer 2
  apply(rule filterA_gt_0_then_rm_nonterminal)
  apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(subgoal_tac "A \<in> cfgSTD_Nonblockingness_nonterminals G")
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  prefer 2
  apply(rule_tac
      A="cfgSTD_accessible_nonterminals_ALT G"
      in set_mp)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: cfgSTD_accessible_nonterminals_ALT_def)
  apply(subgoal_tac "\<lparr>cfg_conf = wx1 @ teA A # liftB wx2\<rparr> \<in> cfg_configurations G")
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  prefer 2
  apply(rule cfgSTD.belongs_configurations)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule conjI)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: cfg_configurations_def setAConcat)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(rule_tac
      x="dh"
      in exI)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(subgoal_tac "A \<in> cfgSTD_Nonblockingness_nonterminals_ALT G")
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  prefer 2
  apply(metis cfgSTD_Nonblockingness_nonterminals_ALT_vs_cfgSTD_Nonblockingness_nonterminals)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(thin_tac "A \<in> cfgSTD_Nonblockingness_nonterminals G")
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_ALT_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
  apply(case_tac na)
  apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w' nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' nat)(*strict*)
  apply(rename_tac na)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule_tac
      x="wx1@ w' @ liftB wx2"
      in meta_allE)
  apply(erule_tac
      x="derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf=wx1@(cfg_conf c)@liftB wx2\<rparr>)) n) (n+Suc na)"
      in meta_allE)
  apply(erule_tac
      x="n+Suc na"
      in meta_allE)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(erule meta_impE)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule setA_empty_filterA_empty)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule cfgSTD.derivation_take_preserves_derivation_initial)
  apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule cfgSTD.derivation_append_preserves_derivation)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule cfgSTD.derivation_map_preserves_derivation)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply (metis cfgLM_derivations_are_cfg_derivations)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na i eb c)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2 l r)(*strict*)
  apply(rule_tac
      x="wx1 @ l"
      in exI)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(rule maximum_of_domain_derivation_take)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(simp add: derivation_take_def derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      x="derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf=wx1@(cfg_conf c)@liftB wx2\<rparr>)) dc (Suc na)) (Suc na+x)"
      in exI)
  apply(rule context_conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule cfgSTD.derivation_take_preserves_derivation)
  apply(rule cfgSTD.derivation_append_preserves_derivation)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule cfgSTD.derivation_map_preserves_derivation)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply (metis cfgLM_derivations_are_cfg_derivations)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x i eb c)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2 l r)(*strict*)
  apply(rule_tac
      x="wx1 @ l"
      in exI)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(simp add: derivation_map_def)
  apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
  apply(case_tac "dc 0")
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
  apply(case_tac option)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule cfgSTD.derivation_belongs)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      d="dh"
      in cfgLM.belongs_configurations)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule cfgSTD.derivation_initial_belongs)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      x="(Suc na + x)"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def derivation_append_fit_def derivation_take_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(subgoal_tac "(derivation_append (derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf = wx1 @ cfg_conf c @ liftB wx2\<rparr>)) n) (Suc (n + na))) dc (Suc (n + na))) = (derivation_append dh (derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf = wx1 @ cfg_conf c @ liftB wx2\<rparr>)) dc (Suc na)) (Suc na + x)) n)")
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule ext)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def derivation_append_fit_def derivation_take_def)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "dc (xa - Suc (n + na))")
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(rule_tac
      d="dc"
      and n="x"
      and m="(xa - Suc (n + na))"
      in cfgSTD.no_some_beyond_maximum_of_domain)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  done

corollary cfgSTD_accessible_nonterminals_ALT_contained_in_cfgSTD_Nonblockingness_nonterminals_implies_cfgSTD_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_accessible_nonterminals_ALT G \<subseteq> cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G"
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(case_tac "dh n")
  apply(rename_tac dh n)(*strict*)
  apply(simp add: maximum_of_domain_def get_configuration_def)
  apply(rename_tac dh n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac dh n a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac dh n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e c cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac dh n e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w)(*strict*)
  apply(rule cfgLM_Nonblockingness_branching_to_cfgSTD_Nonblockingness_branching_hlp_mod)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  done

lemma cfgLM_accessible_productions_vs_cfgSTD_accessible_productions1: "
  valid_cfg G
  \<Longrightarrow> cfgLM_accessible_productions G \<subseteq> cfgSTD_accessible_productions G"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgLM_accessible_productions_def cfgSTD_accessible_productions_def)
  apply(clarsimp)
  apply(simp add: cfgLM.get_accessible_destinations_def cfgSTD.get_accessible_destinations_def cfg_destination_def cfg_get_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
  apply(rename_tac x d i e c)(*strict*)
  apply (metis CFGLM_to_CFG_derivation_initial)
  apply(rename_tac x d i e c)(*strict*)
  apply(erule disjE)
  apply(rename_tac x d i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(case_tac e)
  apply(rename_tac x d i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(clarsimp)
  done

lemma cfg_derivation_can_be_translated_to_cfgLM_derivation2_with_labels: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = w1\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = w2\<rparr>)
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> \<exists>d' e. cfgLM.derivation G d' \<and> maximum_of_domain d' n \<and> d' 0 = Some (pair None \<lparr>cfg_conf = w1\<rparr>) \<and> d' n = Some (pair e \<lparr>cfg_conf = w2\<rparr>) \<and> set (get_labels d' n) = set (get_labels d n)"
  apply(induct n arbitrary: d w1 w2 e rule: nat_less_induct)
  apply(rename_tac n d w1 w2 e)(*strict*)
  apply(case_tac n)
  apply(rename_tac n d w1 w2 e)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2)(*strict*)
  apply(rule_tac
      x = "der1 \<lparr>cfg_conf = w2\<rparr>"
      in exI)
  apply(rule conjI)
  apply(rename_tac d w2)(*strict*)
  apply(rule cfgLM.der1_is_derivation)
  apply(rename_tac d w2)(*strict*)
  apply(rule conjI)
  apply(rename_tac d w2)(*strict*)
  apply(rule der1_maximum_of_domain)
  apply(rename_tac d w2)(*strict*)
  apply(rule conjI)
  apply(rename_tac d w2)(*strict*)
  apply(simp add: der1_def)
  apply(rename_tac d w2)(*strict*)
  apply(rule conjI)
  apply(rename_tac d w2)(*strict*)
  apply(simp add: der1_def)
  apply(rename_tac d w2)(*strict*)
  apply(simp add: get_labels_def der1_def)
  apply(rule_tac
      t="nat_seq (Suc 0) 0"
      and s="[]"
      in ssubst)
  apply(rename_tac d w2)(*strict*)
  apply(rule nat_seqEmpty)
  apply(force)
  apply(rename_tac d w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d w1 w2 e nat)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
  apply(rename_tac n d w1 w2 e nat)(*strict*)
  prefer 2
  apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
  apply(rename_tac n d w1 w2 e nat)(*strict*)
  apply(force)
  apply(rename_tac n d w1 w2 e nat)(*strict*)
  apply(force)
  apply(rename_tac n d w1 w2 e nat)(*strict*)
  apply(force)
  apply(rename_tac n d w1 w2 e nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w1 w2 e nat ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac d w1 w2 e nat ea c cfg_conf)(*strict*)
  apply(rename_tac w1')
  apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> ea \<lparr>cfg_conf = w1'\<rparr>")
  apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
  prefer 2
  apply(rule cfgSTD.position_change_due_to_step_relation)
  apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
  apply(force)
  apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
  apply(force)
  apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
  apply(force)
  apply(rename_tac d w1 w2 e nat ea c w1')(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d w2 e nat ea l r)(*strict*)
  apply(rename_tac d w2 e1 n e2 l r)
  apply(rename_tac d w2 e1 n e2 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac d w2 e1 n e2 l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac d w2 e1 n e2 l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = l\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w@r\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w2 \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1 + n2 = n \<and> set(get_labels (derivation_drop d (Suc 0)) n)=set(get_labels d1 n1)\<union>set(get_labels d2 n2)")
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  prefer 2
  apply(rule derivationCanBeDecomposed2_with_labels)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(force)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(rule_tac
      m = "n"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(rule conjI)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(blast)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(rule conjI)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(blast)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(force)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(rule derivation_drop_preserves_generates_maximum_of_domain)
  apply(blast)
  apply(rename_tac d w2 e1 n l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa)(*strict*)
  apply(case_tac "d1 0")
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa a)(*strict*)
  apply(case_tac "d2 0")
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1' w2' n1 n2 n na xa xaa)(*strict*)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = r\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w2 \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1 + n2 = na \<and> set(get_labels SSd na)=set(get_labels d1 n1)\<union>set(get_labels d2 n2)" for SSd)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  prefer 2
  apply(rule_tac
      d="d2"
      in derivationCanBeDecomposed2_with_labels)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(force)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(rule_tac
      x="na"
      in exI)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d e1 l r A w d1 d2 w1 w2 n1 n2 n na e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(case_tac "d1a 0")
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa a)(*strict*)
  apply(case_tac "d2a 0")
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa a aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(subgoal_tac "n2=n1a+n2a")
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  prefer 2
  apply(rule_tac
      d="d2"
      in cfgSTD.maximum_of_domainUnique)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d e1 l r A w d1 d2 w1 n1 n2 n e2 e3 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(thin_tac "cfgSTD.derivation G d")
  apply(thin_tac "maximum_of_domain d (Suc (n1 + n2))")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = l @ teA A # r\<rparr>)")
  apply(thin_tac "d (Suc (n1 + n2)) = Some (pair e1 \<lparr>cfg_conf = w1 @ w1' @ w2'\<rparr>)")
  apply(thin_tac "maximum_of_domain d2 n2")
  apply(thin_tac "cfgSTD.derivation G d2")
  apply(thin_tac "d2 (Suc (n1a + n2a)) = None")
  apply(thin_tac "d2 (n1a + n2a) = Some (pair e3 \<lparr>cfg_conf = w1' @ w2'\<rparr>)")
  apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = w @ r\<rparr>)")
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(subgoal_tac "na=n1a")
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  prefer 2
  apply(rule_tac
      d="d1a"
      in cfgSTD.maximum_of_domainUnique)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(subgoal_tac "nb=n2a")
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  prefer 2
  apply(rule_tac
      d="d2a"
      in cfgSTD.maximum_of_domainUnique)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a na nb xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(subgoal_tac "n1=n")
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  prefer 2
  apply(rule_tac
      d="d1"
      in cfgSTD.maximum_of_domainUnique)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2 w1 n1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2 w1 n e2 d1a d2a w1' w2' n1a n2a xa xaa)(*strict*)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(thin_tac "d1 (Suc n1)=None")
  apply(thin_tac "d2 (Suc n2)=None")
  apply(thin_tac "d3 (Suc n3)=None")
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(subgoal_tac "(\<exists>d1'. cfgLM.derivation G d1' \<and> maximum_of_domain d1' n1 \<and> d1' 0 = Some (pair None \<lparr>cfg_conf = l\<rparr>) \<and> (\<exists>e1'. d1' n1 = Some (pair e1' \<lparr>cfg_conf = w1\<rparr>))\<and>set (get_labels d1' n1) = set (get_labels d1 n1))")
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  prefer 2
  apply(erule_tac
      x="n1"
      in allE)
  apply(erule impE)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(clarsimp)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(subgoal_tac "(\<exists>d2'. cfgLM.derivation G d2' \<and> maximum_of_domain d2' n2 \<and> d2' 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>) \<and> (\<exists>e2'. d2' n2 = Some (pair e2' \<lparr>cfg_conf = w2\<rparr>))\<and>set (get_labels d2' n2) = set (get_labels d2 n2))")
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  prefer 2
  apply(erule_tac
      x="n2"
      in allE)
  apply(erule impE)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3 d1' e1')(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(subgoal_tac "(\<exists>d3'. cfgLM.derivation G d3' \<and> maximum_of_domain d3' n3 \<and> d3' 0 = Some (pair None \<lparr>cfg_conf = r\<rparr>) \<and> (\<exists>e3'. d3' n3 = Some (pair e3' \<lparr>cfg_conf = w3\<rparr>))\<and>set (get_labels d3' n3) = set (get_labels d3 n3))")
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  prefer 2
  apply(erule_tac
      x="n3"
      in allE)
  apply(erule impE)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(erule_tac
      x="d3"
      in allE)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3 d1' d2' e1' e2')(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3)(*strict*)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 e1 d2 d3 w2 w3 n2 n3 e2 e3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(thin_tac "maximum_of_domain d1 n1")
  apply(thin_tac "cfgSTD.derivation G d1")
  apply(thin_tac "d1 n1 = Some (pair e1 \<lparr>cfg_conf = w1\<rparr>)")
  apply(thin_tac "d1 0 = Some (pair None \<lparr>cfg_conf = l\<rparr>)")
  apply(thin_tac "maximum_of_domain d2 n2")
  apply(thin_tac "maximum_of_domain d3 n3")
  apply(thin_tac "cfgSTD.derivation G d2")
  apply(thin_tac "cfgSTD.derivation G d3")
  apply(thin_tac "d2 n2 = Some (pair e2 \<lparr>cfg_conf = w2\<rparr>)")
  apply(thin_tac "d3 n3 = Some (pair e3 \<lparr>cfg_conf = w3\<rparr>)")
  apply(thin_tac "d2 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
  apply(thin_tac "d3 0 = Some (pair None \<lparr>cfg_conf = r\<rparr>)")
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(subgoal_tac "(\<exists>d2''. cfgLM.derivation G d2'' \<and> maximum_of_domain d2'' (Suc n2) \<and> d2'' 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>) \<and> (\<exists>e2''. d2'' (Suc n2) = Some (pair e2'' \<lparr>cfg_conf = w2\<rparr>)) \<and>set (get_labels d2'' (Suc n2)) = set ((Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>)#get_labels d2' n2))")
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  prefer 2
  apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr> ) d2' (Suc 0)"
      in exI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule cfgLM.derivation_concat2)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule cfgLM.der2_is_derivation)
  apply(simp add: cfgLM_step_relation_def)
  apply(rule_tac
      x="[]"
      in exI)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule der2_maximum_of_domain)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(blast)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(simp add: der2_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule_tac
      t="Suc n2"
      and s="Suc 0+n2"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule_tac concat_has_max_dom)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule der2_maximum_of_domain)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr>) d2' (Suc 0)) (Suc n2)"
      and s="Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # get_labels d2' n2"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(rule get_labels_der2_decompose)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
  apply(thin_tac "d2' 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
  apply(thin_tac "maximum_of_domain d2' n2")
  apply(thin_tac "cfgLM.derivation G d2'")
  apply(thin_tac "d2' n2 = Some (pair e2' \<lparr>cfg_conf = w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(subgoal_tac "(\<exists>d23. cfgLM.derivation G d23 \<and> maximum_of_domain d23 (Suc n2+n3) \<and> d23 0 = Some (pair None \<lparr>cfg_conf = [teA A]@r\<rparr>) \<and> (\<exists>e23. d23 (Suc n2+n3) = Some (pair e23 \<lparr>cfg_conf = w2@w3\<rparr>)) \<and> set (get_labels d23 (Suc ((n2 + n3)))) = set (get_labels (derivation_map d2'' (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ r\<rparr>)) (Suc n2)) \<union> set (get_labels (derivation_map d3' (\<lambda>v. \<lparr>cfg_conf = w2 @ (cfg_conf v)\<rparr>)) n3)) ")
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  prefer 2
  apply(rule_tac
      x="(derivation_append (derivation_map d2'' (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ r\<rparr>)) (derivation_map d3' (\<lambda>v. \<lparr>cfg_conf = w2 @ (cfg_conf v)\<rparr>)) (Suc n2))"
      in exI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule context_conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule cfgLM.from_to_is_der)
  apply(rule_tac
      w1'="w2"
      and ?w2.0="r"
      and w2'="w3"
      in cfgLM_concatExtendIsFromToBoth)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule_tac
      x="Suc n2"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
  apply(rule_tac
      x="n3"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule concat_has_max_dom)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule_tac
      t="Suc (n2+n3)"
      and s="Suc n2+n3"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule cfgLM.derivation_append_preserves_label_set)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule cfgLM.derivation_map_preserves_derivation2)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule cfgLM_step_relation_contextOK1)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule cfgLM.derivation_map_preserves_derivation2)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule cfgLM_step_relation_contextOK2)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(rule setA_decompose)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'')(*strict*)
  apply(thin_tac "d3' 0 = Some (pair None \<lparr>cfg_conf = r\<rparr>)")
  apply(thin_tac "d2'' 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      x="(derivation_append (derivation_map d1' (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ ([teA A]@r)\<rparr>)) (derivation_map d23 (\<lambda>v. \<lparr>cfg_conf = w1@ (cfg_conf v)\<rparr>)) n1)"
      in exI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule cfgLM.from_to_is_der)
  apply(rule_tac
      w1'="w1"
      and ?w2.0="[teA A]@r"
      in cfgLM_concatExtendIsFromToBoth)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      x="n1"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
  apply(rule_tac
      x="Suc (n2 +n3)"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="Suc (n1+(n2+n3))"
      and s="n1+Suc(n2+n3)"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule concat_has_max_dom)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule conjI)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="set (get_labels (derivation_append (derivation_map d1' (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [teA A] @ r\<rparr>)) (derivation_map d23 (\<lambda>v. \<lparr>cfg_conf = w1 @ cfg_conf v\<rparr>)) n1) (Suc (n1 + (n2 + n3))))"
      and s=" set (get_labels ((derivation_map d1' (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [teA A] @ r\<rparr>))) n1) \<union> set (get_labels (derivation_map d23 (\<lambda>v. \<lparr>cfg_conf = w1 @ cfg_conf v\<rparr>)) (Suc ((n2 + n3)))) "
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="(Suc (n1 + (n2 + n3)))"
      and s="n1+(Suc ((n2 + n3)))"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule cfgLM.derivation_append_preserves_label_set)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule cfgLM.derivation_map_preserves_derivation2)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule cfgLM_step_relation_contextOK1)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule cfgLM.derivation_map_preserves_derivation2)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule cfgLM_step_relation_contextOK2)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(clarsimp)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      a="[]"
      and c="w2@w3"
      in setA_decompose)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="set (get_labels (derivation_map d1' (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [teA A] @ r\<rparr>)) n1)"
      and s="set (get_labels (d1') n1)"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule cfgLM.derivation_map_preserves_label_set)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="set (get_labels (derivation_map d23 (\<lambda>v. \<lparr>cfg_conf = w1 @ cfg_conf v\<rparr>)) (Suc (n2 + n3)))"
      and s="set (get_labels d23 (Suc (n2+n3)))"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule cfgLM.derivation_map_preserves_label_set)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="set (get_labels d1' n1)"
      and s="set (get_labels d1 n1)"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="set (get_labels d23 (Suc (n2 + n3)))"
      and s="set (get_labels (derivation_map d2'' (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ r\<rparr>)) (Suc n2)) \<union> set (get_labels (derivation_map d3' (\<lambda>v. \<lparr>cfg_conf = w2 @ cfg_conf v\<rparr>)) n3)"
      in ssubst)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
   apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="set (get_labels (derivation_map d2'' (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ r\<rparr>)) (Suc n2))"
      and s="set (get_labels d2'' (Suc n2))"
      in ssubst)
   apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
   apply(rule cfgLM.derivation_map_preserves_label_set)
     apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
     apply(force)
    apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
    apply(force)
   apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
   apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(rule_tac
      t="set (get_labels (derivation_map d3' (\<lambda>v. \<lparr>cfg_conf = w2 @ cfg_conf v\<rparr>)) n3)"
      and s="set (get_labels d3' n3)"
      in ssubst)
   apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
   apply(rule cfgLM.derivation_map_preserves_label_set)
     apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
     apply(force)
    apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
    apply(force)
   apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
   apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="get_labels d (Suc (n1 + (n2 + n3)))"
      and s=" (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) # get_labels (derivation_drop d (Suc 0)) (n1 + (n2 + n3))"
      in ssubst)
   apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
   apply(rule get_labels_derivation_drop_decompose)
   apply(force)
  apply(rename_tac d l r A w d1 d2X w1 n1 d2 d3 w2 w3 n2 n3 d1' d2' d3' e1' e3' d2'' e2'' d23 e23)(*strict*)
  apply(clarsimp)
  done

lemma cfgLM_accessible_productions_vs_cfgSTD_accessible_productions2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgLM_accessible_productions G \<supseteq> cfgSTD_accessible_productions G"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgLM_accessible_productions_def cfgSTD_accessible_productions_def)
  apply(clarsimp)
  apply(simp add: cfgLM.get_accessible_destinations_def cfgSTD.get_accessible_destinations_def cfg_destination_def cfg_get_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(erule disjE)
   apply(rename_tac x d i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(case_tac e)
   apply(rename_tac x d i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a)(*strict*)
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(erule_tac
      x="derivation_take d i"
      in allE)
  apply(erule impE)
   apply(rename_tac d i c a)(*strict*)
   apply(rename_tac d i c a)(*strict*)
   apply(rule cfgSTD.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac d i c a)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac d i c a)(*strict*)
   apply (metis maximum_of_domain_derivation_take not_Some_eq)
  apply(rename_tac d i c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a dc n')(*strict*)
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(rename_tac d i c a dc n' ia e ca)(*strict*)
  apply(case_tac ca)
  apply(rename_tac d i c a dc n' ia e ca cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a dc n' ia e cfg_confa)(*strict*)
  apply(rename_tac w2)
  apply(rename_tac d i c a dc n' ia e w2)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac d i c a dc n' ia e w2)(*strict*)
   prefer 2
   apply (rule cfgSTD.some_position_has_details_at_0)
   apply(rule cfgSTD.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac d i c a dc n' ia e w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a dc n' ia e w2 ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac d i c a dc n' ia e w2 ca cfg_confa)(*strict*)
  apply(rename_tac w1)
  apply(rename_tac d i c a dc n' ia e w2 ca w1)(*strict*)
  apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
   apply(rename_tac d i c a dc n' ia e w2 ca w1)(*strict*)
   prefer 2
   apply (rule cfgSTD.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac d i c a dc n' ia e w2 ca w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
  apply(subgoal_tac "ia=i+n'")
   apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
   prefer 2
   apply(case_tac "ia<i+n'")
    apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_append (derivation_take d i) dc i) ia = Some (pair e1 c1) \<and> (derivation_append (derivation_take d i) dc i) (Suc ia) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation G c1 e2 c2")
     apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc ia"
      in cfgSTD.step_detail_before_some_position)
       apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
       apply(rule cfgSTD.derivation_append_preserves_derivation)
         apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
         apply(rule cfgSTD.derivation_take_preserves_derivation)
         apply(rule cfgSTD.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
        apply(force)
       apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
       apply(simp add: derivation_take_def)
       apply(case_tac "dc 0")
        apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
        apply(simp add: derivation_append_fit_def)
       apply(rename_tac d i a dc n' ia e w2 ca w1 cb aa)(*strict*)
       apply(clarsimp)
       apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
       apply(simp add: derivation_append_fit_def)
      apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
      apply(simp add: derivation_append_def derivation_take_def)
      apply(rule conjI)
       apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "\<exists>e c. d (Suc ia) = Some (pair (Some e) c)")
        apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
        prefer 2
        apply(rule_tac
      m="i"
      in cfgSTD.pre_some_position_is_some_position_prime)
           apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
           apply(rule cfgSTD.derivation_initial_is_derivation)
           apply(force)
          apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
          apply(force)
         apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
         apply(force)
        apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
        apply(force)
       apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
       apply(force)
      apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "Suc ia > i")
       apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "\<exists>n. Suc ia=i+Suc n")
       apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
       prefer 2
       apply(rule_tac
      x="ia-i"
      in exI)
       apply(force)
      apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
      apply(clarsimp)
      apply(rename_tac d i a dc n' e w2 ca w1 cb n)(*strict*)
      apply(subgoal_tac "\<exists>x. n+Suc x=n'")
       apply(rename_tac d i a dc n' e w2 ca w1 cb n)(*strict*)
       prefer 2
       apply(rule_tac
      x="n'-n-(Suc 0)"
      in exI)
       apply(force)
      apply(rename_tac d i a dc n' e w2 ca w1 cb n)(*strict*)
      apply(clarsimp)
      apply(rename_tac d i a dc e w2 ca w1 cb n x)(*strict*)
      apply(simp add: maximum_of_domain_def)
      apply(clarsimp)
      apply(rename_tac d i a dc e w2 ca w1 cb n x y)(*strict*)
      apply(subgoal_tac "\<exists>e c. dc (Suc n) = Some (pair (Some e) c)")
       apply(rename_tac d i a dc e w2 ca w1 cb n x y)(*strict*)
       prefer 2
       apply(rule_tac
      m="Suc (n+x)"
      in cfgSTD.pre_some_position_is_some_position_prime)
          apply(rename_tac d i a dc e w2 ca w1 cb n x y)(*strict*)
          apply(force)
         apply(rename_tac d i a dc e w2 ca w1 cb n x y)(*strict*)
         apply(force)
        apply(rename_tac d i a dc e w2 ca w1 cb n x y)(*strict*)
        apply(force)
       apply(rename_tac d i a dc e w2 ca w1 cb n x y)(*strict*)
       apply(force)
      apply(rename_tac d i a dc e w2 ca w1 cb n x y)(*strict*)
      apply(force)
     apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
     apply(force)
    apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i a dc n' ia e w2 ca w1 cb e2 c2)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d i a dc n' ia e ca w1 cb e2 c2 l r)(*strict*)
    apply (metis elemInsetA emptyE)
   apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
   apply(subgoal_tac "ia \<ge> i+n'")
    apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
   apply(clarsimp)
   apply(case_tac "i+n'=ia")
    apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
    apply(force)
   apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
   apply(subgoal_tac "ia > i+n'")
    apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
   apply(subgoal_tac "\<exists>n. i+n'+Suc n=ia")
    apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
    prefer 2
    apply(rule_tac
      x="ia-i-n'-Suc 0"
      in exI)
    apply(force)
   apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i a dc n' e w2 ca w1 cb n)(*strict*)
   apply (metis CFG_nonterm_free_conf_at_maximum_of_domain cfgSTD.maximum_of_domainUnique less_add_Suc1 less_not_refl)
  apply(rename_tac d i a dc n' ia e w2 ca w1 cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i a dc n' e w2 ca w1 cb)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac d i a dc n' e w2 ca w1 cb)(*strict*)
   apply(clarsimp)
   apply(case_tac ca)
   apply(rename_tac d i a dc n' e w2 ca w1 cb cfg_confa)(*strict*)
   apply(rename_tac w)
   apply(rename_tac d i a dc n' e w2 ca w1 cb w)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
   apply(subgoal_tac "\<exists>d' e. cfgLM.derivation G d' \<and> maximum_of_domain d' (i+n') \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>) \<and> d' (i+n') = Some (pair e \<lparr>cfg_conf=w2\<rparr>) \<and> set(get_labels d' (i+n'))=set(get_labels (derivation_append (derivation_take d i) dc i) (i+n'))")
    apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
    prefer 2
    apply(rule cfg_derivation_can_be_translated_to_cfgLM_derivation2_with_labels)
         apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
         apply(force)
        apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
        apply(rule cfgSTD.derivation_append_preserves_derivation)
          apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
          apply(rule cfgSTD.derivation_take_preserves_derivation)
          apply(rule cfgSTD.derivation_initial_is_derivation)
          apply(force)
         apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
         apply(force)
        apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
        apply(simp add: derivation_take_def)
        apply(simp add: derivation_append_fit_def)
       apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
       apply(rule concat_has_max_dom)
        apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
        apply(rule maximum_of_domain_derivation_take)
        apply(force)
       apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
       apply(force)
      apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
      apply(simp add: derivation_append_def derivation_take_def)
     apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
     apply(simp add: derivation_append_fit_def)
    apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i a dc n' e w2 w1 cb w)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
   apply(rule_tac
      x="d'"
      in exI)
   apply(rule conjI)
    apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
    apply(rule cfgLM.derivation_initialI)
     apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
     apply(force)
    apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
    apply(simp add: cfgSTD.derivation_initial_def)
   apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
   apply(subgoal_tac "Some a \<in> set (get_labels d' (i + n'))")
    apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
    prefer 2
    apply(subgoal_tac "Some a \<in> set (get_labels (derivation_append (derivation_take d i) dc i) (i + n'))")
     apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
     apply(force)
    apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
    apply(simp add: get_labels_def)
    apply(rule inMap)
    apply(rule_tac
      x="i"
      in bexI)
     apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
     apply(simp add: derivation_append_def derivation_take_def)
     apply(simp add: get_label_def)
    apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
    apply(case_tac i)
     apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i a dc n' e w2 w1 cb w d' ea nat)(*strict*)
    apply (metis le_add1 less_eq_Suc_le_raw nat_seq_interval zero_less_Suc)
   apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
   apply(thin_tac "set (get_labels d' (i + n')) = set (get_labels (derivation_append (derivation_take d i) dc i) (i + n'))")
   apply(rename_tac d i a dc n' e w2 w1 cb w d' ea)(*strict*)
   apply(simp add: get_labels_def)
   apply(clarsimp)
   apply(rename_tac d i a dc n' e w2 w1 cb w d' ea ia)(*strict*)
   apply(rule_tac
      x="ia"
      in exI)
   apply(simp add: get_label_def)
   apply(simp add: derivation_append_def derivation_take_def)
   apply(case_tac "d' ia")
    apply(rename_tac d i a dc n' e w2 w1 cb w d' ea ia)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i a dc n' e w2 w1 cb w d' ea ia aa)(*strict*)
   apply(clarsimp)
   apply(case_tac aa)
   apply(rename_tac d i a dc n' e w2 w1 cb w d' ea ia aa option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i a dc n' e w2 ca w1 cb)(*strict*)
  apply(force)
  done

lemma cfgLM_accessible_productions_vs_cfgSTD_accessible_productions: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgLM_accessible_productions G = cfgSTD_accessible_productions G"
  apply(rule order_antisym)
   apply(metis cfgLM_accessible_productions_vs_cfgSTD_accessible_productions1)
  apply(metis cfgLM_accessible_productions_vs_cfgSTD_accessible_productions2)
  done

lemma cfgLM_accessible_productions_vs_cfgLM_required_productions1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgLM_accessible_productions G \<subseteq> cfgLM_required_productions G"
  apply(simp add: cfgLM_accessible_productions_def cfgLM_required_productions_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(simp add: cfgLM.get_accessible_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(simp add: cfg_get_destinations_def)
  apply(erule disjE)
   apply(rename_tac x d i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(case_tac e)
   apply(rename_tac x d i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a)(*strict*)
  apply(simp add: cfg_destination_def)
  apply(erule_tac
      x="derivation_take d i"
      in allE)
  apply(erule impE)
   apply(rename_tac d i c a)(*strict*)
   apply(rule cfgSTD.derivation_take_preserves_derivation_initial)
   apply (metis CFGLM_to_CFG_derivation_initial)
  apply(rename_tac d i c a)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac d i c a)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac d i c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i c a dc x)(*strict*)
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(rename_tac d i c a dc x ia e ca)(*strict*)
  apply(subgoal_tac "maximum_of_domain (derivation_append (derivation_take d i) dc i) (i+x)")
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   prefer 2
   apply(rule concat_has_max_dom)
    apply(rename_tac d i c a dc x ia e ca)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(force)
  apply(rename_tac d i c a dc x ia e ca)(*strict*)
  apply(subgoal_tac "maximum_of_domain (derivation_append (derivation_take d i) dc i) (i+x)")
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   prefer 2
   apply(rule concat_has_max_dom)
    apply(rename_tac d i c a dc x ia e ca)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(force)
  apply(rename_tac d i c a dc x ia e ca)(*strict*)
  apply(subgoal_tac "cfgSTD.derivation_initial G (derivation_append (derivation_take d i) dc i)")
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
     apply(rename_tac d i c a dc x ia e ca)(*strict*)
     apply(force)
    apply(rename_tac d i c a dc x ia e ca)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation_initial)
    apply (metis CFGLM_to_CFG_derivation_initial)
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac d i c a dc x ia e ca)(*strict*)
     apply(rule cfgSTD.derivation_take_preserves_derivation)
     apply(rule cfgSTD.derivation_initial_is_derivation)
     apply (metis CFGLM_to_CFG_derivation_initial)
    apply(rename_tac d i c a dc x ia e ca)(*strict*)
    apply(force)
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(simp add: derivation_take_def)
   apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
    apply(rename_tac d i c a dc x ia e ca)(*strict*)
    prefer 2
    apply (rule_tac
      M="G"
      in cfgSTD.some_position_has_details_at_0)
    apply(force)
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i c a dc x ia e ca cb)(*strict*)
   apply(simp add: derivation_append_fit_def)
  apply(rename_tac d i c a dc x ia e ca)(*strict*)
  apply(subgoal_tac "ia=i+x")
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i c a dc x e ca)(*strict*)
   apply(subgoal_tac "\<exists>d' e. cfgLM.derivation G d' \<and> maximum_of_domain d' (i+x) \<and> d' 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>) \<and> d' (i+x) = Some (pair e \<lparr>cfg_conf=cfg_conf ca\<rparr>) \<and> set(get_labels d' (i+x))=set(get_labels (derivation_append (derivation_take d i) dc i) (i+x))")
    apply(rename_tac d i c a dc x e ca)(*strict*)
    prefer 2
    apply(rule cfg_derivation_can_be_translated_to_cfgLM_derivation2_with_labels)
         apply(rename_tac d i c a dc x e ca)(*strict*)
         apply(force)
        apply(rename_tac d i c a dc x e ca)(*strict*)
        apply(rule cfgSTD.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac d i c a dc x e ca)(*strict*)
       apply(force)
      apply(rename_tac d i c a dc x e ca)(*strict*)
      apply(simp add: derivation_append_def derivation_take_def)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(clarsimp)
      apply(case_tac "d 0")
       apply(rename_tac d i c a dc x e ca)(*strict*)
       apply(clarsimp)
      apply(rename_tac d i c a dc x e ca aa)(*strict*)
      apply(clarsimp)
      apply(case_tac aa)
      apply(rename_tac d i c a dc x e ca aa option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac d i c a dc x e ca b)(*strict*)
      apply(simp add: cfg_initial_configurations_def)
     apply(rename_tac d i c a dc x e ca)(*strict*)
     apply(force)
    apply(rename_tac d i c a dc x e ca)(*strict*)
    apply(force)
   apply(rename_tac d i c a dc x e ca)(*strict*)
   apply(erule exE)+
   apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
   apply(rule_tac
      x="d'"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
    apply(simp add: cfgLM.derivation_initial_def)
    apply(clarsimp)
    apply(case_tac "d 0")
     apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i c a dc x e ca d' ea aa)(*strict*)
    apply(clarsimp)
    apply(case_tac aa)
    apply(rename_tac d i c a dc x e ca d' ea aa option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i c a dc x e ca d' ea b)(*strict*)
    apply(simp add: cfg_initial_configurations_def)
    apply(force)
   apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
    apply(subgoal_tac "Some a \<in> set(get_labels d' (i + x))")
     apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
     apply(thin_tac "set (get_labels d' (i + x)) = set (get_labels (derivation_append (derivation_take d i) dc i) (i + x))")
     apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
     apply(simp add: get_labels_def)
     apply(clarsimp)
     apply(rename_tac d i c a dc x e ca d' ea ia)(*strict*)
     apply(rule_tac
      x="ia"
      in exI)
     apply(simp add: get_label_def)
     apply(case_tac "d' ia")
      apply(rename_tac d i c a dc x e ca d' ea ia)(*strict*)
      apply(clarsimp)
     apply(rename_tac d i c a dc x e ca d' ea ia aa)(*strict*)
     apply(clarsimp)
     apply(case_tac aa)
     apply(rename_tac d i c a dc x e ca d' ea ia aa option b)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
    apply(rule_tac
      A="set (get_labels (derivation_append (derivation_take d i) dc i) (i + x))"
      in set_mp)
     apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
     apply(force)
    apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
    apply(thin_tac "set (get_labels d' (i + x)) = set (get_labels (derivation_append (derivation_take d i) dc i) (i + x))")
    apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
    apply(simp add: get_labels_def)
    apply(rule inMap)
    apply(rule_tac
      x="i"
      in bexI)
     apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
     apply(simp add: get_label_def derivation_append_def derivation_take_def)
    apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
    apply(case_tac i)
     apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac d c a dc x e ca d' ea)(*strict*)
     apply (metis cfgLM.derivation_initial_is_derivation cfgLM.initialNotEdgeSome)
    apply(rename_tac d i c a dc x e ca d' ea nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d c a dc x e ca d' ea nat)(*strict*)
    apply(rule nat_seq_interval)
     apply(rename_tac d c a dc x e ca d' ea nat)(*strict*)
     apply(force)
    apply(rename_tac d c a dc x e ca d' ea nat)(*strict*)
    apply(force)
   apply(rename_tac d i c a dc x e ca d' ea)(*strict*)
   apply(rule_tac
      x="i+x"
      in exI)
   apply(clarsimp)
   apply(case_tac ca)
   apply(rename_tac d i c a dc x e ca d' ea cfg_confa)(*strict*)
   apply(clarsimp)
  apply(rename_tac d i c a dc x ia e ca)(*strict*)
  apply(case_tac "ia<i+x")
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   prefer 2
   apply(case_tac "ia>i+x")
    apply(rename_tac d i c a dc x ia e ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      d="derivation_append (derivation_take d i) dc i"
      in cfgSTD.no_some_beyond_maximum_of_domain)
      apply(rename_tac d i c a dc x ia e ca)(*strict*)
      apply(rule cfgSTD.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d i c a dc x ia e ca)(*strict*)
     apply(force)
    apply(rename_tac d i c a dc x ia e ca)(*strict*)
    apply(force)
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(force)
  apply(rename_tac d i c a dc x ia e ca)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      d="derivation_append (derivation_take d i) dc i"
      in cfgSTD.noDeadEndBeforeMaxDom)
      apply(rename_tac d i c a dc x ia e ca)(*strict*)
      apply(rule cfgSTD.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac d i c a dc x ia e ca)(*strict*)
     apply(force)
    apply(rename_tac d i c a dc x ia e ca)(*strict*)
    apply(force)
   apply(rename_tac d i c a dc x ia e ca)(*strict*)
   apply(force)
  apply(rename_tac d i c a dc x ia e ca)(*strict*)
  apply(rule cfgSTD_no_step_without_nonterms)
  apply(force)
  done

lemma nonterminals_are_eliminable_in_untouchable_context: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> d (n + m) = Some (pair e' \<lparr>cfg_conf = liftB w1 @ teA A # w\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = c @ teA A # w\<rparr>)
  \<Longrightarrow> setA c \<subseteq> cfgSTD_Nonblockingness_nonterminals G"
  apply(induct m arbitrary: n e e' w1 A w c)
   apply(rename_tac n e e' w1 A w c)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e' w1 A w x)(*strict*)
   apply (metis setA_liftB emptyE)
  apply(rename_tac m n e e' w1 A w c)(*strict*)
  apply(clarsimp)
  apply(rename_tac m n e e' w1 A w c x)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac m n e e' w1 A w c x)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (n+m)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac m n e e' w1 A w c x)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac m n e e' w1 A w c x)(*strict*)
    apply(force)
   apply(rename_tac m n e e' w1 A w c x)(*strict*)
   apply(force)
  apply(rename_tac m n e e' w1 A w c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac m n e e' w1 A w c x e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac m n e e' w1 A w c x e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac m n e e' w1 A w c x e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m n e e' w1 A w c x e2 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac m n e e' w1 A w c x e2 l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac B v)
  apply(rename_tac m n e e' w1 A w c x e2 l r B v)(*strict*)
  apply(clarsimp)
  apply(rename_tac m n e e' w1 A w c x l r B v)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1@[teA x]@w2=c")
   apply(rename_tac m n e e' w1 A w c x l r B v)(*strict*)
   apply(clarsimp)
   apply(rename_tac m n e e' w1 A w x l r B v w1a w2)(*strict*)
   apply(thin_tac "x \<in> setA (w1a @ teA x # w2)")
   apply(subgoal_tac "prefix l w1a")
    apply(rename_tac m n e e' w1 A w x l r B v w1a w2)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac m n e e' w1 A w x l r B v w2 c)(*strict*)
    apply(erule_tac
      x="Suc n"
      in meta_allE)
    apply(clarsimp)
    apply(erule_tac
      x="Some \<lparr>prod_lhs = B, prod_rhs = v\<rparr>"
      in meta_allE)
    apply(erule_tac
      x="e'"
      in meta_allE)
    apply(clarsimp)
    apply(erule_tac
      x="w1"
      in meta_allE)
    apply(erule_tac
      x="A"
      in meta_allE)
    apply(erule_tac
      x="w"
      in meta_allE)
    apply(clarsimp)
    apply(case_tac c)
     apply(rename_tac m n e e' w1 A w x l r B v w2 c)(*strict*)
     prefer 2
     apply(rename_tac m n e e' w1 A w x l r B v w2 c a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac m n e e' w1 A w x l B v w2 list)(*strict*)
     apply(erule_tac
      x="l @ v @ list @ teA x # w2"
      in meta_allE)
     apply(clarsimp)
     apply (metis setA_setmp_concat_2 concat_asso elemInsetA)
    apply(rename_tac m n e e' w1 A w x l r B v w2 c)(*strict*)
    apply(clarsimp)
    apply(rename_tac m n e e' w1 A w l B v w2)(*strict*)
    apply(erule_tac
      x="l @ v @ w2"
      in meta_allE)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = v\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
     apply(rename_tac m n e e' w1 A w l B v w2)(*strict*)
     prefer 2
     apply(rule canElimCombine)
      apply(rename_tac m n e e' w1 A w l B v w2)(*strict*)
      apply(force)
     apply(rename_tac m n e e' w1 A w l B v w2)(*strict*)
     apply(simp add: setAConcat)
    apply(rename_tac m n e e' w1 A w l B v w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac m n e e' w1 A w l B v w2 da w')(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
    apply(case_tac "da 0")
     apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
     apply(clarsimp)
    apply(rename_tac m n e e' w1 A w l B v w2 da w' na x a)(*strict*)
    apply(clarsimp)
    apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
    apply(thin_tac "setA (l @ v @ w2) \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
    apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
    apply(rule conjI)
     apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
     apply (metis prod_lhs_in_nonterms)
    apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
    apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = [teA B]\<rparr> \<lparr>prod_lhs = B, prod_rhs = v\<rparr> \<lparr>cfg_conf = v\<rparr>) da (Suc 0)"
      in exI)
    apply(rule_tac
      x="w'"
      in exI)
    apply(clarsimp)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(rule context_conjI)
     apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
     apply(rule cfgSTD.derivation_append_preserves_derivation)
       apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(simp add: cfgSTD_step_relation_def)
       apply(force)
      apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
      apply(force)
     apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
    apply(rule conjI)
     apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
    apply(rule conjI)
     apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
     apply(force)
    apply(rename_tac m n e e' w1 A w l B v w2 da w' na x)(*strict*)
    apply(rule_tac
      x="Suc na"
      in exI)
    apply(simp add: derivation_append_def der2_def)
    apply(clarsimp)
   apply(rename_tac m n e e' w1 A w x l r B v w1a w2)(*strict*)
   apply(subgoal_tac "prefix l w1a \<or> prefix w1a l")
    apply(rename_tac m n e e' w1 A w x l r B v w1a w2)(*strict*)
    apply(case_tac "prefix l w1a")
     apply(rename_tac m n e e' w1 A w x l r B v w1a w2)(*strict*)
     apply(force)
    apply(rename_tac m n e e' w1 A w x l r B v w1a w2)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac m n e e' w1 A w x r B v w1a w2 c)(*strict*)
    apply(case_tac c)
     apply(rename_tac m n e e' w1 A w x r B v w1a w2 c)(*strict*)
     apply(force)
    apply(rename_tac m n e e' w1 A w x r B v w1a w2 c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac m n e e' w1 A w x r B v w1a w2 list)(*strict*)
    apply (metis elemInsetA ex_in_conv)
   apply(rename_tac m n e e' w1 A w x l r B v w1a w2)(*strict*)
   apply (metis mutual_prefix_prefix)
  apply(rename_tac m n e e' w1 A w c x l r B v)(*strict*)
  apply(rule setA_decomp)
  apply(force)
  done

lemma one_step_preserves_cfgLM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> e \<in> cfg_productions G
  \<Longrightarrow> prod_lhs e \<in> cfgLM_accessible_nonterminals G
  \<Longrightarrow> setA (prod_rhs e) \<subseteq> cfgLM_accessible_nonterminals G"
  apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(force)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d n w1 w2)(*strict*)
   prefer 2
   apply(rule setA_has_position)
   apply(force)
  apply(rename_tac x d n w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w1a w2a)(*strict*)
  apply(case_tac e)
  apply(rename_tac x d n w1 w2 w1a w2a prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac x d n w1 w2 w1a w2a A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w1a w2a A)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(rename_tac x d n w1 w2 w1a w2a A)(*strict*)
   apply(force)
  apply(rename_tac x d n w1 w2 w1a w2a A a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d n w1 w2 w1a w2a A a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w1a w2a A option)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d n w1 w2 w1a w2a A option)(*strict*)
   prefer 2
   apply(rule_tac
      w="w1a"
      in construct_elimininating_derivation_prime)
     apply(rename_tac x d n w1 w2 w1a w2a A option)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 w1a w2a A option)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w1a w2a A option)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(rename_tac x d n w1 w2 w1a w2a A option xa)(*strict*)
   apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w1a @ teA x # w2a\<rparr>"
      in ballE)
    apply(rename_tac x d n w1 w2 w1a w2a A option xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x d n w1 w2 w1a w2a A option xa)(*strict*)
   apply(clarsimp)
   apply(simp add: setAConcat)
   apply(force)
  apply(rename_tac x d n w1 w2 w1a w2a A option)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
  apply(fold get_configuration_def)
  apply(thin_tac "x \<in> setA (w1a @ teA x # w2a)")
  apply(subgoal_tac "\<exists>d. cfgLM.derivation_initial G d \<and> (get_configuration (d (Suc(n+na))) = Some \<lparr>cfg_conf = liftB (w1@v)@teA x#w2a@w2\<rparr>)")
   apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
   apply(force)
  apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.derivation_initial G d \<and> (get_configuration (d (Suc n)) = Some \<lparr>cfg_conf = liftB w1@w1a@teA x#w2a@w2\<rparr>)")
   apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = liftB w1 @ teA (prod_lhs \<lparr>prod_lhs = A, prod_rhs = w1a @ teA x # w2a\<rparr>) # w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = w1a @ teA x # w2a\<rparr> \<lparr>cfg_conf = liftB w1 @ (prod_rhs \<lparr>prod_lhs = A, prod_rhs = w1a @ teA x # w2a\<rparr>) @ w2\<rparr>) n"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
      apply(force)
     apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="liftB w1"
      in exI)
     apply(clarsimp)
     apply(rule setA_liftB)
    apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
    apply(simp add: get_configuration_def)
    apply(simp add: der2_def)
   apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
   apply(simp add: der2_def derivation_append_def get_configuration_def)
  apply(rename_tac x d n w1 w2 w1a w2a A option da na e v)(*strict*)
  apply(thin_tac "d n = Some (pair option \<lparr>cfg_conf = liftB w1 @ teA A # w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
   prefer 2
   apply(rule_tac
      f="da"
      and C="\<lambda>y. \<lparr>cfg_conf=liftB w1@(cfg_conf y)@teA x#w2a@w2\<rparr>"
      in cfgLM.derivation_map_preserves_derivation2)
    apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db a ea b)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db a ea b l r)(*strict*)
   apply(rule_tac
      x="liftB w1 @ l"
      in exI)
   apply(clarsimp)
   apply(simp add: setAConcat)
   apply(simp add: setA_liftB)
  apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
  apply(rule_tac
      x="derivation_append db (derivation_map da (\<lambda>y. \<lparr>cfg_conf = liftB w1 @ cfg_conf y @ teA x # w2a @ w2\<rparr>)) (Suc n)"
      in exI)
  apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
    apply(force)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "db (Suc n)")
    apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db option)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
  apply(simp add: der2_def derivation_map_def derivation_append_def get_configuration_def)
  apply(case_tac na)
   apply(rename_tac x d n w1 w2 w1a w2a A da na e v db)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n w1 w2 w2a A da v db)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac x d n w1 w2 w1a w2a A da na e v db nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 w1a w2a A da e v db nat)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  done

corollary cfgSTD_Nonblockingness_branching_to_cfgLM_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G"
  apply(simp add: cfgSTD.Nonblockingness_branching_def cfgLM.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule impE)
   apply(rename_tac dh n)(*strict*)
   apply (metis CFGLM_to_CFG_derivation_initial)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="n"
      in allE)
  apply(erule impE)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac dh n dc x)(*strict*)
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac dh n dc x y ya)(*strict*)
   apply(case_tac y)
   apply(rename_tac dh n dc x y ya option conf)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x e c)(*strict*)
  apply(subgoal_tac "dc 0 = Some (pair None c)")
   apply(rename_tac dh n dc x e c)(*strict*)
   prefer 2
   apply(simp add: maximum_of_domain_def derivation_append_fit_def derivation_append_def derivation_take_def)
   apply(clarsimp)
   apply(rename_tac dh n dc x e c y)(*strict*)
   apply(case_tac "dc 0")
    apply(rename_tac dh n dc x e c y)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e c y a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n dc x e c y a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x e c y option conf)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n dc x e c y option conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc x e c y option conf a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n dc x e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n dc x e c cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac dh n dc x e c w)(*strict*)
  apply(subgoal_tac "\<exists>e c. dc x = Some (pair e c)")
   apply(rename_tac dh n dc x e c w)(*strict*)
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac dh n dc x e w y)(*strict*)
   apply(case_tac y)
   apply(rename_tac dh n dc x e w y option conf)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x e w ea ca)(*strict*)
  apply(case_tac ca)
  apply(rename_tac dh n dc x e w ea ca cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
   prefer 2
   apply(rule_tac
      d="dc"
      and n="x"
      in cfg_derivation_can_be_translated_to_cfgLM_derivation)
        apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
        apply(force)
       apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
       apply (metis (full_types, hide_lams) cfgSTD.derivation_append_preserves_derivation_initial_prime cfgSTD.derivation_initial_def cfgSTD.derivation_take_preserves_derivation_initial maximum_of_domain_derivation_take option.distinct(1))
      apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
      apply (metis concat_has_max_dom maximum_of_domain_derivation_take option.distinct(1))
     apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x e wa ea w)(*strict*)
   apply(rule_tac
      e="if x=0 then e else ea"
      and ?c.0="\<lparr>cfg_conf=if x=0 then wa else w\<rparr>"
      and n="n+x"
      and d="derivation_append dh dc n"
      in cfgSTD_no_nonterminal_at_end_in_marking_condition)
        apply(rename_tac dh n dc x e wa ea w)(*strict*)
        apply(force)
       apply(rename_tac dh n dc x e wa ea w)(*strict*)
       apply (metis CFGLM_to_CFG_derivation_initial cfgSTD.derivation_append_preserves_derivation_initial_prime cfgSTD.derivation_initial_is_derivation)
      apply(rename_tac dh n dc x e wa ea w)(*strict*)
      apply (metis concat_has_max_dom)
     apply(rename_tac dh n dc x e wa ea w)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x e wa ea w)(*strict*)
    apply(case_tac "x=0")
     apply(rename_tac dh n dc x e wa ea w)(*strict*)
     apply(clarsimp)
     apply(rename_tac dh n dc e w)(*strict*)
     apply(simp add: derivation_append_def)
    apply(rename_tac dh n dc x e wa ea w)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
   apply(rename_tac dh n dc x e wa ea w)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n dc x e wa ea ca w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
      apply(force)
     apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
    apply(rule_tac
      d="dc"
      in cfgSTD.belongs_configurations)
     apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
   apply(simp add: derivation_append_fit_def)
  apply(rename_tac dh n dc x e wa ea w d' eb)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(rule_tac
      x="n+x"
      in exI)
  apply(clarsimp)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rule conjI)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
   apply(case_tac "i=n")
    apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
   apply(case_tac "i<n")
    apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
    prefer 2
    apply(clarsimp)
    apply (metis (erased, hide_lams) cfgSTD.no_some_beyond_maximum_of_domain diff_diff_cancel diff_is_0_eq less_eq_Suc_le less_imp_diff_less not_less_eq_eq option.distinct(1))
   apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and n="i"
      and m="n"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
     apply(force)
    apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
    apply(force)
   apply(rename_tac dh n dc e wa d' i ec c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc e wa d' i ec c e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def cfg_marking_configuration_def)
   apply(clarsimp)
   apply(rename_tac dh n dc e wa d' i ec c e2 c2 l r)(*strict*)
   apply(case_tac c2)
   apply(rename_tac dh n dc e wa d' i ec c e2 c2 l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc e wa d' i ec c e2 l r)(*strict*)
   apply(case_tac c)
   apply(rename_tac dh n dc e wa d' i ec c e2 l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc e wa d' i ec e2 l r)(*strict*)
   apply (metis elemInsetA empty_iff)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
  apply(clarsimp)
  apply(case_tac "i=n")
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x wa ea w d' eb ec)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac dh n dc x wa ea w d' eb ec)(*strict*)
    prefer 2
    apply(rule_tac
      d="d'"
      and n="0"
      and m="x"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac dh n dc x wa ea w d' eb ec)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac dh n dc x wa ea w d' eb ec)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x wa ea w d' eb ec)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x wa ea w d' eb ec)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x wa ea w d' eb ec e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def cfg_marking_configuration_def)
   apply(clarsimp)
   apply(rename_tac dh n dc x ea w d' eb ec e2 c2 l r)(*strict*)
   apply(case_tac c2)
   apply(rename_tac dh n dc x ea w d' eb ec e2 c2 l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x ea w d' eb ec e2 l r)(*strict*)
   apply (metis elemInsetA empty_iff)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
  apply(case_tac "i<n")
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and n="i"
      and m="n"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def cfg_marking_configuration_def)
   apply(clarsimp)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 c2 l r)(*strict*)
   apply(case_tac c2)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 c2 l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 l r)(*strict*)
   apply(case_tac c)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec e2 l r)(*strict*)
   apply (metis elemInsetA empty_iff)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i-n\<le>x")
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
   prefer 2
   apply (metis (full_types) cfgSTD.no_some_beyond_maximum_of_domain less_eq_Suc_le not_less_eq_eq option.distinct(1))
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
  apply(case_tac "i-n=x")
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
   prefer 2
   apply(rule_tac
      d="dc"
      and n="i-n"
      and m="x"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
    apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
   apply(force)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def cfgLM_step_relation_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc x e wa ea w d' eb i ec c e2 l r)(*strict*)
  apply (metis elemInsetA empty_iff)
  done

lemma cfgLM_accessible_productions_vs_cfgLM_required_productions: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgLM_accessible_productions G = cfgLM_required_productions G"
  apply(rule order_antisym)
   apply(rule cfgLM_accessible_productions_vs_cfgLM_required_productions1)
    apply(force)+
  apply(rule cfgLM_accessible_productions_vs_cfgLM_required_productions2)
  apply(force)+
  done

lemma cfgLM_Nonblockingness_branching_to_cfgLM_Nonblockingness_branching_hlp_mod: "
       valid_cfg G \<Longrightarrow>
       cfgLM_accessible_nonterminals G \<subseteq> cfgLM_Nonblockingness_nonterminals G \<Longrightarrow>
       ATS.derivation_initial cfg_initial_configurations
        cfgLM_step_relation G dh \<Longrightarrow>
       maximum_of_domain dh n \<Longrightarrow>
       dh n = Some (pair e \<lparr>cfg_conf = w\<rparr>) \<Longrightarrow>
       \<exists>dc. cfgLM.derivation G dc \<and>
            cfgLM.belongs G dc \<and>
            Ex (maximum_of_domain dc) \<and>
            derivation_append_fit dh dc n \<and>
            cfg_marking_condition G (derivation_append dh dc n)"
  apply(induct "length(filterA w)" arbitrary: dh n e w)
   apply(rename_tac w dh n e)(*strict*)
   apply(subgoal_tac "\<exists>wx. liftB wx = w")
    apply(rename_tac w dh n e)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB w"
      in exI)
    apply(rule liftBDeConv2)
    apply(rule filterA_setA)
    apply(force)
   apply(rename_tac w dh n e)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB wx\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply (metis cfgLM.der1_is_derivation)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule cfgLM.der1_belongs)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac dh n e wx)(*strict*)
     apply(rule cfgLM.derivation_initial_belongs)
      apply(rename_tac dh n e wx)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply (metis der1_maximum_of_domain)
   apply(rename_tac dh n e wx)(*strict*)
   apply(rule conjI)
    apply(rename_tac dh n e wx)(*strict*)
    apply(simp add: derivation_append_fit_def der1_def)
   apply(rename_tac dh n e wx)(*strict*)
   apply(simp add: cfg_marking_condition_def derivation_append_def der1_def cfg_marking_configuration_def)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: setA_liftB)
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac dh n e wx)(*strict*)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(rename_tac dh n e wx)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx)(*strict*)
   apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(subgoal_tac "\<exists>wx1 A wx2. w = liftB wx1 @[teA A]@ wx2")
   apply(rename_tac x w dh n e)(*strict*)
   prefer 2
   apply(rule filterA_gt_0_then_lm_nontelminal)
   apply(force)
  apply(rename_tac x w dh n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(subgoal_tac "A \<in> cfgLM_Nonblockingness_nonterminals G")
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfgLM_accessible_nonterminals G"
      in set_mp)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(thin_tac "cfgLM_accessible_nonterminals G \<subseteq> cfgLM_Nonblockingness_nonterminals G")
   apply(simp add: cfgLM_accessible_nonterminals_def)
   apply(subgoal_tac "\<lparr>cfg_conf = liftB wx1 @ teA A # wx2\<rparr> \<in> cfg_configurations G")
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    prefer 2
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac x dh n e wx1 A wx2)(*strict*)
     apply(rule cfgLM.derivation_initial_belongs)
      apply(rename_tac x dh n e wx1 A wx2)(*strict*)
      apply(force)
     apply(rename_tac x dh n e wx1 A wx2)(*strict*)
     apply(force)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(rule conjI)
    apply(rename_tac x dh n e wx1 A wx2)(*strict*)
    apply(simp add: cfg_configurations_def setAConcat)
   apply(rename_tac x dh n e wx1 A wx2)(*strict*)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(force)
  apply(rename_tac x dh n e wx1 A wx2)(*strict*)
  apply(simp add: cfgLM_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
  apply(case_tac na)
   apply(rename_tac dh n e wx1 A wx2 d na ea w')(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d na ea w' nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' nat)(*strict*)
  apply(rename_tac na)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule_tac
      x="liftB wx1@ w' @ wx2"
      in meta_allE)
  apply(erule_tac
      x="derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf=liftB wx1@(cfg_conf c)@wx2\<rparr>)) n) (n+Suc na)"
      in meta_allE)
  apply(erule_tac
      x="n+Suc na"
      in meta_allE)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule setA_empty_filterA_empty)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule cfgLM.derivation_take_preserves_derivation_initial)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
    apply(rule cfgLM.derivation_map_preserves_derivation)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
      apply (metis cfgLM_derivations_are_cfg_derivations)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na i eb c)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na c1 eb c2 l r)(*strict*)
    apply(rule_tac
      x="liftB wx1 @ l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat setA_liftB)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
   apply(simp add: derivation_take_def derivation_append_def derivation_map_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule_tac
      x="derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf=liftB wx1@(cfg_conf c)@wx2\<rparr>)) dc (Suc na)) (Suc na+x)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule cfgLM.derivation_take_preserves_derivation)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(rule cfgLM.derivation_map_preserves_derivation)
       apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
       apply (metis cfgLM_derivations_are_cfg_derivations)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x i eb c)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x c1 eb c2 l r)(*strict*)
     apply(rule_tac
      x="liftB wx1 @ l"
      in exI)
     apply(clarsimp)
     apply(simp add: setAConcat setA_liftB)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(simp add: derivation_map_def)
   apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
   apply(case_tac "dc 0")
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x a option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
   apply(case_tac option)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x option conf a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
      apply(force)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(simp add: derivation_append_fit_def derivation_take_def derivation_append_def derivation_map_def)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(rule_tac
      d="dh"
      in cfgLM.belongs_configurations)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(rule_tac
      x="(Suc na + x)"
      in exI)
   apply(rule maximum_of_domain_derivation_take)
   apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def maximum_of_domain_def derivation_append_fit_def derivation_take_def)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(subgoal_tac "(derivation_append (derivation_take (derivation_append dh (derivation_map d (\<lambda>c. \<lparr>cfg_conf = liftB wx1 @ cfg_conf c @ wx2\<rparr>)) n) (Suc (n + na))) dc (Suc (n + na))) = (derivation_append dh (derivation_take (derivation_append (derivation_map d (\<lambda>c. \<lparr>cfg_conf = liftB wx1 @ cfg_conf c @ wx2\<rparr>)) dc (Suc na)) (Suc na + x)) n)")
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x)(*strict*)
  apply(rule ext)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(simp add: derivation_append_def derivation_map_def derivation_append_fit_def derivation_take_def)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "dc (xa - Suc (n + na))")
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(rule_tac
      d="dc"
      and n="x"
      and m="(xa - Suc (n + na))"
      in cfgLM.no_some_beyond_maximum_of_domain)
     apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
     apply(force)
    apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
    apply(force)
   apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
   apply(force)
  apply(rename_tac dh n e wx1 A wx2 d ea w' na dc x xa a)(*strict*)
  apply(force)
  done

corollary cfgLM_accessible_nonterminals_contained_in_cfgLM_Nonblockingness_nonterminals_implies_cfgLM_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgLM_accessible_nonterminals G \<subseteq> cfgLM_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G"
  apply(simp add: cfgLM.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(case_tac "dh n")
   apply(rename_tac dh n)(*strict*)
   apply(simp add: maximum_of_domain_def get_configuration_def)
  apply(rename_tac dh n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac dh n a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac dh n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e c cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac dh n e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w)(*strict*)
  apply(rule cfgLM_Nonblockingness_branching_to_cfgLM_Nonblockingness_branching_hlp_mod)
      apply(rename_tac dh n e w)(*strict*)
      apply(force)
     apply(rename_tac dh n e w)(*strict*)
     apply(force)
    apply(rename_tac dh n e w)(*strict*)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(force)
  done

lemma cfgSTD_to_cfgLM_translate_derivation: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgLM.derivation G2 d
  \<Longrightarrow> cfgSTD.belongs G1 d
  \<Longrightarrow> cfgLM.derivation G1 d"
  apply(simp (no_asm) add: cfgLM.derivation_def)
  apply(clarsimp)
  apply(case_tac "i")
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
    apply(simp add: cfgLM.derivation_def)
    apply(erule_tac x="0" in allE)
    apply(force)
   apply(clarsimp)
   apply(case_tac a)
   apply(clarsimp)
   apply(case_tac x1)
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_def)
   apply(erule_tac x="0" in allE)
   apply(force)
  apply(clarsimp)
  apply(case_tac "d (Suc nat)")
   apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac n="nat" and m="Suc nat" and d="d" in cfgLM.step_detail_before_some_position)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac n="nat" and m="Suc nat" and d="d" in cfgLM.step_detail_before_some_position)
     apply(simp add: cfgSTD.derivation_initial_def)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac P="G1" and d="d" in cfgSTD.belongs_step_labels)
    apply(force)
   apply(force)
  apply(simp add: cfg_step_labels_def)
  done

lemma cfgSTD_to_cfgLM_translate_derivation_initial: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgLM.derivation_initial G2 d
  \<Longrightarrow> cfgSTD.derivation_initial G1 d
  \<Longrightarrow> cfgLM.derivation_initial G1 d"
  apply(simp add: cfgLM.derivation_initial_def)
  apply(case_tac "d 0")
   apply(clarsimp)
  apply(case_tac a)
  apply(clarsimp)
  apply(rule conjI)
   prefer 2
   apply(simp add: cfg_sub_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rule_tac ?G1.0="G1" and ?G2.0="G2" in cfgSTD_to_cfgLM_translate_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule cfgSTD.derivation_initial_belongs)
   apply(force)
  apply(force)
  done

lemma cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals_1: "
  valid_cfg G
  \<Longrightarrow> cfgLM_Nonblockingness_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G"
  apply(simp add: cfgLM_Nonblockingness_nonterminals_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rule_tac x="derivation_take d n" in exI)
  apply(rule_tac x="w'" in exI)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(rule conjI)
   apply (metis cfgLM_derivations_are_cfg_derivations cfgSTD.derivation_take_preserves_derivation)
  apply(rule conjI)
   apply(simp add: derivation_take_def)
  apply(rule conjI)
   apply (metis cfgLM_derivations_are_cfg_derivations cfgSTD.derivation_take_preserves_derivation)
  apply(rule_tac x="n" in exI)
  apply(simp add: derivation_take_def)
  done

lemma cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals_2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G \<subseteq> cfgLM_Nonblockingness_nonterminals G"
  apply(simp add: cfgLM_Nonblockingness_nonterminals_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac n="n" and d="derivation_take d n" in cfg_derivation_can_be_translated_to_cfgLM_derivation)
        apply(force)
       apply (metis cfgLM_derivations_are_cfg_derivations cfgSTD.derivation_take_preserves_derivation)
      apply (metis maximum_of_domain_derivation_take option.distinct(1))
     apply(simp add: derivation_take_def)
     apply(case_tac "d 0")
      apply(force)
     apply(force)
    apply(simp add: derivation_take_def)
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="d'" in exI)
  apply(clarsimp)
  apply(rule_tac x="n" in exI)
  apply(clarsimp)
  done

lemma cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G = cfgLM_Nonblockingness_nonterminals G"
  apply(rule antisym)
   apply(metis cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals_2 cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals_1)
  apply(metis cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals_2 cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals_1)
  done

lemma cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp4: "
valid_cfg G \<Longrightarrow>
    cfg_nonterminals G = cfgLM_language_relevant_nonterminals G \<Longrightarrow>
    cfgLM_language_relevant_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G"
  apply(simp (no_asm) add: cfgLM_language_relevant_nonterminals_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule earliest_occurence_in_list)
   apply(force)
  apply(clarsimp)
  apply(simp add: setAConcat)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(simp add: cfg_configurations_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(case_tac ca)
  apply(rename_tac w)
  apply(case_tac c)
  apply(clarsimp)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>wx. w=liftB wx")
   prefer 2
   apply(rule_tac x="filterB w" in exI)
   apply (metis liftBDeConv2)
  apply(clarsimp)
  apply(case_tac "i<n")
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac n="i" and m="n" and d="d" in cfgLM.step_detail_before_some_position)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(case_tac "i=n")
   apply(clarsimp)
   apply (metis liftB_with_nonterminal_inside)
  apply(subgoal_tac "n<i")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "maximum_of_domain d i")
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(case_tac "d (Suc i)")
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac n="i" and m="Suc i" and d="d" in cfgLM.step_detail_before_some_position)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac n="i-n" and d="derivation_drop d n" and w'="liftB wx" and ?w1.0="w1" and ?w2.0="teA x # w2" in CFGLM_derivationCanBeDecomposed2_with_labels)
     apply(force)
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(rule context_conjI)
     apply(rule_tac m="i-n" in cfgLM.derivation_drop_preserves_derivation)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(clarsimp)
    apply(clarsimp)
    apply(rule conjI)
     apply(simp add: derivation_drop_def)
    apply(rule_tac x="i-n" in exI)
    apply(simp add: derivation_drop_def)
    apply(simp add: maximum_of_domain_def)
   apply(simp add: derivation_drop_def)
   apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac n="nb" and d="d2" and w'="w2'" and ?w1.0="[teA x]" and ?w2.0="w2" in CFGLM_derivationCanBeDecomposed2_with_labels)
     apply(force)
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(rule_tac x="nb" in exI)
    apply(clarsimp)
   apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
  apply(rule_tac x="d1a" in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply (metis cfgLM_derivations_are_cfg_derivations)
  apply(rule_tac x="w1'a" in exI)
  apply(rule context_conjI)
   apply(rule_tac x="nb" in exI)
   apply(clarsimp)
  apply(clarsimp)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "X" for X)
  apply(thin_tac "maximum_of_domain d1 n1")
  apply(thin_tac "       maximum_of_domain d2 n2")
  apply(thin_tac "       n1 + n2 = i - n ")
  apply(thin_tac "       set (get_labels (derivation_drop d n) (i - n)) =
       set (get_labels d1 n1) \<union> set (get_labels d2 n2)")
  apply(thin_tac "       case d1 0 of None \<Rightarrow> False | Some x \<Rightarrow> x \<in> {pair None \<lparr>cfg_conf = w1\<rparr>}")
  apply(thin_tac "       case d2 0 of None \<Rightarrow> False
       | Some xa \<Rightarrow> xa \<in> {pair None \<lparr>cfg_conf = teA x # w2\<rparr>}")
  apply (metis liftBSplit prefix_also_no_nonterms)
  done

lemma cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp5: "
valid_cfg G \<Longrightarrow>
    cfg_nonterminals G = cfgLM_language_relevant_nonterminals G \<Longrightarrow>
    cfgLM_language_relevant_nonterminals G \<subseteq> cfgLM_accessible_nonterminals G"
  apply(simp (no_asm) add: cfgLM_language_relevant_nonterminals_def cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule earliest_occurence_in_list)
   apply(force)
  apply(clarsimp)
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(case_tac ca)
  apply(clarsimp)
  apply(rename_tac w)
  apply(simp add: setAConcat)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac w="w1" in construct_elimininating_derivation_prime)
     apply(force)
    apply(rule antisym)
     prefer 2
     apply(simp add: cfgSTD_Nonblockingness_nonterminals_def cfg_configurations_def)
     apply(force)
    apply(metis cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp4)
   apply(simp add: cfg_configurations_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
   apply(force)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: cfg_configurations_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(case_tac c)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>wx. w=liftB wx")
   prefer 2
   apply(rule_tac x="filterB w" in exI)
   apply (metis liftBDeConv2)
  apply(clarsimp)
  apply(case_tac "i<n")
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac n="i" and m="n" and d="d" in cfgLM.step_detail_before_some_position)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(case_tac "i=n")
   apply(clarsimp)
   apply (metis liftB_with_nonterminal_inside)
  apply(subgoal_tac "n<i")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "maximum_of_domain d i")
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(case_tac "d (Suc i)")
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac n="i" and m="Suc i" and d="d" in cfgLM.step_detail_before_some_position)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(rule_tac x="derivation_append d (derivation_map da (%c. \<lparr>cfg_conf=(cfg_conf c)@teA x # w2\<rparr>)) n" in exI)
  apply(rule conjI)
   prefer 2
   apply(rule_tac x="n+na" in exI)
   apply(simp add: derivation_append_def derivation_map_def get_configuration_def)
   apply(rule conjI)
    apply(clarsimp)
    apply(force)
   apply(force)
  apply(rule cfgLM.derivation_append_preserves_derivation_initial)
    apply(force)
   apply(force)
  apply(rule cfgLM.derivation_append_preserves_derivation)
    apply(simp add: cfgLM.derivation_initial_def)
   apply(rule cfgLM.derivation_map_preserves_derivation2)
    apply(simp add: cfgLM.derivation_initial_def cfgLM_step_relation_def)
   apply(simp add: cfgLM.derivation_initial_def cfgLM_step_relation_def)
   apply(clarsimp)
   apply(case_tac a)
   apply(case_tac b)
   apply(clarsimp)
   apply(rule_tac x="l" in exI)
   apply(force)
  apply(case_tac "d n")
   apply(clarsimp)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  done

lemma cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp1: "
valid_cfg G \<Longrightarrow>
    cfg_nonterminals G =
    cfgLM_accessible_nonterminals G \<inter> cfgSTD_Nonblockingness_nonterminals G \<Longrightarrow>
    cfgLM_accessible_nonterminals G \<inter> cfgSTD_Nonblockingness_nonterminals G
    \<subseteq> cfgLM_language_relevant_nonterminals G"
  apply(simp (no_asm) add: cfgLM_language_relevant_nonterminals_def cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(clarsimp)
  apply(clarsimp)
  apply(case_tac a)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac w="liftB w1 @ teA x # w2" in construct_elimininating_derivation_prime)
     apply(force)
    apply(rule antisym)
     apply(force)
    apply(simp add: cfgSTD_Nonblockingness_nonterminals_def cfg_configurations_def)
    apply(force)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def cfg_configurations_def)
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="derivation_append d da n" in exI)
  apply(rule conjI)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(force)
    apply(force)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(simp add: cfg_marking_condition_def derivation_append_def)
   apply(rule_tac x="n+na" in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(clarsimp)
    apply (metis liftB_with_nonterminal_inside)
   apply(clarsimp)
   apply(subgoal_tac "\<lparr>cfg_conf = liftB v\<rparr> \<in> SSX" for SSX)
    prefer 2
    apply(rule_tac d="da" in cfgLM.belongs_configurations)
     apply(rule cfgLM.derivation_belongs)
        apply(force)
       apply(force)
      apply(case_tac c)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: cfg_marking_configuration_def)
   apply (metis setA_liftB_empty)
  apply(rule_tac x="n" in exI)
  apply(simp add: derivation_append_def)
  apply(simp add: setAConcat)
  done

lemma cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp2: "
valid_cfg G \<Longrightarrow>
    cfg_nonterminals G =
    cfgLM_accessible_nonterminals G \<inter> cfgSTD_Nonblockingness_nonterminals G \<Longrightarrow>
    cfgLM_language_relevant_nonterminals G \<subseteq> cfgLM_accessible_nonterminals G"
  apply(simp add: cfgLM_language_relevant_nonterminals_def cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(simp add: cfg_configurations_def)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule earliest_occurence_in_list)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac w="w1" in construct_elimininating_derivation_prime)
     apply(force)
    apply(rule antisym)
     apply(force)
    apply(simp add: cfgSTD_Nonblockingness_nonterminals_def cfg_configurations_def)
    apply(force)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def cfg_configurations_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
   apply(force)
  apply(clarsimp)
  apply(rule_tac x="derivation_append d (derivation_map da (%c. \<lparr>cfg_conf=(cfg_conf c)@[teA x]@w2\<rparr>)) n" in exI)
  apply(rule conjI)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(force)
    apply(force)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rule cfgLM.derivation_map_preserves_derivation2)
     apply(simp add: cfgLM.derivation_initial_def cfgLM_step_relation_def)
    apply(simp add: cfgLM.derivation_initial_def cfgLM_step_relation_def)
    apply(clarsimp)
    apply(case_tac a)
    apply(case_tac b)
    apply(clarsimp)
    apply(force)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rule_tac x="n+na" in exI)
  apply(simp add: derivation_append_def derivation_map_def)
  apply(simp add: cfg_configurations_def get_configuration_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(force)
  done

lemma cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp3: "
valid_cfg G \<Longrightarrow>
    cfg_nonterminals G =
    cfgLM_accessible_nonterminals G \<inter> cfgSTD_Nonblockingness_nonterminals G \<Longrightarrow>
    cfgLM_language_relevant_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G"
  apply(clarsimp)
  apply(simp add: cfgLM_language_relevant_nonterminals_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(simp add: cfg_configurations_def)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule earliest_occurence_in_list)
   apply(force)
  apply(clarsimp)
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(case_tac ca)
  apply(clarsimp)
  apply(rename_tac w)
  apply(case_tac "i<n")
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac n="i" and m="n" and d="d" in cfgLM.step_detail_before_some_position)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(case_tac "i=n")
   apply(clarsimp)
  apply(simp add: setAConcat)
  apply(subgoal_tac "n<i")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "maximum_of_domain d i")
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(case_tac "d (Suc i)")
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac n="i" and m="Suc i" and d="d" in cfgLM.step_detail_before_some_position)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac  n="i-n" and d="derivation_drop d n" and w'="w" and ?w1.0="w1" and ?w2.0="teA x # w2" in CFGLM_derivationCanBeDecomposed2_with_labels)
     apply(force)
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(rule context_conjI)
     apply(rule_tac m="i-n" in cfgLM.derivation_drop_preserves_derivation)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(clarsimp)
    apply(clarsimp)
    apply(rule conjI)
     apply(simp add: derivation_drop_def)
    apply(rule_tac x="i-n" in exI)
    apply(simp add: derivation_drop_def)
    apply(simp add: maximum_of_domain_def)
   apply(simp add: derivation_drop_def)
   apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac  n="nb" and d="d2" and w'="w2'" and ?w1.0="[teA x]" and ?w2.0="w2" in CFGLM_derivationCanBeDecomposed2_with_labels)
     apply(force)
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(rule_tac x="nb" in exI)
    apply(clarsimp)
   apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rule_tac x="d1a" in exI)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
  apply(clarsimp)
  apply(rule_tac x="w1'a" in exI)
  apply(simp add: setAConcat)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(rule conjI)
   prefer 2
   apply(rule_tac x="nb" in exI)
   apply(clarsimp)
  apply (metis cfgLM_derivations_are_cfg_derivations)
  done

lemma cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgLM_accessible_nonterminals G \<inter> cfgSTD_Nonblockingness_nonterminals G
   \<longleftrightarrow> cfg_nonterminals G = cfgLM_language_relevant_nonterminals G"
  apply(rule antisym)
   apply(clarsimp)
   apply(rule antisym)
    apply(rule cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp1)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule conjI)
    apply(rule cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp2)
     apply(force)
    apply(force)
   apply(rule cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp3)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule antisym)
   apply(clarsimp)
   apply(rule conjI)
    apply(rule cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp5)
     apply(force)
    apply(force)
   apply(rule cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_hlp4)
    apply(force)
   apply(force)
  apply(rule_tac t="cfgLM_language_relevant_nonterminals G" and s="cfg_nonterminals G" in ssubst)
   apply(force)
  apply(simp (no_asm) add: cfgLM_accessible_nonterminals_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(force)
  done

lemma CFGLM_Nonblockingness_from_cfgLM_Nonblockingness_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgLM_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G"
  apply(simp add: cfgLM.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   prefer 2
   apply (metis cfgLM.derivation_initial_is_derivation cfgLM.some_position_at_max_dom)
  apply(clarsimp)
  apply(case_tac c)
  apply(clarsimp)
  apply(rename_tac w)
  apply(subgoal_tac "\<lparr>cfg_conf = w\<rparr> \<in> cfg_configurations G")
   prefer 2
   apply (metis cfgLM.derivation_initial_configurations)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac w="w" in construct_elimininating_derivation_prime)
     apply(force)
    apply (metis cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals)
   apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule cfgLM.derivation_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule_tac x="na" in exI)
   apply(rule cfgLM_maximum_of_domain_by_nonterminal_free)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: derivation_append_fit_def)
  apply(simp add: cfg_marking_condition_def)
  apply(rule_tac x="n+na" in exI)
  apply(simp add: derivation_append_def cfg_marking_configuration_def)
  apply(rule conjI)
   apply(clarsimp)
   apply (metis setA_liftB_empty)
  apply(clarsimp)
  apply(rule conjI)
   apply (metis setA_liftB_empty)
  apply(rule_tac d="d" in cfgLM.belongs_configurations)
   apply(rule cfgLM.derivation_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfgLM_language_relevant_nonterminals_vs_cfgLM_accessible_nonterminals_and_cfgSTD_Nonblockingness_nonterminals_in_cfgSTD_Nonblockingness_nonterminals_grammar: "
valid_cfg G \<Longrightarrow>
          valid_cfg G' \<Longrightarrow>
          cfg_sub G' G \<Longrightarrow>
          cfg_nonterminals G' = cfgSTD_Nonblockingness_nonterminals G' \<Longrightarrow>
          cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G' =
          cfgLM_language_relevant_nonterminals G'"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(simp add: cfgLM_language_relevant_nonterminals_def cfgLM_accessible_nonterminals_def)
   apply(clarsimp)
   apply(case_tac c)
   apply(clarsimp)
   apply(case_tac "d n")
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(clarsimp)
   apply(rename_tac e)
   apply(subgoal_tac "ATS_Language0.Nonblockingness_branching cfg_configurations cfg_initial_configurations
        cfg_step_labels cfgLM_step_relation cfg_marking_condition G'")
    prefer 2
    apply (metis CFGLM_Nonblockingness_from_cfgLM_Nonblockingness_nonterminals cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals)
   apply(simp add: cfgLM.Nonblockingness_branching_def)
   apply(erule_tac x="derivation_take d n" in allE)
   apply(erule impE)
    apply(rule cfgLM.derivation_take_preserves_derivation_initial)
    apply(clarsimp)
   apply(erule_tac x="n" in allE)
   apply(erule impE)
    apply (metis maximum_of_domain_derivation_take option.distinct(1))
   apply(clarsimp)
   apply(rule_tac x="derivation_append (derivation_take d n) dc n" in exI)
   apply(rule conjI)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(force)
     apply(rule cfgLM.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rule cfgLM.derivation_take_preserves_derivation)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(force)
    apply(simp add: derivation_take_def derivation_append_fit_def)
    apply(case_tac "dc 0")
     apply(force)
    apply(case_tac a)
    apply(clarsimp)
    apply(simp add: cfgLM.derivation_initial_def)
    apply(clarsimp)
    apply(case_tac x1)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule_tac x="n" in exI)
   apply(simp add: derivation_append_def derivation_take_def)
   apply(simp add: setAConcat)
  apply(clarsimp)
  apply(rule propSym)
  apply(rule conjI)
   apply(simp add: cfgLM_language_relevant_nonterminals_def)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule cfgLM.belongs_configurations)
     apply(rule cfgLM.derivation_initial_belongs)
      prefer 2
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: cfg_configurations_def)
   apply(clarsimp)
   apply(force)
  apply(simp add: cfgLM_language_relevant_nonterminals_def cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rule cfgLM.derivation_initial_belongs)
     prefer 2
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule earliest_occurence_in_list)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="G'" in cfgLM_Nonblockingness_branching_implies_FB_iterated_elimination)
       apply(force)
      apply (metis CFGLM_Nonblockingness_from_cfgLM_Nonblockingness_nonterminals cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  done

lemma cfgSTD_accessible_nonterminals_vs_cfgLM_accessible_nonterminals_1: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgSTD_accessible_nonterminals G \<subseteq> cfgLM_accessible_nonterminals G"
  apply(rule_tac B="cfgSTD_accessible_nonterminals_ALT G" in subset_trans)
   apply(rule cfgSTD_accessible_nonterminals_vs_cfgSTD_accessible_nonterminals_ALT_1)
   apply(force)
  apply(rule cfgSTD_accessible_nonterminals_ALT_contained_in_cfgLM_accessible_nonterminals)
   apply(force)
  apply(rule CFGLM_Nonblockingness_from_cfgLM_Nonblockingness_nonterminals)
   apply(force)
  apply(rule_tac t="cfgLM_Nonblockingness_nonterminals G" in subst)
   apply(rule cfgLM_Nonblockingness_nonterminals_vs_cfgSTD_Nonblockingness_nonterminals)
   apply(force)
  apply(force)
  done

lemma cfgSTD_accessible_nonterminals_vs_cfgLM_accessible_nonterminals_2: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgLM_accessible_nonterminals G \<subseteq> cfgSTD_accessible_nonterminals G"
  apply(simp add: cfgLM_accessible_nonterminals_def cfgSTD_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(rule conjI)
   apply (metis CFGLM_to_CFG_derivation_initial)
  apply(rule_tac x="n" in exI)
  apply(rule_tac x="c" in exI)
  apply(clarsimp)
  apply (metis elemInsetA)
  done

lemma cfgSTD_accessible_nonterminals_vs_cfgLM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgSTD_accessible_nonterminals G = cfgLM_accessible_nonterminals G"
  apply(rule antisym)
   apply(metis cfgSTD_accessible_nonterminals_vs_cfgLM_accessible_nonterminals_2 cfgSTD_accessible_nonterminals_vs_cfgLM_accessible_nonterminals_1)
  apply(metis cfgSTD_accessible_nonterminals_vs_cfgLM_accessible_nonterminals_2 cfgSTD_accessible_nonterminals_vs_cfgLM_accessible_nonterminals_1)
  done

lemma construct_elimininating_derivation: "
  valid_cfg G'
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G'
  \<Longrightarrow> \<exists>d n e v.
  cfgLM.derivation G' d
  \<and> d 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>)
  \<and> d n = Some (pair e \<lparr>cfg_conf=liftB v\<rparr>)"
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
   prefer 2
   apply(rule canElimCombine)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d w')(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def)
  apply(simp add: cfgSTD.derivation_to_def)
  apply(simp add: cfgSTD.derivation_from_def)
  apply(clarsimp)
  apply(rename_tac d w' n x)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac d w' n x)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' n x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' n x)(*strict*)
  apply(subgoal_tac "\<exists>d' e. cfgLM.derivation G' d' \<and> maximum_of_domain d' n \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>) \<and> d' n = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac d w' n x)(*strict*)
   prefer 2
   apply(rule cfg_derivation_can_be_translated_to_cfgLM_derivation)
        apply(rename_tac d w' n x)(*strict*)
        apply(force)
       apply(rename_tac d w' n x)(*strict*)
       apply(force)
      apply(rename_tac d w' n x)(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac d w' n x)(*strict*)
     apply(force)
    apply(rename_tac d w' n x)(*strict*)
    apply(force)
   apply(rename_tac d w' n x)(*strict*)
   apply(force)
  apply(rename_tac d w' n x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' n x d' e)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="filterB w'"
      in exI)
  apply (metis liftBDeConv2)
  done

lemma construct_elimininating_trans_der_list: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> \<exists>ds f\<pi> fw. cfgLM.trans_der_list G ds (map (\<lambda>w. \<lparr>cfg_conf=[w]\<rparr>) w) f\<pi> (map (\<lambda>w. \<lparr>cfg_conf=w\<rparr>) fw) \<and> setA (foldl (@) [] fw) = {}"
  apply(induct w)
   apply(clarsimp)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_list_def)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w ds f\<pi> fw)(*strict*)
  apply(case_tac a)
   apply(rename_tac a w ds f\<pi> fw aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w ds f\<pi> fw aa)(*strict*)
   apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA aa]\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
    apply(rename_tac w ds f\<pi> fw aa)(*strict*)
    prefer 2
    apply(rule canElimCombine)
     apply(rename_tac w ds f\<pi> fw aa)(*strict*)
     apply(force)
    apply(rename_tac w ds f\<pi> fw aa)(*strict*)
    apply(force)
   apply(rename_tac w ds f\<pi> fw aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w ds f\<pi> fw aa d w')(*strict*)
   apply(simp add: cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.derivation_from_to_def)
   apply(clarsimp)
   apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
   apply(subgoal_tac "\<exists>d' e. cfgLM.derivation SSG d' \<and> maximum_of_domain d' SSn \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSw1\<rparr>) \<and> d' SSn = Some (pair e \<lparr>cfg_conf = SSw2\<rparr>)" for SSG SSw1 SSn SSw2)
    apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
    prefer 2
    apply(rule_tac
      n="n"
      and d="d"
      in cfg_derivation_can_be_translated_to_cfgLM_derivation)
         apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
         apply(force)
        apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
        apply(force)
       apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
       apply(simp add: maximum_of_domain_def)
      apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
      apply(case_tac "d 0")
       apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
       apply(force)
      apply(rename_tac w ds f\<pi> fw aa d w' n x a)(*strict*)
      apply(force)
     apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
    apply(force)
   apply(rename_tac w ds f\<pi> fw aa d w' n x)(*strict*)
   apply(thin_tac "case d 0 of None \<Rightarrow> False | Some x \<Rightarrow> x \<in> {pair None \<lparr>cfg_conf = [teA aa]\<rparr>}")
   apply(thin_tac "d (Suc n) = None")
   apply(thin_tac "d n = Some (pair x \<lparr>cfg_conf = w'\<rparr>)")
   apply(thin_tac "cfgSTD.derivation G d")
   apply(clarsimp)
   apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
   apply(rule_tac
      x="d'#ds"
      in exI)
   apply(rule_tac
      x="map the (get_labels d' n)#f\<pi>"
      in exI)
   apply(rule_tac
      x="w'#fw"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
    apply(simp add: cfgLM.trans_der_list_def)
    apply(clarsimp)
    apply(rename_tac w ds f\<pi> fw aa w' n d' e i)(*strict*)
    apply(case_tac i)
     apply(rename_tac w ds f\<pi> fw aa w' n d' e i)(*strict*)
     apply(clarsimp)
     apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
     apply(rule conjI)
      apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
      apply(rule cfgLM.derivation_belongs)
         apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
         apply(force)
        apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
        apply(force)
       apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
       apply(simp add: cfg_configurations_def)
      apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
      apply(force)
     apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
     apply(rule_tac
      t="length (get_labels d' n)"
      and s="n"
      in ssubst)
      apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
      apply (metis get_labels_length)
     apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
     apply(rule conjI)
      apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
      apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
       apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
       apply(force)
      apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
      apply(force)
     apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
     apply(force)
    apply(rename_tac w ds f\<pi> fw aa w' n d' e i nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac w ds f\<pi> fw aa w' n d' e)(*strict*)
   apply (metis setA_app empty_subsetI foldl_first subset_empty)
  apply(rename_tac a w ds f\<pi> fw b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w ds f\<pi> fw b)(*strict*)
  apply(rule_tac
      x="(der1 \<lparr>cfg_conf=[teB b]\<rparr>)#ds"
      in exI)
  apply(rule_tac
      x="[]#f\<pi>"
      in exI)
  apply(rule_tac
      x="[teB b]#fw"
      in exI)
  apply(rule conjI)
   apply(rename_tac w ds f\<pi> fw b)(*strict*)
   apply(simp add: cfgLM.trans_der_list_def)
   apply(clarsimp)
   apply(rename_tac w ds f\<pi> fw b i)(*strict*)
   apply(case_tac i)
    apply(rename_tac w ds f\<pi> fw b i)(*strict*)
    apply(clarsimp)
    apply(rename_tac w ds f\<pi> fw b)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(rule conjI)
     apply(rename_tac w ds f\<pi> fw b)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac w ds f\<pi> fw b)(*strict*)
    apply(rule conjI)
     apply(rename_tac w ds f\<pi> fw b)(*strict*)
     apply(rule cfgLM.der1_belongs)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac w ds f\<pi> fw b)(*strict*)
    apply(rule conjI)
     apply(rename_tac w ds f\<pi> fw b)(*strict*)
     apply(simp add: der1_def)
     apply(simp add: get_labels_def)
     apply (metis nat_seqEmpty zero_less_Suc)
    apply(rename_tac w ds f\<pi> fw b)(*strict*)
    apply(rule conjI)
     apply(rename_tac w ds f\<pi> fw b)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac w ds f\<pi> fw b)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac w ds f\<pi> fw b i nat)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac w ds f\<pi> fw b)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) [teB b] fw"
      and s="[teB b]@foldl (@) [] fw"
      in ssubst)
   apply(rename_tac w ds f\<pi> fw b)(*strict*)
   apply (metis append_Cons eq_Nil_appendI foldl_append_initial_pullout)
  apply(rename_tac w ds f\<pi> fw b)(*strict*)
  apply (metis setA_Cons_teB setA_take_head append_Cons eq_Nil_appendI equalityI subset_refl)
  done

lemma trans_der_construct_elimininating_derivation_prime: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> \<lparr>cfg_conf=w\<rparr> \<in> cfg_configurations G
  \<Longrightarrow> \<exists>d \<pi> v. cfgLM.trans_der G d \<lparr>cfg_conf=w\<rparr> \<pi> \<lparr>cfg_conf=liftB v\<rparr>"
  apply(subgoal_tac "\<exists>d n e v. cfgLM.derivation SSG d \<and> d 0 = Some (pair None \<lparr>cfg_conf = SSw\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB v\<rparr>)" for SSG SSw)
   prefer 2
   apply(rule_tac
      w="w"
      in construct_elimininating_derivation_prime)
     apply(force)
    apply(force)
   apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac d n e v)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule_tac
      x="map the (get_labels d n)"
      in exI)
  apply(rule_tac
      x="v"
      in exI)
  apply(simp add: cfgLM.trans_der_def)
  apply(rule_tac
      t="length (get_labels d n)"
      and s="n"
      in ssubst)
   apply(rename_tac d n e v)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac d n e v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n e v)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac d n e v)(*strict*)
      apply(force)
     apply(rename_tac d n e v)(*strict*)
     apply(force)
    apply(rename_tac d n e v)(*strict*)
    apply(force)
   apply(rename_tac d n e v)(*strict*)
   apply(force)
  apply(rename_tac d n e v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n e v)(*strict*)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac d n e v)(*strict*)
    apply(force)
   apply(rename_tac d n e v)(*strict*)
   apply(force)
  apply(rename_tac d n e v)(*strict*)
  apply(force)
  done

lemma cfgSTD_Nonblockingness_nonterminals_ALT3_cfgSTD_Nonblockingness_nonterminals: "
  valid_cfg G
  \<Longrightarrow> A \<in> cfgSTD_Nonblockingness_nonterminals_ALT3 G
  \<Longrightarrow> A \<in> cfgSTD_Nonblockingness_nonterminals G"
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_ALT3_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(rule conjI)
   prefer 2
   apply(clarsimp)
   apply(rename_tac d \<pi> w)(*strict*)
   apply(rule_tac
      x="derivation_take d (length \<pi>)"
      in exI)
   apply(rule_tac
      x="liftB w"
      in exI)
   apply(simp add: setA_liftB)
   apply(simp add: cfgLM.trans_der_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.derivation_from_to_def)
   apply(rule conjI)
    apply(rename_tac d \<pi> w)(*strict*)
    apply(rule cfgLM_derivations_are_cfg_derivations)
    apply(rule cfgLM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d \<pi> w)(*strict*)
   apply(rule conjI)
    apply(rename_tac d \<pi> w)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d \<pi> w)(*strict*)
   apply(rule conjI)
    apply(rename_tac d \<pi> w)(*strict*)
    apply(rule cfgLM_derivations_are_cfg_derivations)
    apply(rule cfgLM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d \<pi> w)(*strict*)
   apply(rule_tac
      x="length \<pi>"
      in exI)
   apply(simp add: derivation_take_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac d \<pi> w)(*strict*)
  apply(case_tac "\<pi>")
   apply(rename_tac d \<pi> w)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(case_tac w)
    apply(rename_tac d w)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d \<pi> w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w a list)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac d w a list)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d w a list e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (a#list)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d w a list e)(*strict*)
     apply(force)
    apply(rename_tac d w a list e)(*strict*)
    apply(force)
   apply(rename_tac d w a list e)(*strict*)
   apply(force)
  apply(rename_tac d w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w a list e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d w a list e1 e2 c1 c2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac d w a list e1 e2 c1 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w a list e1 e2 c2 l r)(*strict*)
  apply(subgoal_tac "a=e2")
   apply(rename_tac d w a list e1 e2 c2 l r)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule_tac
      d="d"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac d w a list e1 e2 c2 l r)(*strict*)
       apply(force)
      apply(rename_tac d w a list e1 e2 c2 l r)(*strict*)
      apply(force)
     apply(rename_tac d w a list e1 e2 c2 l r)(*strict*)
     apply(force)
    apply(rename_tac d w a list e1 e2 c2 l r)(*strict*)
    apply(force)
   apply(rename_tac d w a list e1 e2 c2 l r)(*strict*)
   apply(force)
  apply(rename_tac d w a list e1 e2 c2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w list e1 e2 c2 l r)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac d w list e2 c2 l r e)(*strict*)
  apply(case_tac l)
   apply(rename_tac d w list e2 c2 l r e)(*strict*)
   prefer 2
   apply(rename_tac d w list e2 c2 l r e a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w list e2 c2 l r e)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w list e2 c2 e)(*strict*)
  apply(simp add: valid_cfg_def)
  done

lemma cfgSTD_Nonblockingness_nonterminals_cfgSTD_Nonblockingness_nonterminals_ALT3: "
  valid_cfg G
  \<Longrightarrow> A \<in> cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> A \<in> cfgSTD_Nonblockingness_nonterminals_ALT3 G"
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_ALT3_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac d w')(*strict*)
  apply(simp add: cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_from_to_def)
  apply(clarsimp)
  apply(rename_tac d w' n x)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac d w' n x)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w' n x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w' n x)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = w'")
   apply(rename_tac d w' n x)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB w'"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac d w' n x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n x l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "X" for X)
   apply(rename_tac d n x l')(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and n="n"
      in cfg_derivation_can_be_translated_to_cfgLM_derivation)
        apply(rename_tac d n x l')(*strict*)
        apply(force)
       apply(rename_tac d n x l')(*strict*)
       apply(force)
      apply(rename_tac d n x l')(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac d n x l')(*strict*)
     apply(force)
    apply(rename_tac d n x l')(*strict*)
    apply(force)
   apply(rename_tac d n x l')(*strict*)
   apply(simp add: setA_liftB)
  apply(rename_tac d n x l')(*strict*)
  apply(clarsimp)
  apply(rename_tac d n x l' d' e)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(rule_tac
      x="map the (get_labels d' n)"
      in exI)
  apply(rule_tac
      x="l'"
      in exI)
  apply(simp add: cfgLM.trans_der_def)
  apply(rule conjI)
   apply(rename_tac d n x l' d' e)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac d n x l' d' e)(*strict*)
      apply(force)
     apply(rename_tac d n x l' d' e)(*strict*)
     apply(force)
    apply(rename_tac d n x l' d' e)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac d n x l' d' e)(*strict*)
   apply(force)
  apply(rename_tac d n x l' d' e)(*strict*)
  apply(rule_tac
      t="length (get_labels d' n)"
      and s="n"
      in ssubst)
   apply(rename_tac d n x l' d' e)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac d n x l' d' e)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n x l' d' e)(*strict*)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac d n x l' d' e)(*strict*)
    apply(force)
   apply(rename_tac d n x l' d' e)(*strict*)
   apply(force)
  apply(rename_tac d n x l' d' e)(*strict*)
  apply(clarsimp)
  done

lemma elim_map_equal_by_CFGlm_unambiguous: "
  valid_cfg G
  \<Longrightarrow> CFGlm_unambiguous G
  \<Longrightarrow> cfg_nonterminals G = cfgLM_accessible_nonterminals G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> elim_map G v \<pi>1 (map (\<lambda>x. []) ns)
  \<Longrightarrow> elim_map G v \<pi>2 (map (\<lambda>x. []) ns)
  \<Longrightarrow> length v=length \<pi>1
  \<Longrightarrow> length v=length \<pi>2
  \<Longrightarrow> length v=length ns
  \<Longrightarrow> \<pi>1=\<pi>2"
  apply(rule listEqI)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: elim_map_def)
  apply(erule_tac
      x="i"
      in allE)+
  apply(clarsimp)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = [teA (v ! i)]\<rparr> \<in> cfg_configurations G")
   apply(rename_tac i d da n na e ea)(*strict*)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac i d da n na e ea)(*strict*)
    apply(force)
   apply(rename_tac i d da n na e ea)(*strict*)
   apply(force)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(simp add: CFGlm_unambiguous_def)
  apply(subgoal_tac "v!i \<in> cfgLM_accessible_nonterminals G")
   apply(rename_tac i d da n na e ea)(*strict*)
   prefer 2
   apply(simp add: cfg_configurations_def)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(subgoal_tac "\<exists>d n c. cfgLM.derivation_initial G d \<and> get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA (v!i) # w2)")
   apply(rename_tac i d da n na e ea)(*strict*)
   prefer 2
   apply(thin_tac "cfg_nonterminals G = cfgLM_accessible_nonterminals G")
   apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(rename_tac i d da n na e ea)(*strict*)
  apply(thin_tac "v ! i \<in> cfgLM_accessible_nonterminals G")
  apply(clarsimp)
  apply(rename_tac i d da n na e ea db nb c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac i d da n na e ea db nb c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i d da n na e ea db nb w1 w2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "db nb")
   apply(rename_tac i d da n na e ea db nb w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac i d da n na e ea db nb w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac i d da n na e ea db nb w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i d da n na e ea db nb w1 w2 option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB w1 @ teA (v ! i) # w2\<rparr> \<in> cfg_configurations G")
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
   apply(force)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
  apply(subgoal_tac "\<exists>d n e v. cfgLM.derivation SSG d \<and> d 0 = Some (pair None \<lparr>cfg_conf = SSw\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB v\<rparr>)" for SSG SSw)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
   prefer 2
   apply(rule_tac
      w="liftB w1 @ w2"
      in construct_elimininating_derivation_prime)
     apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
    apply(force)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(simp add: simpY)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e)(*strict*)
  apply(clarsimp)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
  apply(thin_tac "cfgSTD_Nonblockingness_nonterminals G = cfgLM_accessible_nonterminals G")
  apply(thin_tac "cfg_nonterminals G = cfgLM_accessible_nonterminals G")
  apply(subgoal_tac "\<lparr>cfg_conf = liftB w1 @ w2\<rparr> \<in> cfg_configurations G")
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   prefer 2
   apply(simp add: cfg_configurations_def simpY)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
  apply(subgoal_tac "length (get_labels da na)=na")
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
  apply(subgoal_tac "length (get_labels d n)=n")
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
  apply(subgoal_tac "n=length (\<pi>1!i)")
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   prefer 2
   apply(rule_tac
      t="n"
      and s="length (get_labels d n)"
      in ssubst)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(force)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(rule_tac
      t="length (get_labels d n)"
      and s="length(map the (get_labels d n))"
      in subst)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(rule length_map)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(force)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
  apply(subgoal_tac "na=length (\<pi>2!i)")
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   prefer 2
   apply(rule_tac
      t="na"
      and s="length (get_labels da na)"
      in ssubst)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(force)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(rule_tac
      t="length (get_labels da na)"
      and s="length(map the (get_labels da na))"
      in subst)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(rule length_map)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(force)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
  apply(subgoal_tac "\<exists>d'. cfgLM.trans_der G d' \<lparr>cfg_conf = liftB w1 @ teA (v ! i) # w2\<rparr> (map the (get_labels d n)) \<lparr>cfg_conf = liftB w1 @ w2\<rparr>")
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(subgoal_tac "\<exists>da'. cfgLM.trans_der G da' \<lparr>cfg_conf = liftB w1 @ teA (v ! i) # w2\<rparr> (map the (get_labels da na)) \<lparr>cfg_conf = liftB w1 @ w2\<rparr>")
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(clarsimp)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
    apply(erule_tac
      x="derivation_append db (derivation_append d' dc (length (\<pi>1!i))) nb"
      in allE)
    apply(erule impE)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation_initial)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
       apply(force)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
       apply(simp add: cfgLM.derivation_initial_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
      apply(rule cfgLM.derivation_append_preserves_derivation)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
        apply(simp add: cfgLM.trans_der_def)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
       apply(simp add: cfgLM.trans_der_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
      apply(simp add: cfgLM.trans_der_def)
      apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_append_def)
     apply(simp add: cfgLM.trans_der_def)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
    apply(erule_tac
      x="derivation_append db (derivation_append da' dc (length (\<pi>2!i))) nb"
      in allE)
    apply(erule impE)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation_initial)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
       apply(force)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
       apply(simp add: cfgLM.derivation_initial_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
      apply(rule cfgLM.derivation_append_preserves_derivation)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
        apply(simp add: cfgLM.trans_der_def)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
       apply(simp add: cfgLM.trans_der_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
      apply(simp add: cfgLM.trans_der_def)
      apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_append_def)
     apply(simp add: cfgLM.trans_der_def)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da')(*strict*)
    apply(erule_tac
      x="nb+length(\<pi>1!i)+nc"
      in allE)
    apply(erule_tac
      x="nb+length(\<pi>2!i)+nc"
      in allE)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(erule_tac
      x="if nc=0 then (if(length (\<pi>1!i))=0 then ea else ec) else eb"
      in allE)
    apply(erule_tac
      x="if nc=0 then (if(length (\<pi>2!i))=0 then ea else ed) else eb"
      in allE)
    apply(erule_tac
      x="va"
      in allE)
    apply(erule impE)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(simp add: derivation_append_def der2_def)
     apply(clarsimp)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(erule impE)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(simp add: derivation_append_def der2_def)
     apply(clarsimp)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(case_tac "length (\<pi>1!i) < length (\<pi>2!i)")
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(subgoal_tac "derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb (nb+(length(\<pi>1!i))+nc)= derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb (nb+(length(\<pi>1!i))+nc)")
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(thin_tac "derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb = derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb")
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(subgoal_tac "get_configuration (derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb (nb + length (\<pi>1 ! i) + nc)) \<noteq> get_configuration(derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb (nb + length (\<pi>1 ! i) + nc))")
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(thin_tac "derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb (nb + length (\<pi>1 ! i) + nc) = derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb (nb + length (\<pi>1 ! i) + nc)")
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(rule_tac
      t="get_configuration (derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb (nb + length (\<pi>1 ! i) + nc))"
      and s="Some \<lparr>cfg_conf=liftB va\<rparr>"
      in ssubst)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(simp add: derivation_append_def)
      apply(rule conjI)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(clarsimp)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc va d' da' ec ed)(*strict*)
       apply(case_tac "\<pi>1!i")
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc va d' da' ec ed)(*strict*)
        apply(clarsimp)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc va d' da' ec ed a list)(*strict*)
       apply(clarsimp)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc va d' da' ec ed z zs)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb ) ((nb + length (\<pi>1 ! i) + nc)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      prefer 2
      apply(rule_tac
      m="(nb + length (\<pi>2 ! i) + nc)"
      in cfgLM.step_detail_before_some_position)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(rule cfgLM.derivation_append_preserves_derivation)
          apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
          apply(simp add: cfgLM.derivation_initial_def)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(rule cfgLM.derivation_append_preserves_derivation)
           apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
           apply(simp add: cfgLM.trans_der_def)
          apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
          apply(simp add: cfgLM.trans_der_def)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(simp add: cfgLM.trans_der_def)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(clarsimp)
        apply(simp add: derivation_append_def)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(simp add: derivation_append_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(simp add: cfgLM.trans_der_def)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 c1 c2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 c1 c2 l r)(*strict*)
     apply(simp add: get_configuration_def)
     apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 c2 l r)(*strict*)
     apply(case_tac c2)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 c2 l r cfg_confa)(*strict*)
     apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 l r)(*strict*)
     apply (metis setA_liftB elemInsetA emptyE)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(case_tac "length (\<pi>1!i) > length (\<pi>2!i)")
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(subgoal_tac "derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb (nb+(length(\<pi>2!i))+nc)= derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb (nb+(length(\<pi>2!i))+nc)")
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(thin_tac "derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb = derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb")
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(subgoal_tac "get_configuration (derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb (nb + length (\<pi>2 ! i) + nc)) \<noteq> get_configuration(derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb (nb + length (\<pi>2 ! i) + nc))")
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(thin_tac "derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb (nb + length (\<pi>2 ! i) + nc) = derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb (nb + length (\<pi>2 ! i) + nc)")
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(rule_tac
      t="get_configuration (derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb (nb + length (\<pi>2 ! i) + nc))"
      and s="Some \<lparr>cfg_conf=liftB va\<rparr>"
      in ssubst)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(simp add: derivation_append_def)
      apply(rule conjI)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(clarsimp)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc va d' da' ec ed)(*strict*)
       apply(case_tac "\<pi>2!i")
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc va d' da' ec ed)(*strict*)
        apply(clarsimp)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc va d' da' ec ed a list)(*strict*)
       apply(clarsimp)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc va d' da' ec ed z zs)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb ) ((nb + length (\<pi>2 ! i) + nc)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      prefer 2
      apply(rule_tac
      m="(nb + length (\<pi>1 ! i) + nc)"
      in cfgLM.step_detail_before_some_position)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(rule cfgLM.derivation_append_preserves_derivation)
          apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
          apply(simp add: cfgLM.derivation_initial_def)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(rule cfgLM.derivation_append_preserves_derivation)
           apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
           apply(simp add: cfgLM.trans_der_def)
          apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
          apply(simp add: cfgLM.trans_der_def)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(simp add: cfgLM.trans_der_def)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(clarsimp)
        apply(simp add: derivation_append_def)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(simp add: derivation_append_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(simp add: cfgLM.trans_der_def)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 c1 c2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 c1 c2 l r)(*strict*)
     apply(simp add: get_configuration_def)
     apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 c2 l r)(*strict*)
     apply(case_tac c2)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 c2 l r cfg_confa)(*strict*)
     apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed e1 e2 l r)(*strict*)
     apply (metis setA_liftB elemInsetA emptyE)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(subgoal_tac "length (\<pi>1 ! i)=length (\<pi>2 ! i)")
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(map the (get_labels db nb))@(\<pi>1!i)@(map the (get_labels dc nc))=(map the (get_labels db nb))@(\<pi>2!i)@(map the (get_labels dc nc))")
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(force)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(rule_tac
      t="map the (get_labels db nb) @ \<pi>1 ! i @ map the (get_labels dc nc)"
      and s="map the(get_labels (derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb) (nb+(length (\<pi>1!i))+nc))"
      in ssubst)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     prefer 2
     apply(rule_tac
      t="map the (get_labels db nb) @ \<pi>2 ! i @ map the (get_labels dc nc)"
      and s="map the(get_labels (derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb) (nb+(length (\<pi>2!i))+nc))"
      in ssubst)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(rule_tac
      t="nb + length (\<pi>2 ! i) + nc"
      and s="nb + (length (\<pi>2 ! i) + nc)"
      in ssubst)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(rule_tac
      t="get_labels (derivation_append db (derivation_append da' dc (length (\<pi>2 ! i))) nb) (nb + (length (\<pi>2 ! i) + nc))"
      and s="get_labels SSd1 SSn1 @ get_labels SSd2 SSn2" for SSd1 SSn1 SSd2 SSn2
      in ssubst)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(rule cfgLM.get_labels_concat2)
          apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
          apply(force)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(simp add: cfgLM.derivation_initial_def)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(rule cfgLM.derivation_append_preserves_derivation)
          apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
          apply(simp add: cfgLM.trans_der_def)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(simp add: cfgLM.trans_der_def)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(simp add: cfgLM.trans_der_def)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(clarsimp)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(clarsimp)
      apply(simp add: derivation_append_def)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(rule_tac
      t="get_labels (derivation_append da' dc (length (\<pi>2 ! i))) (length (\<pi>2 ! i) + nc)"
      and s="get_labels SSd1 SSn1 @ get_labels SSd2 SSn2" for SSd1 SSn1 SSd2 SSn2
      in ssubst)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(rule cfgLM.get_labels_concat2)
          apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
          apply(force)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(force)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(force)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(force)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(clarsimp)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(rule_tac
      t="nb + length (\<pi>1 ! i) + nc"
      and s="nb + (length (\<pi>1 ! i) + nc)"
      in ssubst)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(force)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(rule_tac
      t="get_labels (derivation_append db (derivation_append d' dc (length (\<pi>1 ! i))) nb) (nb + (length (\<pi>1 ! i) + nc))"
      and s="get_labels SSd1 SSn1 @ get_labels SSd2 SSn2" for SSd1 SSn1 SSd2 SSn2
      in ssubst)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(rule cfgLM.get_labels_concat2)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(force)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(simp add: cfgLM.derivation_initial_def)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(rule cfgLM.derivation_append_preserves_derivation)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(simp add: cfgLM.trans_der_def)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(simp add: cfgLM.trans_der_def)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(simp add: cfgLM.trans_der_def)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(clarsimp)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(clarsimp)
     apply(simp add: derivation_append_def)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(rule_tac
      t="get_labels (derivation_append d' dc (length (\<pi>1 ! i))) (length (\<pi>1 ! i) + nc)"
      and s="get_labels SSd1 SSn1 @ get_labels SSd2 SSn2" for SSd1 SSn1 SSd2 SSn2
      in ssubst)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(rule cfgLM.get_labels_concat2)
         apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
         apply(force)
        apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
        apply(force)
       apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
       apply(force)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
     apply(force)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va d' da' ec ed)(*strict*)
    apply(clarsimp)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(thin_tac "\<exists>d'. cfgLM.trans_der G d' \<lparr>cfg_conf = liftB w1 @ teA (v ! i) # w2\<rparr> (map the (get_labels d n)) \<lparr>cfg_conf = liftB w1 @ w2\<rparr>")
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    prefer 2
    apply(rule_tac
      ?w1.0="[teA (v!i)]"
      and ?\<pi>1.0="map the (get_labels da na)"
      and ?w1'.0="[]"
      and ?d1.0="da"
      and G="G"
      and v="w1"
      and ?w2.0="w2"
      in cfgLM_trans_der_context_prime)
      apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
      apply(force)
     apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
     apply(force)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(rule_tac
      t="\<pi>2 ! i"
      and s="map the (get_labels da (length (\<pi>2 ! i)))"
      in ssubst)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
     apply(force)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(rule_tac
      t="length (map the (get_labels da (length (\<pi>2 ! i))))"
      and s="length ((get_labels da (length (\<pi>2 ! i))))"
      in ssubst)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
     apply(rule length_map)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(rule_tac
      t="length (get_labels da (length (\<pi>2 ! i)))"
      and s="length (\<pi>2 ! i)"
      in ssubst)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
     apply (metis get_labels_length)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(rule_tac
      t="get_labels da (length (\<pi>2 ! i))"
      and s="x" for x
      in ssubst)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
     apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
      apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
      apply(force)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
     apply(force)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(force)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(force)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="[teA (v!i)]"
      and ?\<pi>1.0="map the (get_labels d n)"
      and ?w1'.0="[]"
      and ?d1.0="d"
      and G="G"
      and v="w1"
      and ?w2.0="w2"
      in cfgLM_trans_der_context_prime)
     apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
     apply(force)
    apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(force)
   apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(rule_tac
      t="\<pi>1 ! i"
      and s="map the (get_labels d (length (\<pi>1 ! i)))"
      in ssubst)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(force)
   apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(rule_tac
      t="length (map the (get_labels d (length (\<pi>1 ! i))))"
      and s="length ((get_labels d (length (\<pi>1 ! i))))"
      in ssubst)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(rule length_map)
   apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(rule_tac
      t="length (get_labels d (length (\<pi>1 ! i)))"
      and s="length (\<pi>1 ! i)"
      in ssubst)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(rule_tac
      t="get_labels d (length (\<pi>1 ! i))"
      and s="x" for x
      in ssubst)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
     apply(force)
    apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
    apply(force)
   apply(rename_tac i d da ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
   apply(force)
  apply(rename_tac i d da n na ea eaa db nb w1 w2 e dc nc eb va)(*strict*)
  apply(force)
  done

lemma cfgLM_trans_der_construct_elimininating_derivation_prime: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> \<exists>d v \<pi>. cfgLM.trans_der G d \<lparr>cfg_conf=w\<rparr> \<pi> \<lparr>cfg_conf=liftB v\<rparr>"
  apply(subgoal_tac "\<exists>d n e v. cfgLM.derivation SSG d \<and> d 0 = Some (pair None \<lparr>cfg_conf = SSw\<rparr>) \<and> d n = Some (pair e \<lparr>cfg_conf = liftB v\<rparr>)" for SSG SSw)
   prefer 2
   apply(rule construct_elimininating_derivation_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d n e v)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule_tac
      x="v"
      in exI)
  apply(rule_tac
      x="map the (get_labels d n)"
      in exI)
  apply(simp add: cfgLM.trans_der_def)
  apply(rule conjI)
   apply(rename_tac d n e v)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac d n e v)(*strict*)
      apply(force)
     apply(rename_tac d n e v)(*strict*)
     apply(force)
    apply(rename_tac d n e v)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac d n e v)(*strict*)
   apply(force)
  apply(rename_tac d n e v)(*strict*)
  apply(rule_tac
      t="length (get_labels d n)"
      and s="n"
      in ssubst)
   apply(rename_tac d n e v)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac d n e v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d n e v)(*strict*)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac d n e v)(*strict*)
    apply(force)
   apply(rename_tac d n e v)(*strict*)
   apply(force)
  apply(rename_tac d n e v)(*strict*)
  apply(force)
  done

lemma trans_der_list_construct_elimininating_derivation: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> \<lparr>cfg_conf=w\<rparr> \<in> cfg_configurations G
  \<Longrightarrow> \<exists>ds \<pi>s fw.
  cfgLM.trans_der_list G
  ds (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) w) \<pi>s
  (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw)"
  apply(induct w)
   apply(clarsimp)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(simp add: cfgLM.trans_der_list_def)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac a w)(*strict*)
   apply(simp add: cfg_configurations_def)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w ds \<pi>s fw)(*strict*)
  apply(subgoal_tac "\<exists>d \<pi> v. cfgLM.trans_der SSG d \<lparr>cfg_conf = [a]\<rparr> \<pi> \<lparr>cfg_conf = liftB v\<rparr>" for SSG)
   apply(rename_tac a w ds \<pi>s fw)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in trans_der_construct_elimininating_derivation_prime)
     apply(rename_tac a w ds \<pi>s fw)(*strict*)
     apply(force)
    apply(rename_tac a w ds \<pi>s fw)(*strict*)
    apply(force)
   apply(rename_tac a w ds \<pi>s fw)(*strict*)
   apply(simp add: cfg_configurations_def)
  apply(rename_tac a w ds \<pi>s fw)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w ds \<pi>s fw d \<pi> v)(*strict*)
  apply(rule_tac
      x="d#ds"
      in exI)
  apply(rule_tac
      x="\<pi>#\<pi>s"
      in exI)
  apply(rule_tac
      x="v#fw"
      in exI)
  apply(simp add: cfgLM.trans_der_list_def)
  apply(clarsimp)
  apply(rename_tac a w ds \<pi>s fw d \<pi> v i)(*strict*)
  apply(case_tac i)
   apply(rename_tac a w ds \<pi>s fw d \<pi> v i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w ds \<pi>s fw d \<pi> v i nat)(*strict*)
  apply(clarsimp)
  done

lemma cfgSTD_Nonblockingness_nonterminals_equal_cfgLM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfg_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgLM_accessible_nonterminals G \<inter> cfgSTD_Nonblockingness_nonterminals G = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G = cfgLM_accessible_nonterminals G"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x \<in> cfg_nonterminals G")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgLM_accessible_nonterminals_def)
  done

lemma cfgLM_accessible_nonterminals_closed_under_steps: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_lhs p \<in> cfgLM_accessible_nonterminals G
  \<Longrightarrow> cfg_nonterminals G \<subseteq> cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> prod_rhs p = liftB v1 @ liftA (option_to_list v2) @ teA A # liftA v3
  \<Longrightarrow> A \<in> cfgLM_accessible_nonterminals G"
  apply(subgoal_tac "\<exists>d1 \<pi>1 \<alpha>1. cfgLM.trans_der G d1 \<lparr>cfg_conf=liftA (option_to_list v2)\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>")
   prefer 2
   apply(case_tac v2)
    apply(clarsimp)
    apply(simp add: option_to_list_def)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply(rule cfgLM_trans_der_der1)
     apply(force)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "a \<in> cfgSTD_Nonblockingness_nonterminals_ALT3 G")
    apply(rename_tac a)(*strict*)
    prefer 2
    apply(rule cfgSTD_Nonblockingness_nonterminals_cfgSTD_Nonblockingness_nonterminals_ALT3)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      A="setA (prod_rhs p)"
      in set_mp)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(rule_tac
      t="prod_rhs p"
      and s="liftB v1 @ teA a # teA A # liftA v3"
      in ssubst)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(simp add: setAConcat)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      B="cfg_nonterminals G"
      in subset_trans)
     apply(rename_tac a)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_ALT3_def)
  apply(subgoal_tac "\<exists>d2 \<pi>2 \<alpha>2 v. cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> \<pi>2 \<lparr>cfg_conf=liftB \<alpha>2@(teA (prod_lhs p))#v\<rparr>")
   prefer 2
   apply(subgoal_tac "prod_lhs p \<in> cfgLM_accessible_nonterminals_ALT2 G")
    prefer 2
    apply(rule cfgLM_accessible_nonterminals_cfgLM_accessible_nonterminals_ALT2)
     apply(force)
    apply(force)
   apply(simp add: cfgLM_accessible_nonterminals_ALT2_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = liftB \<alpha>2 @ teA (prod_lhs p) # v\<rparr> \<in> cfg_configurations G")
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v e ea)(*strict*)
   apply(rule_tac
      d="d2"
      in cfgLM.belongs_configurations)
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v e ea)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v e ea)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der SSG (der2 \<lparr>cfg_conf = liftB \<alpha>2 @ teA (prod_lhs p) # v\<rparr> p \<lparr>cfg_conf = liftB \<alpha>2 @ (prod_rhs p) @ v\<rparr>) SSc [SSe] SSc'" for SSG SSc SSe SSc')
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
   prefer 2
   apply(rule_tac cfgLM.trans_der_der2)
     apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(rule_tac
      x="liftB \<alpha>2"
      in exI)
   apply(clarsimp)
   apply(simp add: setA_liftB)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
  apply(rule cfgLM_accessible_nonterminals_ALT2_cfgLM_accessible_nonterminals)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
  apply(simp add: cfgLM_accessible_nonterminals_ALT2_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and ?v1.0="[]"
      and ?v4.0="[]"
      and ?d1.0="d2"
      and ?d2.0="der2 \<lparr>cfg_conf = liftB \<alpha>2 @ teA (prod_lhs p) # v\<rparr> p \<lparr>cfg_conf = liftB \<alpha>2 @ liftB v1 @ liftA (option_to_list v2) @ teA A # liftA v3 @ v\<rparr>"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v d)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and ?v1.0="\<alpha>2@v1"
      and ?v4.0="teA A # liftA v3 @ v"
      and ?d1.0="d"
      and ?d2.0="d1"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v d)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v d)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v d)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v d)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2 v d da)(*strict*)
  apply(rule_tac
      x="da"
      in exI)
  apply(rule_tac
      x="\<pi>2@p#\<pi>1"
      in exI)
  apply(rule_tac
      x="\<alpha>2@v1@\<alpha>1"
      in exI)
  apply(rule_tac
      x="liftA v3@v"
      in exI)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma reachable_and_eliminiable_implies_eliminable: "
  cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G' = cfgSTD_Nonblockingness_nonterminals G'"
  apply(rule order_antisym)
   apply(clarsimp)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  done

lemma reachable_and_eliminiable_implies_reachable: "
  cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> cfg_nonterminals G' = cfgLM_accessible_nonterminals G'"
  apply(rule order_antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgLM_accessible_nonterminals_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(force)
  done

lemma reachable_and_eliminiable_implies_eliminable2: "
  cfg_nonterminals G' = cfgLM_accessible_nonterminals G' \<inter> cfgSTD_Nonblockingness_nonterminals G'
  \<Longrightarrow> cfg_nonterminals G' = cfgSTD_Nonblockingness_nonterminals G'"
  apply(rule order_antisym)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgLM_accessible_nonterminals_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d w')(*strict*)
  apply(force)
  done

end
