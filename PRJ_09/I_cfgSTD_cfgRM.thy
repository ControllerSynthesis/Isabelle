section {*I\_cfgSTD\_cfgRM*}
theory
  I_cfgSTD_cfgRM

imports
  I_cfgSTD
  I_cfgRM

begin

lemma CFG_CFGRM_StepRelation: "
  cfgRM_step_relation M ca ea c
  \<Longrightarrow> cfgSTD_step_relation M ca ea c"
  apply(simp add: cfgSTD_step_relation_def cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(force)
  done

definition FOLLOW :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event)DT_two_elements list
  \<Rightarrow> 'event list set"
  where
    "FOLLOW G k \<gamma> \<equiv>
  {y. \<exists>d n \<alpha> \<beta> e1.
	 cfgRM.derivation G d
	 \<and> maximum_of_domain d n
	 \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>)
	 \<and> d n = Some (pair e1 \<lparr>cfg_conf = \<alpha> @ \<gamma> @ \<beta>\<rparr>)
	 \<and> y \<in> cfgSTD_first G k \<beta>}"

lemma cfgRM_derivations_are_cfg_derivations: "
  cfgRM.derivation G d
  \<Longrightarrow> cfgSTD.derivation G d"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule cfgRM.some_position_has_details_at_0)
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
   apply(rule cfgRM.derivation_Always_PreEdge)
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
      in cfgRM.pre_some_position_is_some_position)
     apply(rename_tac c nat b y)(*strict*)
     apply(blast)
    apply(rename_tac c nat b y)(*strict*)
    apply(blast)
   apply(rename_tac c nat b y)(*strict*)
   apply(force)
  apply(rename_tac c nat b y)(*strict*)
  apply(clarsimp)
  apply(rename_tac c nat b y e ca)(*strict*)
  apply(subgoal_tac "cfgRM_step_relation G ca y b")
   apply(rename_tac c nat b y e ca)(*strict*)
   prefer 2
   apply(rule cfgRM.position_change_due_to_step_relation)
     apply(rename_tac c nat b y e ca)(*strict*)
     apply(blast)+
  apply(rename_tac c nat b y e ca)(*strict*)
  apply(simp add: cfgSTD_step_relation_def cfgRM_step_relation_def)
  apply(auto)
  done

lemma cfg_derivation_can_be_translated_to_cfgRM_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w2\<rparr>)
  \<Longrightarrow> setA w2={}
  \<Longrightarrow> \<exists>d' e.
  cfgRM.derivation G d'
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
    apply(rule cfgRM.der1_is_derivation)
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
  apply(subgoal_tac "(\<exists>d1'. cfgRM.derivation G d1' \<and> maximum_of_domain d1' n1 \<and> d1' 0 = Some (pair None \<lparr>cfg_conf = l\<rparr>) \<and> (\<exists>e1'. d1' n1 = Some (pair e1' \<lparr>cfg_conf = w1\<rparr>)))")
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
  apply(subgoal_tac "(\<exists>d2'. cfgRM.derivation G d2' \<and> maximum_of_domain d2' n2 \<and> d2' 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>) \<and> (\<exists>e2'. d2' n2 = Some (pair e2' \<lparr>cfg_conf = w2\<rparr>)))")
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
  apply(subgoal_tac "(\<exists>d3'. cfgRM.derivation G d3' \<and> maximum_of_domain d3' n3 \<and> d3' 0 = Some (pair None \<lparr>cfg_conf = r\<rparr>) \<and> (\<exists>e3'. d3' n3 = Some (pair e3' \<lparr>cfg_conf = w3\<rparr>)))")
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
  apply(subgoal_tac "(\<exists>d2''. cfgRM.derivation G d2'' \<and> maximum_of_domain d2'' (Suc n2) \<and> d2'' 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>) \<and> (\<exists>e2''. d2'' (Suc n2) = Some (pair e2'' \<lparr>cfg_conf = w2\<rparr>)))")
   apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
   prefer 2
   apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr> ) d2' (Suc 0)"
      in exI)
   apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
   apply(rule conjI)
    apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
    apply(rule cfgRM.derivation_concat2)
       apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d2' d3' e1' e2' e3')(*strict*)
       apply(rule cfgRM.der2_is_derivation)
       apply(simp add: cfgRM_step_relation_def)
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
  apply(thin_tac "cfgRM.derivation G d2'")
  apply(thin_tac "d2' n2 = Some (pair e2' \<lparr>cfg_conf = w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(subgoal_tac "(\<exists>d23. cfgRM.derivation G d23 \<and> maximum_of_domain d23 (Suc n2+n3) \<and> d23 0 = Some (pair None \<lparr>cfg_conf = [teA A]@r\<rparr>) \<and> (\<exists>e23. d23 (Suc n2+n3) = Some (pair e23 \<lparr>cfg_conf = w2@w3\<rparr>)))")
   apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
   prefer 2
   apply(rule_tac
      x="(derivation_append (derivation_map d3' (\<lambda>v. \<lparr>cfg_conf = [teA A] @ (cfg_conf v)\<rparr>)) (derivation_map d2'' (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w3\<rparr>)) n3)"
      in exI)
   apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
   apply(rule conjI)
    apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
    apply(rule cfgRM.from_to_is_der)
    apply(rule_tac
      w1'="w2"
      and ?w2.0="r"
      and w2'="w3"
      in cfgRM_concatExtendIsFromToBoth)
         apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
         apply(force)
        apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
        apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_to_def cfgRM.derivation_from_def)
        apply(rule_tac
      x="Suc n2"
      in exI)
        apply(simp add: maximum_of_domain_def)
       apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
       apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_to_def cfgRM.derivation_from_def)
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
    apply(rule_tac
      t="Suc n2+n3"
      and s="n3+Suc n2"
      in ssubst)
     apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
     apply(force)
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
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' d3' e1' e3' d2'' e2'')(*strict*)
  apply(thin_tac "cfgRM.derivation G d3'")
  apply(thin_tac "maximum_of_domain d3' n3")
  apply(thin_tac "d3' 0 = Some (pair None \<lparr>cfg_conf = r\<rparr>)")
  apply(thin_tac "d3' n3 = Some (pair e3' \<lparr>cfg_conf = w3\<rparr>)")
  apply(thin_tac "cfgRM.derivation G d2''")
  apply(thin_tac "maximum_of_domain d2'' (Suc n2)")
  apply(thin_tac "d2'' 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
  apply(thin_tac "d2'' (Suc n2) = Some (pair e2'' \<lparr>cfg_conf = w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule_tac
      x="(derivation_append (derivation_map d23 (\<lambda>v. \<lparr>cfg_conf = l @ (cfg_conf v)\<rparr>)) (derivation_map d1' (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w2 @ w3\<rparr>)) (Suc(n2+n3)))"
      in exI)
  apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
  apply(rule conjI)
   apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
   apply(rule cfgRM.from_to_is_der)
   apply(rule_tac
      w1'="w1"
      and ?w2.0="[teA A]@r"
      in cfgRM_concatExtendIsFromToBoth)
        apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
        apply(force)
       apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
       apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_to_def cfgRM.derivation_from_def)
       apply(rule_tac
      x="n1"
      in exI)
       apply(simp add: maximum_of_domain_def)
      apply(rename_tac l r A w w1 n1 w2 w3 n2 n3 d1' e1' d23 e23)(*strict*)
      apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_to_def cfgRM.derivation_from_def)
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
      and s="Suc(n2+n3)+n1"
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
  apply(clarsimp)
  done

lemma CFG_lang_rm_lang_equal1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G \<supseteq> cfgRM.marked_language G"
  apply(simp add: cfgSTD.marked_language_def cfgRM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: cfgRM.derivation_initial_def cfgSTD.derivation_initial_def)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(clarsimp)
  apply(rule cfgRM_derivations_are_cfg_derivations)
  apply(force)
  done

lemma CFG_lang_rm_lang_equal2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G \<subseteq> cfgRM.marked_language G"
  apply(simp add: cfgSTD.marked_language_def cfgRM.marked_language_def)
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
  apply(subgoal_tac "\<exists>d' e. cfgRM.derivation SSG d' \<and> maximum_of_domain d' SSn \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSw1\<rparr>) \<and> d' SSn = Some (pair e \<lparr>cfg_conf = SSw2\<rparr>)" for SSG SSw1 SSn SSw2)
   apply(rename_tac x d n w1 e)(*strict*)
   prefer 2
   apply(rule cfg_derivation_can_be_translated_to_cfgRM_derivation)
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
  apply(simp add: cfgRM.derivation_initial_def)
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

lemma CFG_lang_rm_lang_equal: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.marked_language G = cfgRM.marked_language G"
  apply(rule order_antisym)
   apply(rule CFG_lang_rm_lang_equal2)
   apply(force)
  apply(rule CFG_lang_rm_lang_equal1)
  apply(force)
  done

lemma CFGRM_to_CFG_derivation_initial: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation_initial G d
  \<Longrightarrow> cfgSTD.derivation_initial G d"
  apply(simp add: cfgRM.derivation_initial_def cfgSTD.derivation_initial_def)
  apply(clarsimp)
  apply(rule cfgRM_derivations_are_cfg_derivations)
  apply(force)
  done

corollary cfgSTD_unmarked_in_cfgRM_unmarked: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD.unmarked_language G \<subseteq> cfgRM.unmarked_language G"
  apply(simp add: cfgSTD.unmarked_language_def cfgRM.unmarked_language_def)
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
      in cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
        apply(force)
       apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
       apply (metis (full_types, hide_lams) cfgSTD.derivation_append_preserves_derivation_initial_prime cfgSTD.derivation_initial_def cfgSTD.derivation_take_preserves_derivation_initial maximum_of_domain_derivation_take option.distinct(1))
      apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
      apply (metis concat_has_max_dom maximum_of_domain_derivation_take option.distinct(1))
     apply(rename_tac x d e i z dc xa ia ea c eb ca)(*strict*)
     apply(simp add: derivation_append_def derivation_take_def)
     apply(simp add: cfgSTD.derivation_initial_def cfgRM.derivation_initial_def cfg_marking_configuration_def cfg_initial_configurations_def)
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
  apply(simp add: cfgRM.derivation_initial_def)
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

lemma cfgSTD_first_suffix_is_shorter: "
  valid_cfg G
  \<Longrightarrow> y \<in> cfgSTD_first G k (w1@(liftB w2))
  \<Longrightarrow> length y < k
  \<Longrightarrow> suffix y w2"
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac x d e1 n)(*strict*)
  apply(subgoal_tac "suffix (liftB x) (liftB w2)")
   apply(rename_tac x d e1 n)(*strict*)
   apply(rule liftB_creates_suffix)
   apply(force)
  apply(rename_tac x d e1 n)(*strict*)
  apply(subgoal_tac "\<exists>d' e. cfgRM.derivation G d' \<and> maximum_of_domain d' n \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w1@liftB w2\<rparr>) \<and> d' n = Some (pair e \<lparr>cfg_conf=liftB x\<rparr>)")
   apply(rename_tac x d e1 n)(*strict*)
   prefer 2
   apply(rule cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(rename_tac x d e1 n)(*strict*)
        apply(force)
       apply(rename_tac x d e1 n)(*strict*)
       apply(simp add: maximum_of_domain_def)
      apply(rename_tac x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac x d e1 n)(*strict*)
     apply(force)
    apply(rename_tac x d e1 n)(*strict*)
    apply(force)
   apply(rename_tac x d e1 n)(*strict*)
   apply (metis setA_liftB)
  apply(rename_tac x d e1 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e1 n d' e)(*strict*)
  apply(rule_tac
      d="d'"
      in CFGRM_terminals_stay_at_end)
       apply(rename_tac x d e1 n d' e)(*strict*)
       apply(force)
      apply(rename_tac x d e1 n d' e)(*strict*)
      apply(force)
     apply(rename_tac x d e1 n d' e)(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac x d e1 n d' e)(*strict*)
    apply(force)
   apply(rename_tac x d e1 n d' e)(*strict*)
   apply(force)
  apply(rename_tac x d e1 n d' e)(*strict*)
  apply(force)
  done

corollary CFGRM_CFG_translate_Nonblockingness_id: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G"
  apply(simp add: cfgRM.Nonblockingness_branching_def cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule impE)
   apply(rename_tac dh n)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rename_tac dh n dc n')(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac dh n dc n' i e c)(*strict*)
  apply(case_tac "i<n")
   apply(rename_tac dh n dc n' i e c)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac dh n dc n' i e c)(*strict*)
    apply(force)
   apply(rename_tac dh n dc n' i e c)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh i = Some (pair e1 c1) \<and> dh (Suc i) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
    apply(rename_tac dh n dc n' i e c)(*strict*)
    prefer 2
    apply(rule_tac
      m="n"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac dh n dc n' i e c)(*strict*)
      apply(rule cfgRM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac dh n dc n' i e c)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac dh n dc n' i e c)(*strict*)
    apply(force)
   apply(rename_tac dh n dc n' i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc n' i e c e1 e2 c1 c2)(*strict*)
   apply(simp add: cfg_marking_configuration_def cfgRM_step_relation_def derivation_append_def)
   apply(clarsimp)
   apply(rename_tac dh n dc n' i e c e2 c2 l r)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(force)
  apply(rename_tac dh n dc n' i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
   apply(rename_tac dh n dc n' i e c)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac dh n dc n' i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc n' i e c ca)(*strict*)
  apply(case_tac ca)
  apply(rename_tac dh n dc n' i e c ca cfg_conf)(*strict*)
  apply(rename_tac w1)
  apply(rename_tac dh n dc n' i e c ca w1)(*strict*)
  apply(subgoal_tac "dc (i-n) = (if i=n then Some(pair None c) else Some(pair e c))")
   apply(rename_tac dh n dc n' i e c ca w1)(*strict*)
   prefer 2
   apply(simp add: derivation_append_def derivation_append_fit_def)
   apply(clarsimp)
   apply(rename_tac dh n dc n' i e c w1)(*strict*)
   apply(force)
  apply(rename_tac dh n dc n' i e c ca w1)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n dc n' i e c ca w1 cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc n' i e w1 cfg_conf)(*strict*)
  apply(rename_tac w2)
  apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
  apply(subgoal_tac "maximum_of_domain dc (i - n)")
   apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      e="if i=n then None else e"
      and c="\<lparr>cfg_conf=w2\<rparr>"
      in cfgSTD.dead_end_at_some_is_max_dom2)
     apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc n' i e w1 w2 ea c')(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac dh n dc n' i e w1 ea c' l r)(*strict*)
   apply(simp add: cfg_marking_configuration_def)
   apply(clarsimp)
   apply(simp only: setAConcat concat_asso)
   apply(force)
  apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>d' e. cfgRM.derivation G d' \<and> maximum_of_domain d' (i-n) \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>) \<and> d' (i-n) = Some (pair e \<lparr>cfg_conf=w2\<rparr>)")
   apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      e="if i=n then None else e"
      in cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
      apply(force)
     apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
   apply(simp add: cfg_marking_configuration_def)
  apply(rename_tac dh n dc n' i e w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
      apply(force)
     apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
     apply(force)
    apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
    apply(rule_tac
      d="dc"
      in cfgSTD.belongs_configurations)
     apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
     apply(force)
    apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
    apply(force)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(case_tac "dh n")
    apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea option)(*strict*)
   apply(force)
  apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
   apply(case_tac "dh n")
    apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea a)(*strict*)
   apply(case_tac a)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc n' i e w1 w2 d' ea option b)(*strict*)
   apply(simp add: derivation_append_fit_def)
  apply(rename_tac dh n dc n' i e w1 w2 d' ea)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="if i=n then e else ea"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf=w2\<rparr>"
      in exI)
  apply(clarsimp)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  done

corollary cfgSTD_Nonblockingness_branching_to_cfgRM_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G"
  apply(rule CFGRM_CFG_translate_Nonblockingness_id)
   apply(force)
  apply(force)
  done

lemma cfgSTD_accessible_nonterminals_ALT_contained_in_cfgRM_accessible_nonterminals_hlp: "
  valid_cfg G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> ATS.derivation_initial cfg_initial_configurations
  cfgSTD_step_relation G d
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # w2\<rparr>)
  \<Longrightarrow> \<exists>d. ATS.derivation_initial cfg_initial_configurations
  cfgRM_step_relation G d \<and>
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
    apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def der1_def)
    apply(fold der1_def)
    apply(rule cfgRM.der1_is_derivation)
   apply(rule_tac
      x="0"
      in exI)
   apply(simp add: cfgRM.derivation_initial_def cfg_initial_configurations_def der1_def get_configuration_def)
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
    apply(rule cfgRM_Nonblockingness_branching_implies_FB_iterated_elimination)
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
   apply(thin_tac "cfgRM.derivation_initial G d")
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
      x="derivation_append d (der2 \<lparr>cfg_conf = w1a @ teA A # liftB w2a\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w1a @ w @ liftB w2a\<rparr>) n"
      in exI)
   apply(rule conjI)
    apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation_initial)
      apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
      apply(force)
     apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
     apply(force)
    apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation)
      apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
      apply(simp add: cfgRM.derivation_initial_def)
     apply(rename_tac w1 x w2 l r A w d n w1a w2a e)(*strict*)
     apply(rule cfgRM.der2_is_derivation)
     apply(simp add: cfgRM_step_relation_def)
     apply(rule_tac
      x="w1a"
      in exI)
     apply(rule_tac
      x="liftB w2a"
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
      x="\<lparr>cfg_conf = w1a @ w @ liftB w2a\<rparr>"
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
      x="w1a @ w1b"
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

lemma cfgSTD_accessible_nonterminals_ALT_contained_in_cfgRM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD_accessible_nonterminals_ALT G \<subseteq> cfgRM_accessible_nonterminals G"
  apply(simp add: cfgSTD_accessible_nonterminals_ALT_def cfgRM_accessible_nonterminals_def)
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
   apply(rule cfgSTD_accessible_nonterminals_ALT_contained_in_cfgRM_accessible_nonterminals_hlp)
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
   apply(rule cfgRM_Nonblockingness_branching_implies_FB_iterated_elimination)
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
      x="\<lparr>cfg_conf = w1b @ teA x # liftB w2b\<rparr>"
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
  apply(force)
  done

lemma Sentential_rm_is_normal: "
  valid_cfg G
  \<Longrightarrow> SententialRM G w
  \<Longrightarrow> Sentential G w"
  apply(simp add: Sentential_def SententialRM_def)
  apply(clarsimp)
  apply(rename_tac d e n v)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d e n v)(*strict*)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac d e n v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d e n v)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def cfgRM.derivation_initial_def)
   apply(rule cfgRM_derivations_are_cfg_derivations)
   apply(force)
  apply(rename_tac d e n v)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule_tac
      x="v"
      in exI)
  apply(clarsimp)
  done

lemma cfg_derivation_can_be_translated_to_cfgRM_derivation_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> cfgSTD.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w2\<rparr>)
  \<Longrightarrow> setA w2={}
  \<Longrightarrow> \<exists>d' e.
  cfgRM.derivation G d'
  \<and> cfgRM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>)
  \<and> d' n = Some (pair e \<lparr>cfg_conf=w2\<rparr>)"
  apply(subgoal_tac "\<exists>d' e. cfgRM.derivation SSG d' \<and> maximum_of_domain d' SSn \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSw1\<rparr>) \<and> d' SSn = Some (pair e \<lparr>cfg_conf = SSw2\<rparr>)" for SSG SSw1 SSn SSw2)
   prefer 2
   apply(rule_tac
      d="derivation_take d n"
      in cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(force)
       apply(rule cfgSTD.derivation_take_preserves_derivation)
       apply(force)
      apply(rule maximum_of_domain_derivation_take)
      apply(force)
     apply(simp add: derivation_take_def)
    apply(simp add: derivation_take_def)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d' ea)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule cfgRM.derivation_belongs)
     apply(rename_tac d' ea)(*strict*)
     apply(force)
    apply(rename_tac d' ea)(*strict*)
    apply(force)
   apply(rename_tac d' ea)(*strict*)
   apply(rule cfgRM.belongs_configurations)
    apply(rename_tac d' ea)(*strict*)
    apply(force)
   apply(rename_tac d' ea)(*strict*)
   apply(force)
  apply(rename_tac d' ea)(*strict*)
  apply(force)
  done

end
