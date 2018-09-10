section {*I\_cfgSTD*}
theory
  I_cfgSTD

imports
  I_cfg_base

begin

definition cfgSTD_step_relation :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "cfgSTD_step_relation G c1 e c2 \<equiv>
  e \<in> cfg_productions G
  \<and> (\<exists>l r.
      cfg_conf c1 = l @ teA (prod_lhs e) # r
      \<and> cfg_conf c2 = l @ prod_rhs e @ r)"

lemma cfgSTD_inst_AX_step_relation_preserves_belongs: "
  (\<forall>M. valid_cfg M \<longrightarrow> (\<forall>c1 e c2. cfgSTD_step_relation M c1 e c2 \<longrightarrow> c1 \<in> cfg_configurations M \<longrightarrow> e \<in> cfg_step_labels M \<and> c2 \<in> cfg_configurations M))"
  apply(rule allI)
  apply(rename_tac M)(*strict*)
  apply(rule impI)+
  apply(rule allI)+
  apply(rename_tac M c1 e c2)(*strict*)
  apply(rule impI)+
  apply(simp add: cfg_configurations_def cfgSTD_step_relation_def cfg_step_labels_def)
  apply(case_tac c2)
  apply(rename_tac M c1 e c2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e l r)(*strict*)
  apply(simp only: setAConcat concat_asso setBConcat)
  apply(clarsimp)
  apply(simp add: valid_cfg_def)
  done

lemma cfgSTD_step_relation_both_sides_context: "
  \<forall>a e b. cfgSTD_step_relation G a e b \<longrightarrow> cfgSTD_step_relation G \<lparr>cfg_conf = left @ cfg_conf a @ right\<rparr> e \<lparr>cfg_conf = left @ cfg_conf b @ right\<rparr>"
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac a e b l r)(*strict*)
  apply(rule_tac
      x="left@l"
      in exI)
  apply(rule_tac
      x="r@right"
      in exI)
  apply(clarsimp)
  done

lemma cfgSTD_no_step_without_nonterms: "
  setA (cfg_conf ca) = {}
  \<Longrightarrow> \<forall>e c'. \<not> cfgSTD_step_relation G' ca e c'"
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e c' l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma inProdsFromcfgSTD_step_relation: "
  cfgSTD_step_relation G c1 e c2
  \<Longrightarrow> e \<in> cfg_productions G"
  apply(simp add: cfgSTD_step_relation_def)
  done

lemma staysInSigma: "
  valid_cfg G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD_step_relation G \<lparr>cfg_conf=w\<rparr> e \<lparr>cfg_conf=w'\<rparr>
  \<Longrightarrow> e \<in> cfg_productions G
  \<Longrightarrow> setB w' \<subseteq> cfg_events G"
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac x l r)(*strict*)
  apply(case_tac e)
  apply(rename_tac x l r prod_lhsa prod_rhsa)(*strict*)
  apply(auto)
  apply(rename_tac x l r prod_lhs prod_rhs)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(rename_tac x l r prod_lhsa prod_rhsa)(*strict*)
  apply(auto)
  apply(erule_tac
      x="\<lparr>prod_lhs = prod_lhsa, prod_rhs = prod_rhsa\<rparr>"
      in ballE)
   apply(rename_tac x l r prod_lhsa prod_rhsa)(*strict*)
   apply(auto)
  apply(rename_tac x l r prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac x l r A w)(*strict*)
  apply(rule_tac
      A="setB (l @ w @ r)"
      in set_mp)
   apply(rename_tac x l r A w)(*strict*)
   apply(rule_tac
      s="setB l \<union> setB w \<union> setB r"
      and t="setB (l @ w @ r)"
      in ssubst)
    apply(rename_tac x l r A w)(*strict*)
    apply(simp (no_asm) only: setBConcat concat_asso)
   apply(rename_tac x l r A w)(*strict*)
   apply(clarsimp)
   defer
   apply(clarsimp)
  apply(rename_tac x l r A w)(*strict*)
  apply(rule conjI)
   apply(rename_tac x l r A w)(*strict*)
   apply(simp only: setBConcat concat_asso)
   apply(rule_tac
      B="setB l \<union> setB (teA A # r)"
      in subset_trans)
    apply(rename_tac x l r A w)(*strict*)
    apply(blast)
   apply(rename_tac x l r A w)(*strict*)
   apply(blast)
  apply(rename_tac x l r A w)(*strict*)
  apply(subgoal_tac "setB (l @ [teA A] @ r) \<subseteq> cfg_events G")
   apply(rename_tac x l r A w)(*strict*)
   apply(simp only: setBConcat concat_asso)
   apply(rule_tac
      B="setB l \<union> setB [teA A] \<union> setB r"
      in subset_trans)
    apply(rename_tac x l r A w)(*strict*)
    apply(blast)
   apply(rename_tac x l r A w)(*strict*)
   apply(blast)
  apply(rename_tac x l r A w)(*strict*)
  apply(auto)
  done

lemma CFGStepNonTermBehaviour: "
  cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> \<lparr>prod_lhs=A, prod_rhs=w\<rparr> \<lparr>cfg_conf = w2\<rparr>
  \<Longrightarrow> setA w2 \<subseteq> setA w1 \<union> setA w"
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp del: subsetI)
  apply(rename_tac l r)(*strict*)
  apply(rule_tac
      t="teA A#r"
      and s="[teA A]@r"
      in ssubst)
   apply(rename_tac l r)(*strict*)
   apply(force)
  apply(rename_tac l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma cfgSTD_step_relation_closed_under_post_context: "
  valid_cfg M
  \<Longrightarrow> C = (\<lambda>w. \<lparr>cfg_conf = cfg_conf w @ x\<rparr>)
  \<Longrightarrow> \<forall>a e b. cfgSTD_step_relation M a e b \<longrightarrow> cfgSTD_step_relation M (C a) e (C b)"
  apply(auto)
  apply(rename_tac a e b)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac a e b l r)(*strict*)
  apply(rule_tac
      x = "l"
      in exI)
  apply(rule_tac
      x = "r @ x"
      in exI)
  apply(auto)
  done

lemma cfgSTD_step_relation_closed_under_post_context2: "
  valid_cfg M
  \<Longrightarrow> C = (\<lambda>w. \<lparr>cfg_conf = x @ cfg_conf w\<rparr>)
  \<Longrightarrow> \<forall>a e b. cfgSTD_step_relation M a e b \<longrightarrow> cfgSTD_step_relation M (C a) e (C b)"
  apply(auto)
  apply(rename_tac a e b)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac a e b l r)(*strict*)
  apply(rule_tac
      x = "x @ l"
      in exI)
  apply(rule_tac
      x = "r"
      in exI)
  apply(auto)
  done

lemma terminalPreserved: "
  cfgSTD_step_relation G \<lparr>cfg_conf = w1a @ teB b # w2a\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w'\<rparr>
  \<Longrightarrow> \<exists>w1 w2. w' = w1 @ teB b # w2"
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac l r)(*strict*)
  apply(subgoal_tac "w1a \<sqsubseteq> (l @ [teA A]) \<or> (l @ [teA A]) \<sqsubseteq> w1a")
   apply(rename_tac l r)(*strict*)
   prefer 2
   apply(rule_tac
      b = "teB b#w2a"
      and d = "r"
      in mutual_prefix_prefix)
   apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(erule disjE)
   apply(rename_tac l r)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac l r c)(*strict*)
   apply(subgoal_tac "w1a @ teB b # w2a = w1a @ c @ r")
    apply(rename_tac l r c)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac l r c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "w1a \<sqsubseteq> l \<or> l \<sqsubseteq> w1a")
    apply(rename_tac l r c)(*strict*)
    prefer 2
    apply(rule_tac
      b = "c"
      and d = "[teA A]"
      in mutual_prefix_prefix)
    apply(clarsimp)
   apply(rename_tac l r c)(*strict*)
   apply(erule disjE)
    apply(rename_tac l r c)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac r ca)(*strict*)
    apply(case_tac ca)
     apply(rename_tac r ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac r ca a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac r list)(*strict*)
    apply(rule_tac
      x = "w1a"
      in exI)
    apply(rule_tac
      x = "list @ w @ r"
      in exI)
    apply(clarsimp)
   apply(rename_tac l r c)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac l r c ca)(*strict*)
   apply(case_tac c)
    apply(rename_tac l r c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac l)(*strict*)
    apply(rule_tac
      x = "l @ w"
      in exI)
    apply(rule_tac
      x = "w2a"
      in exI)
    apply(clarsimp)
   apply(rename_tac l r c ca a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac l r ca list)(*strict*)
   apply(case_tac ca)
    apply(rename_tac l r ca list)(*strict*)
    apply(clarsimp)
   apply(rename_tac l r ca list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac l c)(*strict*)
  apply(rule_tac
      x = "l @ w @ c"
      in exI)
  apply(rule_tac
      x = "w2a"
      in exI)
  apply(clarsimp)
  done

lemma alt_case: "
  cfgSTD_step_relation G \<lparr>cfg_conf = w1 @ w2\<rparr> e \<lparr>cfg_conf = c\<rparr>
  \<Longrightarrow> \<not> (\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = c)
  \<Longrightarrow> \<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = c"
  apply(clarsimp)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(case_tac e)
  apply(rename_tac l r prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac l r A w)(*strict*)
  apply(thin_tac "\<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<in> cfg_productions G")
  apply(subgoal_tac "prefix w1 l \<or> prefix l w1")
   apply(rename_tac l r A w)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(blast)
  apply(rename_tac l r A w)(*strict*)
  apply(simp add: prefix_def)
  apply(auto)
   apply(rename_tac r A w c)(*strict*)
   apply(rule_tac
      x = "c"
      in exI)
   apply(rule_tac
      x = "r"
      in exI)
   apply(auto)
  apply(rename_tac l r A w c)(*strict*)
  apply(case_tac c)
   apply(rename_tac l r A w c)(*strict*)
   apply(auto)
  apply(rename_tac l A w list)(*strict*)
  apply(erule_tac
      x = "l @ w @ list"
      in allE)
  apply(auto)
  done

lemma supCFGhasAllStepsOfsub: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgSTD_step_relation G1 c1 e c2
  \<Longrightarrow> cfgSTD_step_relation G2 c1 e c2"
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac l r)(*strict*)
  apply(simp add: cfg_sub_def)
  apply(auto)
  done

interpretation "cfgSTD" : loc_cfg_0
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgSTD_step_relation"
  (* effects *)
  "cfg_effects"
  (* marking_condition *)
  "cfg_marking_condition"
  (* marked_effect *)
  "cfg_marked_effect"
  (* unmarked_effect *)
  "cfg_unmarked_effect"
  (* destinations *)
  "cfg_destination"
  (* get_destinations *)
  "cfg_get_destinations"
  apply(simp add: LOCALE_DEFS_ALL LOCALE_DEFS_cfg)
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgSTD_inst_AX_step_relation_preserves_belongs )
  done

definition cfgSTD_Nonblockingness_nonterminals :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgSTD_Nonblockingness_nonterminals G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d w'.
      cfgSTD.derivation_from_to G d
          {pair None \<lparr>cfg_conf = [teA A]\<rparr>}
          {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>}
    \<and> setA w' = {}}"

definition cfgSTD_Nonblockingness_nonterminals_ALT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgSTD_Nonblockingness_nonterminals_ALT G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n e w'.
      cfgSTD.derivation G d
      \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)
      \<and> d n = Some (pair e \<lparr>cfg_conf = w'\<rparr>)
      \<and> setA w' = {}}"

lemma cfgSTD_Nonblockingness_nonterminals_ALT_vs_cfgSTD_Nonblockingness_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals_ALT G = cfgSTD_Nonblockingness_nonterminals G"
  apply(rule antisym)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_ALT_def cfgSTD_Nonblockingness_nonterminals_def)
   apply(clarsimp)
   apply(rename_tac x d n e w')(*strict*)
   apply(rule_tac
      x="derivation_take d n"
      in exI)
   apply(rule_tac
      x="w'"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
   apply(rule context_conjI)
    apply(rename_tac x d n e w')(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac x d n e w')(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x d n e w')(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac x d n e w')(*strict*)
   apply(simp add: derivation_take_def)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_ALT_def cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d w')(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
  apply(clarsimp)
  apply(rename_tac x d w' n xa)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d w' n xa)(*strict*)
   apply(force)
  apply(rename_tac x d w' n xa)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d w' n xa)(*strict*)
   apply(case_tac "d 0")
    apply(rename_tac x d w' n xa)(*strict*)
    apply(force)
   apply(rename_tac x d w' n xa a)(*strict*)
   apply(force)
  apply(rename_tac x d w' n xa)(*strict*)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule_tac
      x="xa"
      in exI)
  apply(rule_tac
      x="w'"
      in exI)
  apply(clarsimp)
  done

definition cfgSTD_first_symbol_of_derivable_marked_effect :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'event option set"
  where
    "cfgSTD_first_symbol_of_derivable_marked_effect G w \<equiv>
  {Some v | v.
    v \<in> cfg_events G
    \<and> (\<exists>d w'.
          cfgSTD.derivation_from_to G d
              {pair None \<lparr>cfg_conf = w\<rparr>}
              {y. \<exists>x. y = pair x \<lparr>cfg_conf = teB v # w'\<rparr>}
        \<and> setA w'={})}
  \<union> {x. x = None
        \<and> (\<exists>d. cfgSTD.derivation_from_to G d
                   {pair None \<lparr>cfg_conf = w\<rparr>}
                   {y. \<exists>x. y = pair x \<lparr>cfg_conf = []\<rparr>})}"

definition cfgSTD_first_symbol_of_derivable_effect :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'event option set"
  where
    "cfgSTD_first_symbol_of_derivable_effect G w \<equiv>
  {Some v | v.
    v \<in> cfg_events G
    \<and> (\<exists>d w'.
          cfgSTD.derivation_from_to G d
              {pair None \<lparr>cfg_conf = w\<rparr>}
              {y. \<exists>x. y = pair x \<lparr>cfg_conf = teB v # w'\<rparr>})}
  \<union> {x. x = None
        \<and> (\<exists>d. cfgSTD.derivation_from_to G d
                   {pair None \<lparr>cfg_conf = w\<rparr>}
                   {y. \<exists>x. y = pair x \<lparr>cfg_conf = []\<rparr>})}"

definition cfgSTD_first :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event)DT_two_elements list
  \<Rightarrow> ('event list) set"
  where
    "cfgSTD_first G k \<gamma> \<equiv>
  (\<lambda>x. take k x)
     ` {r. \<exists>d e1 n.
           cfgSTD.derivation G d
           \<and> maximum_of_domain d n
           \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<gamma>\<rparr>)
           \<and> d n = Some (pair e1 \<lparr>cfg_conf = liftB r\<rparr>)}"

lemma cfgSTD_first_contains_Nil_on_no_nonterminals: "
  setA w = {}
  \<Longrightarrow> [] \<in> cfgSTD_first G 0 w"
  apply(simp add: cfgSTD_first_def)
  apply(rule inMap)
  apply(clarsimp)
  apply(rule_tac
      x="filterB w"
      in exI)
  apply(rule_tac
      x="der1 \<lparr>cfg_conf=w\<rparr>"
      in exI)+
  apply(rule conjI)
   apply(rule cfgSTD.der1_is_derivation)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="0"
      in exI)
  apply(simp add: der1_def maximum_of_domain_def)
  apply (metis liftBDeConv2)
  done

lemma cfgSTD_first_sound: "
  cfgSTD_first G k \<gamma> = (\<lambda>x. take k x) ` {r. \<exists>d e1 n. cfgSTD.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf=\<gamma>\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=liftB r\<rparr>)}"
  apply(simp add: cfgSTD_first_def)
  done

lemma cfgSTD_first_on_terminal_string_is_kPrefix: "
  setA w = {}
  \<Longrightarrow> cfgSTD_first G k w = {kPrefix k (filterB w)}"
  apply(simp add: cfgSTD_first_sound)
  apply(auto)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(subgoal_tac "n=0")
    apply(rename_tac xa d e1 n)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa d)(*strict*)
    apply(rule_tac
      t="filterB (liftB xa)"
      and s="xa"
      in ssubst)
     apply(rename_tac xa d)(*strict*)
     apply(rule liftBDeConv1)
    apply(rename_tac xa d)(*strict*)
    apply(simp add: kPrefix_def)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(case_tac n)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa d e1 n nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa d e1 nat)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac xa d e1 nat)(*strict*)
    prefer 2
    apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac xa d e1 nat)(*strict*)
      apply(force)
     apply(rename_tac xa d e1 nat)(*strict*)
     apply(force)
    apply(rename_tac xa d e1 nat)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa d e1 nat e c)(*strict*)
   apply(case_tac c)
   apply(rename_tac xa d e1 nat e c cfg_conf)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w\<rparr> e c")
    apply(rename_tac xa d e1 nat e c cfg_conf)(*strict*)
    prefer 2
    apply(rule cfgSTD.position_change_due_to_step_relation)
      apply(rename_tac xa d e1 nat e c cfg_conf)(*strict*)
      apply(force)
     apply(rename_tac xa d e1 nat e c cfg_conf)(*strict*)
     apply(force)
    apply(rename_tac xa d e1 nat e c cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 nat e c cfg_conf)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(auto)
   apply(rename_tac xa d e1 nat e l r)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
  apply(rule inMap)
  apply(simp add: kPrefix_def)
  apply(rule_tac
      x="filterB w"
      in exI)
  apply(auto)
  apply(rule_tac
      x = "der1 \<lparr>cfg_conf = w\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgSTD.der1_is_derivation)
  apply(rule_tac
      x="None"
      in exI)
  apply(simp add: der1_def)
  apply(auto)
   apply(simp add: maximum_of_domain_def)
  apply(rule sym)
  apply(rule liftBDeConv2)
  apply(clarsimp)
  done

lemma cfgSTD_first_take: "
  k'\<le>k
  \<Longrightarrow> w \<in> cfgSTD_first G k v
  \<Longrightarrow> take k' w \<in> cfgSTD_first G k' v"
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac x d e1 n)(*strict*)
  apply(rule_tac
      t="(ord_class.min k' k)"
      and s="k'"
      in ssubst)
   apply(rename_tac x d e1 n)(*strict*)
   apply(force)
  apply(rename_tac x d e1 n)(*strict*)
  apply(rule inMap)
  apply(rule_tac
      x="x"
      in bexI)
   apply(rename_tac x d e1 n)(*strict*)
   apply(force)
  apply(rename_tac x d e1 n)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  done

lemma cfgSTD_firstk_shorter_than_k: "
  w \<in> cfgSTD_first G k v
  \<Longrightarrow> length w \<le> k"
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  done

lemma staysInAlpha2: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>)
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
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = cw\<rparr> e \<lparr>cfg_conf = w'nonterminal\<rparr>")
    apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
    apply(rule conjI)
     apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
     prefer 2
     apply(rule_tac
      w="cw"
      and e="e"
      in staysInSigma)
        apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
        apply(blast)
       apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
       apply(blast)
      apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
      apply(blast)
     apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
    apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
    prefer 2
    apply(rule cfgSTD.position_change_due_to_step_relation)
      apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
      apply(blast)+
   apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
   apply(case_tac e)
   apply(rename_tac ia e2a w'nonterminal e ea c cw prod_lhs prod_rhs)(*strict*)
   apply(clarsimp del: subsetI)
   apply(rename_tac ia w'nonterminal ea cw prod_lhs prod_rhs)(*strict*)
   apply(rename_tac Ax wx)
   apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
   apply(rule_tac
      B="setA cw \<union> setA wx"
      in subset_trans)
    apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
    apply(rule CFGStepNonTermBehaviour)
    apply(blast)
   apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
   apply(clarsimp del: subsetI)
   apply(rule_tac
      a="Ax"
      in prod_rhs_in_nonterms)
    apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
    apply(blast)+
   apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
  apply(rename_tac ia e2a w'nonterminal)(*strict*)
  apply(case_tac e2a)
   apply(rename_tac ia e2a w'nonterminal)(*strict*)
   apply(clarsimp)
   apply(rename_tac ia w'nonterminal)(*strict*)
   apply(rule cfgSTD.derivation_Always_PreEdge_prime)
    apply(rename_tac ia w'nonterminal)(*strict*)
    apply(blast)+
  done

lemma staysInSigma2: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>)
  \<Longrightarrow> setB w' \<subseteq> cfg_events G"
  apply(subgoal_tac "setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G")
   apply(force)
  apply(rule staysInAlpha2)
       apply(force)+
  done

lemma cfgSTD_firstk_in_cfg_events: "
  valid_cfg G
  \<Longrightarrow> setA v \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB v \<subseteq> cfg_events G
  \<Longrightarrow> w \<in> cfgSTD_first G k v
  \<Longrightarrow> set w \<subseteq> cfg_events G"
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp del: subsetI)
  apply(rename_tac x d e1 n)(*strict*)
  apply(rule_tac
      B="set x"
      in subset_trans)
   apply(rename_tac x d e1 n)(*strict*)
   apply(rule_tac
      t="set x"
      and s="set (take (k+(length x)) x)"
      in ssubst)
    apply(rename_tac x d e1 n)(*strict*)
    apply(force)
   apply(rename_tac x d e1 n)(*strict*)
   apply(rule setTakeIndexSubset)
  apply(rename_tac x d e1 n)(*strict*)
  apply(rule_tac
      s="setB (liftB x)"
      and t="set x"
      in ssubst)
   apply(rename_tac x d e1 n)(*strict*)
   apply(rule set_setBliftB)
  apply(rename_tac x d e1 n)(*strict*)
  apply(rule_tac
      w'="liftB x"
      and w="v"
      and i="0"
      and j="n"
      in staysInSigma2)
       apply(rename_tac x d e1 n)(*strict*)
       apply(blast)
      apply(rename_tac x d e1 n)(*strict*)
      apply(blast)
     apply(rename_tac x d e1 n)(*strict*)
     apply(blast)
    apply(rename_tac x d e1 n)(*strict*)
    apply(blast)
   apply(rename_tac x d e1 n)(*strict*)
   apply(blast)
  apply(rename_tac x d e1 n)(*strict*)
  apply(clarsimp)
  apply(blast)
  done

lemma terminals_at_ending_are_never_modified_list: "
  cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d (m + n)
  \<Longrightarrow> setA v={}
  \<Longrightarrow> d m = Some (pair e1 \<lparr>cfg_conf = w @ v\<rparr>)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<exists>e w. d x = Some (pair e \<lparr>cfg_conf = w @ v\<rparr>)"
  apply(rule cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(blast)+
  apply(auto)
  apply(rename_tac i e wa)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i e wa)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac i e wa)(*strict*)
     apply(force)
    apply(rename_tac i e wa)(*strict*)
    apply(force)
   apply(rename_tac i e wa)(*strict*)
   apply(force)
  apply(rename_tac i e wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e wa ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac i e wa ea c cfg_conf)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = wa @ v\<rparr> ea c")
   apply(rename_tac i e wa ea c cfg_conf)(*strict*)
   prefer 2
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac i e wa ea c cfg_conf)(*strict*)
     apply(force)
    apply(rename_tac i e wa ea c cfg_conf)(*strict*)
    apply(force)
   apply(rename_tac i e wa ea c cfg_conf)(*strict*)
   apply(force)
  apply(rename_tac i e wa ea c cfg_conf)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac i e wa ea l r)(*strict*)
  apply(subgoal_tac "\<exists>r'. r=r'@v")
   apply(rename_tac i e wa ea l r)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e wa ea l r)(*strict*)
  apply(rule terminal_end_suffix)
   apply(rename_tac i e wa ea l r)(*strict*)
   apply(force)
  apply(rename_tac i e wa ea l r)(*strict*)
  apply(force)
  done

lemma cfgSTD_firstk_in_kPrefix_with_terminal_end: "
  valid_cfg G
  \<Longrightarrow> setA v1 \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB v1 \<subseteq> cfg_events G
  \<Longrightarrow> set v2 \<subseteq> cfg_events G
  \<Longrightarrow> w \<in> cfgSTD_first G k (v1@(liftB v2))
  \<Longrightarrow> w \<in> (kPrefix k) ` {w. set w \<subseteq> cfg_events G \<and> (\<exists>x. w=x@v2)}"
  apply(subgoal_tac "set w \<subseteq> cfg_events G")
   prefer 2
   apply(rule_tac cfgSTD_firstk_in_cfg_events)
      prefer 4
      apply(force)
     apply(force)
    apply(simp (no_asm) only: setAConcat concat_asso)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "setA (liftB v2)={}")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule setA_liftB_empty)
   apply(simp (no_asm) only: setBConcat concat_asso)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "setB (liftB v2)=set v2")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule sym)
   apply(rule set_setBliftB)
  apply(rule inMap)
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac x d e1 n)(*strict*)
  apply(subgoal_tac "\<exists>x'. x=x'@v2")
   apply(rename_tac x d e1 n)(*strict*)
   apply(erule exE)+
   apply(rename_tac x d e1 n x')(*strict*)
   apply(rule_tac
      x="x'@v2"
      in exI)
   apply(clarsimp)
   apply(rename_tac d e1 n x')(*strict*)
   apply(simp add: kPrefix_def)
   apply(subgoal_tac "setB (liftB (x' @ v2)) \<subseteq> cfg_events G")
    apply(rename_tac d e1 n x')(*strict*)
    prefer 2
    apply(rule_tac
      w="v1 @ liftB v2"
      and i="0"
      and j="n"
      in staysInSigma2)
         apply(rename_tac d e1 n x')(*strict*)
         apply(force)
        apply(rename_tac d e1 n x')(*strict*)
        apply(simp (no_asm) only: setAConcat concat_asso)
        apply(clarsimp)
        apply(rename_tac d e1 n x' x)(*strict*)
        apply(subgoal_tac "setA (liftB v2)={}")
         apply(rename_tac d e1 n x' x)(*strict*)
         apply(force)
        apply(rename_tac d e1 n x' x)(*strict*)
        apply(rule setA_liftB_empty)
       apply(rename_tac d e1 n x')(*strict*)
       apply(simp (no_asm) only: setBConcat concat_asso)
       apply(clarsimp)
       apply(rename_tac d e1 n x' x)(*strict*)
       apply(subgoal_tac "setB (liftB v2)=set v2")
        apply(rename_tac d e1 n x' x)(*strict*)
        apply(force)
       apply(rename_tac d e1 n x' x)(*strict*)
       apply(rule sym)
       apply(rule set_setBliftB)
      apply(rename_tac d e1 n x')(*strict*)
      apply(force)
     apply(rename_tac d e1 n x')(*strict*)
     apply(force)
    apply(rename_tac d e1 n x')(*strict*)
    apply(force)
   apply(rename_tac d e1 n x')(*strict*)
   apply(rule_tac
      B="setB (liftB (x' @ v2))"
      in subset_trans)
    apply(rename_tac d e1 n x')(*strict*)
    apply(rule_tac
      t="setB (liftB (x' @ v2))"
      and s="set(x'@v2)"
      in ssubst)
     apply(rename_tac d e1 n x')(*strict*)
     apply(rule sym)
     apply(rule set_setBliftB)
    apply(rename_tac d e1 n x')(*strict*)
    apply(force)
   apply(rename_tac d e1 n x')(*strict*)
   apply(force)
  apply(rename_tac x d e1 n)(*strict*)
  apply(subgoal_tac "\<exists>e w. d n = Some (pair e \<lparr>cfg_conf = w @ (liftB v2)\<rparr>)")
   apply(rename_tac x d e1 n)(*strict*)
   prefer 2
   apply(rule_tac
      m="0"
      and n="n"
      in terminals_at_ending_are_never_modified_list)
        apply(rename_tac x d e1 n)(*strict*)
        apply(force)
       apply(rename_tac x d e1 n)(*strict*)
       apply(force)
      apply(rename_tac x d e1 n)(*strict*)
      apply(rule setA_liftB_empty)
     apply(rename_tac x d e1 n)(*strict*)
     apply(force)
    apply(rename_tac x d e1 n)(*strict*)
    apply(force)
   apply(rename_tac x d e1 n)(*strict*)
   apply(force)
  apply(rename_tac x d e1 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e1 n w)(*strict*)
  apply(rule_tac
      x="filterB w"
      in exI)
  apply(rule_tac
      t="v2"
      and s="filterB (liftB v2)"
      in subst)
   apply(rename_tac x d e1 n w)(*strict*)
   apply(rule liftBDeConv1)
  apply(rename_tac x d e1 n w)(*strict*)
  apply(rule_tac
      t="filterB w @ filterB (liftB v2)"
      and s="filterB (w @ (liftB v2))"
      in subst)
   apply(rename_tac x d e1 n w)(*strict*)
   apply(rule filterB_commutes_over_concat)
  apply(rename_tac x d e1 n w)(*strict*)
  apply(rule_tac
      t="w@(liftB v2)"
      and s="liftB x"
      in ssubst)
   apply(rename_tac x d e1 n w)(*strict*)
   apply(force)
  apply(rename_tac x d e1 n w)(*strict*)
  apply(rule sym)
  apply(rule liftBDeConv1)
  done

lemma terminal_at_beginning_are_never_modified: "
  cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d (m + n)
  \<Longrightarrow> d m = Some (pair e1 \<lparr>cfg_conf = teB b # w\<rparr>)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<exists>e w. d x = Some (pair e \<lparr>cfg_conf = teB b # w\<rparr>)"
  apply(rule cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(blast)+
  apply(auto)
  apply(rename_tac i e wa)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i e wa)(*strict*)
   apply(clarsimp, case_tac c)
   apply(rename_tac i e wa ea c cfg_conf)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = teB b # wa\<rparr> ea c")
    apply(rename_tac i e wa ea c cfg_conf)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(auto)
    apply(rename_tac i e wa ea l r)(*strict*)
    apply(case_tac l)
     apply(rename_tac i e wa ea l r)(*strict*)
     apply(auto)
   apply(rename_tac i e wa ea cfg_conf)(*strict*)
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac i e wa ea cfg_conf)(*strict*)
     apply(blast)+
  apply(rename_tac i e wa)(*strict*)
  apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
    apply(rename_tac i e wa)(*strict*)
    apply(blast)+
  apply(rename_tac i e wa)(*strict*)
  apply(arith)
  done

lemma terminal_at_ending_is_never_modified: "
  cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d (m + n)
  \<Longrightarrow> d m = Some (pair e1 \<lparr>cfg_conf = w @ [teB b]\<rparr>)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<exists>e w. d x = Some (pair e \<lparr>cfg_conf = w @ [teB b]\<rparr>)"
  apply(rule cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(blast)+
  apply(auto)
  apply(rename_tac i e wa)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i e wa)(*strict*)
   apply(clarsimp, case_tac c)
   apply(rename_tac i e wa ea c cfg_conf)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = wa @ [teB b]\<rparr> ea c")
    apply(rename_tac i e wa ea c cfg_conf)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(auto)
    apply(rename_tac i e wa ea l r)(*strict*)
    apply(case_tac r)
     apply(rename_tac i e wa ea l r)(*strict*)
     apply(force)
    apply(rename_tac i e wa ea l r a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
     apply(rename_tac i e wa ea l r a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac i e wa ea l r a list)(*strict*)
    apply(thin_tac "r = a # list")
    apply(auto)
   apply(rename_tac i e wa ea cfg_conf)(*strict*)
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac i e wa ea cfg_conf)(*strict*)
     apply(blast)+
  apply(rename_tac i e wa)(*strict*)
  apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
    apply(rename_tac i e wa)(*strict*)
    apply(blast)+
  apply(rename_tac i e wa)(*strict*)
  apply(arith)
  done

lemma contextExtendIsFromTo: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None dF} {y. \<exists>xa. y = pair xa dT}
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> C = (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)
  \<Longrightarrow> cfgSTD.derivation_from_to G (derivation_map d C) {pair None (C dF)} {y. \<exists>xa. y = pair xa (C dT)}"
  apply(subgoal_tac "d 0 = Some(pair None dF)")
   apply(subgoal_tac "\<exists>e1. d m = Some(pair e1 dT)")
    apply(erule_tac exE)+
    apply(rename_tac e1)(*strict*)
    defer
    apply(rule cfgSTD.toAtMaxDom)
     apply(blast)+
   apply(rule cfgSTD.fromAtZero)
    apply(blast)+
  apply(rename_tac e1)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
  apply(auto)
     apply(rename_tac e1 n xa)(*strict*)
     apply(rule cfgSTD.derivation_map_preserves_derivation2)
      apply(rename_tac e1 n xa)(*strict*)
      apply(blast)
     apply(rename_tac e1 n xa)(*strict*)
     apply(rule cfgSTD_step_relation_closed_under_post_context)
      apply(rename_tac e1 n xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac e1 n xa)(*strict*)
     apply(blast)
    apply(rename_tac e1 n xa)(*strict*)
    prefer 2
    apply(rule cfgSTD.derivation_map_preserves_derivation2)
     apply(rename_tac e1 n xa)(*strict*)
     apply(blast)
    apply(rename_tac e1 n xa)(*strict*)
    apply(rule cfgSTD_step_relation_closed_under_post_context)
     apply(rename_tac e1 n xa)(*strict*)
     apply(blast)
    apply(rename_tac e1 n xa)(*strict*)
    apply(blast)
   apply(rename_tac e1 n xa)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac e1 n xa)(*strict*)
  apply(subgoal_tac "maximum_of_domain (derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) m")
   apply(rename_tac e1 n xa)(*strict*)
   defer
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(blast)
  apply(rename_tac e1 n xa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(auto)
  apply(rename_tac e1 n xa y)(*strict*)
  apply(rule_tac
      x = "m"
      in exI)
  apply(auto)
  apply(rule_tac
      x = "e1"
      in exI)
  apply(simp add: derivation_map_def)
  done

lemma contextExtendIsFromTo2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None dF} {y. \<exists>xa. y = pair xa dT}
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> C = (\<lambda>v. \<lparr>cfg_conf = w @ (cfg_conf v)\<rparr>)
  \<Longrightarrow> cfgSTD.derivation_from_to G (derivation_map d C) {pair None (C dF)} {y. \<exists>xa. y = pair xa (C dT)}"
  apply(subgoal_tac "d 0 = Some(pair None dF)")
   apply(subgoal_tac "\<exists>e1. d m = Some(pair e1 dT)")
    apply(erule_tac exE)+
    apply(rename_tac e1)(*strict*)
    defer
    apply(rule cfgSTD.toAtMaxDom)
     apply(blast)+
   apply(rule cfgSTD.fromAtZero)
    apply(blast)+
  apply(rename_tac e1)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
  apply(auto)
     apply(rename_tac e1 n xa)(*strict*)
     apply(rule cfgSTD.derivation_map_preserves_derivation2)
      apply(rename_tac e1 n xa)(*strict*)
      apply(blast)
     apply(rename_tac e1 n xa)(*strict*)
     apply(rule cfgSTD_step_relation_closed_under_post_context2)
      apply(rename_tac e1 n xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac e1 n xa)(*strict*)
     apply(blast)
    apply(rename_tac e1 n xa)(*strict*)
    prefer 2
    apply(rule cfgSTD.derivation_map_preserves_derivation2)
     apply(rename_tac e1 n xa)(*strict*)
     apply(blast)
    apply(rename_tac e1 n xa)(*strict*)
    apply(rule cfgSTD_step_relation_closed_under_post_context2)
     apply(rename_tac e1 n xa)(*strict*)
     apply(blast)
    apply(rename_tac e1 n xa)(*strict*)
    apply(blast)
   apply(rename_tac e1 n xa)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac e1 n xa)(*strict*)
  apply(subgoal_tac "maximum_of_domain (derivation_map d (\<lambda>v. \<lparr>cfg_conf = w @ (cfg_conf v)\<rparr>)) m")
   apply(rename_tac e1 n xa)(*strict*)
   defer
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(blast)
  apply(rename_tac e1 n xa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(auto)
  apply(rename_tac e1 n xa y)(*strict*)
  apply(rule_tac
      x = "m"
      in exI)
  apply(auto)
  apply(rule_tac
      x = "e1"
      in exI)
  apply(simp add: derivation_map_def)
  done

lemma cfgSTD_first_drop_first_terminal: "
  valid_cfg G
  \<Longrightarrow> take (k - 1) w \<in> cfgSTD_first G (k - 1) v
  \<Longrightarrow> take (ord_class.max k 1) (x#w) \<in> cfgSTD_first G (ord_class.max k 1) (teB x#v)"
  apply(simp add: cfgSTD_first_def)
  apply(rule inMap)
  apply(auto)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x="x#xa"
      in exI)
  apply(auto)
   apply(rename_tac xa d e1 n)(*strict*)
   prefer 2
   apply(case_tac k)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(auto)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x = "derivation_map d (\<lambda>v. \<lparr>cfg_conf = [teB x]@ (cfg_conf v)\<rparr>)"
      in exI)
  apply(rule conjI)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(rule cfgSTD.from_to_is_der)
   apply(rule_tac
      w="[teB x]"
      and dF="\<lparr>cfg_conf = v\<rparr>"
      and dT="\<lparr>cfg_conf=liftB xa\<rparr>"
      in contextExtendIsFromTo2)
      apply(rename_tac x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac x d e1 n)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
     apply(auto)
   apply(rename_tac x d e1 n)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(auto)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(auto)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(rename_tac x d e1 n)(*strict*)
    apply(blast)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(simp add: derivation_map_def)+
  done

lemma cfgSTD_first_add_terminal_front_prime: "
  valid_cfg G'
  \<Longrightarrow> take k y \<in> cfgSTD_first G' k w
  \<Longrightarrow> take k (x # y) \<in> cfgSTD_first G' k ([teB x] @ w)"
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule inMap)
  apply(rule_tac
      x="x#xa"
      in bexI)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(case_tac k)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(auto)
   apply(rename_tac x d e1 n nat)(*strict*)
   apply(thin_tac "cfgSTD.derivation G' d")
   apply(thin_tac "maximum_of_domain d n")
   apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
   apply(thin_tac "d n = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
   apply(case_tac "length x \<le> nat")
    apply(rename_tac x d e1 n nat)(*strict*)
    apply(auto)
   apply(rename_tac x nat)(*strict*)
   apply(rule_tac
      t="take nat x"
      and s="take nat (take (Suc nat) x)"
      in ssubst)
    apply(rename_tac x nat)(*strict*)
    apply(rule_tac
      s="take (ord_class.min nat (Suc nat)) x"
      and t="take nat (take (Suc nat) x)"
      in ssubst)
     apply(rename_tac x nat)(*strict*)
     apply(rule take_take)
    apply(rename_tac x nat)(*strict*)
    apply(rule_tac
      t="ord_class.min nat (Suc nat)"
      and s="nat"
      in ssubst)
     apply(rename_tac x nat)(*strict*)
     apply(force)
    apply(rename_tac x nat)(*strict*)
    apply(force)
   apply(rename_tac x nat)(*strict*)
   apply(rule_tac
      t="take (Suc nat) x"
      and s="take (Suc nat) y"
      in ssubst)
    apply(rename_tac x nat)(*strict*)
    apply(force)
   apply(rename_tac x nat)(*strict*)
   apply(thin_tac "take (Suc nat) y = take (Suc nat) x")
   apply(clarsimp)
   apply(rule_tac
      t="ord_class.min nat (Suc nat)"
      and s="nat"
      in ssubst)
    apply(rename_tac x nat)(*strict*)
    apply(force)
   apply(rename_tac x nat)(*strict*)
   apply(auto)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x = "derivation_map d (\<lambda>v. \<lparr>cfg_conf = [teB x]@ (cfg_conf v)\<rparr>)"
      in exI)
  apply(rule conjI)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(rule cfgSTD.from_to_is_der)
   apply(rule_tac
      w="[teB x]"
      and dF="\<lparr>cfg_conf = w\<rparr>"
      and dT="\<lparr>cfg_conf=liftB xa\<rparr>"
      in contextExtendIsFromTo2)
      apply(rename_tac x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac x d e1 n)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
     apply(auto)
   apply(rename_tac x d e1 n)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(auto)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(auto)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(rename_tac x d e1 n)(*strict*)
    apply(blast)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(simp add: derivation_map_def)+
  done

lemma cfgSTD_first_add_terminal_front_prime_prime: "
  valid_cfg G'
  \<Longrightarrow> take k y \<in> cfgSTD_first G' k w
  \<Longrightarrow> take (Suc k) (x # y) \<in> cfgSTD_first G' (Suc k) ([teB x] @ w)"
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule inMap)
  apply(rule_tac
      x="x#xa"
      in bexI)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(case_tac k)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(auto)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x = "derivation_map d (\<lambda>v. \<lparr>cfg_conf = [teB x]@ (cfg_conf v)\<rparr>)"
      in exI)
  apply(rule conjI)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(rule cfgSTD.from_to_is_der)
   apply(rule_tac
      w="[teB x]"
      and dF="\<lparr>cfg_conf = w\<rparr>"
      and dT="\<lparr>cfg_conf=liftB xa\<rparr>"
      in contextExtendIsFromTo2)
      apply(rename_tac x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac x d e1 n)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
     apply(auto)
   apply(rename_tac x d e1 n)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(auto)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(auto)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(rename_tac x d e1 n)(*strict*)
    apply(blast)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(simp add: derivation_map_def)+
  done

lemma cfgSTD_first_add_terminal_front: "
  valid_cfg G'
  \<Longrightarrow> take k y @ take (k - length y) [Do] \<in> cfgSTD_first G' k (\<beta> @ liftB z)
  \<Longrightarrow> (take k (x # y)) @ take (k - length (x # y)) [Do] \<in> cfgSTD_first G' k (([teB x] @ \<beta>) @ liftB z)"
  apply(simp add: cfgSTD_first_def)
  apply(clarsimp)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule inMap)
  apply(rule_tac
      x="x#xa"
      in bexI)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(case_tac k)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(auto)
   apply(rename_tac x d e1 n nat)(*strict*)
   apply(thin_tac "cfgSTD.derivation G' d")
   apply(thin_tac "maximum_of_domain d n")
   apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB z\<rparr>)")
   apply(thin_tac "d n = Some (pair e1 \<lparr>cfg_conf = liftB x\<rparr>)")
   apply(case_tac "length x \<le> nat")
    apply(rename_tac x d e1 n nat)(*strict*)
    apply(auto)
   apply(rename_tac x nat)(*strict*)
   apply(rule_tac
      t="take nat x"
      and s="take nat (take (Suc nat) x)"
      in ssubst)
    apply(rename_tac x nat)(*strict*)
    apply(rule_tac
      s="take (ord_class.min nat (Suc nat)) x"
      and t="take nat (take (Suc nat) x)"
      in ssubst)
     apply(rename_tac x nat)(*strict*)
     apply(rule take_take)
    apply(rename_tac x nat)(*strict*)
    apply(rule_tac
      t="ord_class.min nat (Suc nat)"
      and s="nat"
      in ssubst)
     apply(rename_tac x nat)(*strict*)
     apply(force)
    apply(rename_tac x nat)(*strict*)
    apply(force)
   apply(rename_tac x nat)(*strict*)
   apply(rule_tac
      t="take (Suc nat) x"
      and s="take (Suc nat) y @ take (Suc nat - length y) [Do]"
      in ssubst)
    apply(rename_tac x nat)(*strict*)
    apply(force)
   apply(rename_tac x nat)(*strict*)
   apply(thin_tac "take (Suc nat) y @ take (Suc nat - length y) [Do] = take (Suc nat) x")
   apply(clarsimp)
   apply(rule_tac
      t="ord_class.min nat (Suc nat)"
      and s="nat"
      in ssubst)
    apply(rename_tac x nat)(*strict*)
    apply(force)
   apply(rename_tac x nat)(*strict*)
   apply(auto)
   apply(rule_tac
      t="ord_class.min (nat - ord_class.min (length y) (Suc nat)) (Suc nat - length y)"
      and s="nat - length y"
      in ssubst)
    apply(rename_tac x nat)(*strict*)
    apply(force)
   apply(rename_tac x nat)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x = "derivation_map d (\<lambda>v. \<lparr>cfg_conf = [teB x]@ (cfg_conf v)\<rparr>)"
      in exI)
  apply(rule conjI)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(rule cfgSTD.from_to_is_der)
   apply(rule_tac
      w="[teB x]"
      and dF="\<lparr>cfg_conf = \<beta> @ liftB z\<rparr>"
      and dT="\<lparr>cfg_conf=liftB xa\<rparr>"
      in contextExtendIsFromTo2)
      apply(rename_tac x d e1 n)(*strict*)
      apply(force)
     apply(rename_tac x d e1 n)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
     apply(auto)
   apply(rename_tac x d e1 n)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(auto)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(auto)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(rename_tac x d e1 n)(*strict*)
    apply(blast)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(simp add: derivation_map_def)+
  done

lemma concatExtendIsFromTo: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = v\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = R\<rparr>}
  \<Longrightarrow> maximum_of_domain d1 m1
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> cfgSTD.derivation_from_to G (derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) d2 m1) {pair None \<lparr>cfg_conf = v @ w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = R\<rparr>}"
  apply(rule cfgSTD.concatIsFromTo)
     apply(auto)
   apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>) \<lparr>cfg_conf = v\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>) \<lparr>cfg_conf = []\<rparr>)}")
    prefer 2
    apply(rule contextExtendIsFromTo)
       apply(blast)+
   apply(auto)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  done

lemma concatExtendIsFromTo2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = v\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = R\<rparr>}
  \<Longrightarrow> maximum_of_domain d1 m1
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> cfgSTD.derivation_from_to G (derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = w@ (cfg_conf v)\<rparr>)) d2 m1) {pair None \<lparr>cfg_conf = w@ v\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = R\<rparr>}"
  apply(rule cfgSTD.concatIsFromTo)
     apply(auto)
   apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = w @ (cfg_conf v)\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = w@(cfg_conf v)\<rparr>) \<lparr>cfg_conf = v\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = w@(cfg_conf v)\<rparr>) \<lparr>cfg_conf = []\<rparr>)}")
    prefer 2
    apply(rule contextExtendIsFromTo2)
       apply(blast)+
   apply(auto)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  done

lemma concatExtendIsFromToBoth: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>}
  \<Longrightarrow> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>}
  \<Longrightarrow> maximum_of_domain d1 m1
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> cfgSTD.derivation_from_to G (derivation_append
(derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w2\<rparr>))
(derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = w1' @ (cfg_conf v)\<rparr>))
m1) {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1' @ w2'\<rparr>}"
  apply(rule_tac
      dJ="\<lparr>cfg_conf=w1'@w2\<rparr>"
      in cfgSTD.concatIsFromTo)
     apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w2\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w2\<rparr>) \<lparr>cfg_conf = w1\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w2\<rparr>) \<lparr>cfg_conf = w1'\<rparr>)}")
      apply(clarsimp)
     apply(rule contextExtendIsFromTo)
        apply(blast)+
    defer
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(blast)
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(blast)
  apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = w1' @ (cfg_conf v)\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = w1' @ (cfg_conf v)\<rparr>) \<lparr>cfg_conf = w2\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = w1' @ (cfg_conf v)\<rparr>) \<lparr>cfg_conf = w2'\<rparr>)}")
   apply(clarsimp)
  apply(rule contextExtendIsFromTo2)
     apply(blast)+
  done

lemma noStepFromTerminal: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teB b]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w'\<rparr>}
  \<Longrightarrow> x = b"
  apply(subgoal_tac "maximum_of_domain d 0")
   apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = [teB b]\<rparr>)")
    apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = teB x # w'\<rparr>)")
     apply(erule exE)
     apply(rename_tac e)(*strict*)
     apply(clarsimp)
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(clarsimp)
   apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = [teB b]\<rparr>}. d 0 = Some x")
    apply(blast)
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac n xa)(*strict*)
  apply(erule_tac
      x = "Suc 0"
      in allE)
  apply(auto)
  apply(case_tac "d (Suc 0)")
   apply(rename_tac n xa)(*strict*)
   apply(auto)
   apply(simp add: maximum_of_domain_def)
   apply(case_tac "d 0")
    apply(rename_tac n xa)(*strict*)
    apply(auto)
  apply(rename_tac n xa a)(*strict*)
  apply(case_tac a)
  apply(rename_tac n xa a option ba)(*strict*)
  apply(auto)
  apply(rename_tac n xa option ba)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac n xa option ba)(*strict*)
   apply(auto)
  apply(rename_tac n xa option ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac n xa option ba)(*strict*)
   apply(auto)
  apply(rename_tac n xa ba a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac n xa ba a l r)(*strict*)
  apply(case_tac a)
  apply(rename_tac n xa ba a l r prod_lhsa prod_rhsa)(*strict*)
  apply(auto)
  apply(rename_tac n xa ba l r prod_lhs prod_rhs)(*strict*)
  apply(case_tac ba)
  apply(rename_tac n xa ba l r prod_lhs prod_rhs cfg_confa)(*strict*)
  apply(auto)
  apply(rename_tac n xa l r prod_lhs prod_rhs)(*strict*)
  apply(subgoal_tac "[teB b] \<noteq> l @ teA prod_lhs # r")
   apply(rename_tac n xa l r prod_lhs prod_rhs)(*strict*)
   apply(blast)
  apply(rename_tac n xa l r prod_lhs prod_rhs)(*strict*)
  apply(rule setA_with_context_is_not_setB)
  done

lemma noStepFromNone: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = []\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = x # w\<rparr>}
  \<Longrightarrow> P"
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(case_tac n)
   apply(rename_tac n)(*strict*)
   defer
   apply(rename_tac n nat)(*strict*)
   apply(rule cfgSTD.noNonEmptyDeriFromEmpty)
     apply(rename_tac n nat)(*strict*)
     prefer 3
     apply(rule cfgSTD.from_to_is_from)
     apply(blast)
    apply(rename_tac n nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e c2)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
   apply(rename_tac n nat)(*strict*)
   apply(blast)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = []\<rparr>)")
   apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = x # w\<rparr>)")
    apply(erule exE)
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(clarsimp)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = []\<rparr>}. d 0 = Some x")
   apply(blast)
  apply(rule cfgSTD.derivation_from_starts_from)
  apply(rule cfgSTD.from_to_is_from)
  apply(blast)
  done

lemma noStepWithoutNonTerm: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}
  \<Longrightarrow> setA w = {}
  \<Longrightarrow> w=w'"
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(case_tac n)
   apply(rename_tac n)(*strict*)
   defer
   apply(rename_tac n nat)(*strict*)
   apply(rule cfgSTD.noNonEmptyDeriFromEmpty)
     apply(rename_tac n nat)(*strict*)
     prefer 3
     apply(rule cfgSTD.from_to_is_from)
     apply(blast)
    apply(rename_tac n nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e c2)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac nat e c2 l r)(*strict*)
    apply(subgoal_tac "prod_lhs e\<in> setA (l @ teA (prod_lhs e) # r)")
     apply(rename_tac nat e c2 l r)(*strict*)
     apply(force)
    apply(rename_tac nat e c2 l r)(*strict*)
    apply(rule elemInsetA)
   apply(rename_tac n nat)(*strict*)
   apply(blast)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
   apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = w'\<rparr>)")
    apply(erule exE)
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(clarsimp)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w\<rparr>}. d 0 = Some x")
   apply(blast)
  apply(rule cfgSTD.derivation_from_starts_from)
  apply(rule cfgSTD.from_to_is_from)
  apply(blast)
  done

lemma hasStep: "
  maximum_of_domain d (Suc n)
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w\<rparr>}
  \<Longrightarrow> \<exists>v. (cfgSTD_step_relation G \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = v\<rparr> \<and> d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>) \<lparr>cfg_conf = v\<rparr>) \<and> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G)"
  apply(case_tac "d (Suc 0)")
   apply(rule_tac
      d = "d"
      and n = "Suc 0"
      in cfgSTD.maximum_of_domainSmaller)
      apply(blast)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(arith)
   apply(blast)
  apply(rename_tac a)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
  apply(auto)
  apply(rename_tac a na xa)(*strict*)
  apply(erule_tac
      x = "Suc 0"
      in allE)
  apply(auto)
  apply(case_tac "d 0")
   apply(rename_tac a na xa)(*strict*)
   apply(auto)
  apply(rename_tac a na xa)(*strict*)
  apply(case_tac a)
  apply(rename_tac a na xa option b)(*strict*)
  apply(auto)
  apply(rename_tac na xa option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac na xa option b)(*strict*)
   apply(auto)
  apply(rename_tac na xa b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac na xa b a prod_lhs prod_rhs)(*strict*)
  apply(auto)
     apply(rename_tac na xa b prod_lhs prod_rhs)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(auto)
      apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
      apply(case_tac b)
      apply(rename_tac na xa b prod_lhs prod_rhs l r cfg_confa)(*strict*)
      apply(auto)
      apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
      apply(subgoal_tac "l = [] \<and> r = [] \<and> teA A = teA prod_lhs")
       apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
       prefer 2
       apply(rule_tac
      x = "teA A"
      and y = "teA prod_lhs"
      in length_1_context_empty)
       apply(clarsimp)
      apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
      apply(clarsimp)
     apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
     apply(rule_tac
      x = "l"
      in exI)
     apply(rule_tac
      x = "r"
      in exI)
     apply(auto)
      apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
      apply(subgoal_tac "l = [] \<and> r = [] \<and> teA A = teA prod_lhs")
       apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
       prefer 2
       apply(rule_tac
      x = "teA A"
      and y = "teA prod_lhs"
      in length_1_context_empty)
       apply(clarsimp)
      apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
      apply(clarsimp)
     apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
     apply(case_tac b)
     apply(rename_tac na xa b prod_lhs prod_rhs l r cfg_confa)(*strict*)
     apply(auto)
     apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
     apply(subgoal_tac "l = [] \<and> r = [] \<and> teA A = teA prod_lhs")
      apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
      prefer 2
      apply(rule_tac
      x = "teA A"
      and y = "teA prod_lhs"
      in length_1_context_empty)
      apply(clarsimp)
     apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac na xa b prod_lhs prod_rhs)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(auto)
    apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
    apply(subgoal_tac "l = [] \<and> r = [] \<and> teA A = teA prod_lhs")
     apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
     prefer 2
     apply(rule_tac
      x = "teA A"
      and y = "teA prod_lhs"
      in length_1_context_empty)
     apply(clarsimp)
    apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac na xa b prod_lhs prod_rhs)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(auto)
   apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
   apply(case_tac b)
   apply(rename_tac na xa b prod_lhs prod_rhs l r cfg_confa)(*strict*)
   apply(auto)
   apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
   apply(subgoal_tac "l = [] \<and> r = [] \<and> teA A = teA prod_lhs")
    apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
    prefer 2
    apply(rule_tac
      x = "teA A"
      and y = "teA prod_lhs"
      in length_1_context_empty)
    apply(clarsimp)
   apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
   apply(clarsimp)
  apply(rename_tac na xa b prod_lhs prod_rhs)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(auto)
  apply(rename_tac na xa b prod_lhs prod_rhs l r)(*strict*)
  apply(case_tac b)
  apply(rename_tac na xa b prod_lhs prod_rhs l r cfg_confa)(*strict*)
  apply(auto)
  apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
  apply(subgoal_tac "A = prod_lhs")
   apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
   apply(blast)
  apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
  apply(subgoal_tac "l = [] \<and> r = [] \<and> teA A = teA prod_lhs")
   apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
   prefer 2
   apply(rule_tac
      x = "teA A"
      and y = "teA prod_lhs"
      in length_1_context_empty)
   apply(clarsimp)
  apply(rename_tac na xa prod_lhs prod_rhs l r)(*strict*)
  apply(clarsimp)
  done

lemma terminalStaysInside: "
  cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d (m + n)
  \<Longrightarrow> d m = Some (pair e1 \<lparr>cfg_conf = w1 @ teB b # w2\<rparr>)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<exists>e w1 w2. d x = Some (pair e \<lparr>cfg_conf = w1 @ teB b # w2\<rparr>)"
  apply(rule cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(blast)+
  apply(auto)
  apply(rename_tac i e w1a w2a)(*strict*)
  apply(case_tac "d (Suc i)")
   apply(rename_tac i e w1a w2a)(*strict*)
   apply(auto)
   apply(rule_tac
      n = "Suc i"
      in cfgSTD.maximum_of_domainSmaller)
      apply(rename_tac i e w1a w2a)(*strict*)
      apply(blast)
     apply(rename_tac i e w1a w2a)(*strict*)
     apply(blast)
    apply(rename_tac i e w1a w2a)(*strict*)
    apply(arith)
   apply(rename_tac i e w1a w2a)(*strict*)
   apply(blast)
  apply(rename_tac i e w1a w2a a)(*strict*)
  apply(simp add: cfgSTD.derivation_def)
  apply(erule_tac
      x = "Suc i"
      in allE)
  apply(auto)
  apply(case_tac a)
  apply(rename_tac i e w1a w2a a option ba)(*strict*)
  apply(auto)
  apply(rename_tac i e w1a w2a option ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac i e w1a w2a option ba)(*strict*)
   apply(auto)
  apply(rename_tac i e w1a w2a ba a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i e w1a w2a ba a prod_lhs prod_rhs)(*strict*)
  apply(auto)
  apply(rename_tac i e w1a w2a ba prod_lhs prod_rhs)(*strict*)
  apply(case_tac ba)
  apply(rename_tac i e w1a w2a ba prod_lhs prod_rhs cfg_conf)(*strict*)
  apply(auto)
  apply(rename_tac i e w1a w2a prod_lhs prod_rhs cfg_conf)(*strict*)
  apply(rule terminalPreserved)
  apply(blast)
  done

lemma canElimAll1: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> d m = Some (pair xa \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> setB w = {}"
  apply(case_tac "\<exists>x. x \<in> setB w")
   defer
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w = w1 @ [teB x] @ w2")
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac x)(*strict*)
    apply(auto)
   apply(rename_tac x w1 w2)(*strict*)
   apply(rename_tac b w1 w2)
   apply(rename_tac b w1 w2)(*strict*)
   apply(subgoal_tac "\<exists>e w1 w2. d m = Some (pair e \<lparr>cfg_conf = w1 @ teB b # w2\<rparr>)")
    apply(rename_tac b w1 w2)(*strict*)
    apply(subgoal_tac "\<exists>e. d m = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
     apply(rename_tac b w1 w2)(*strict*)
     apply(clarsimp)
    apply(rename_tac b w1 w2)(*strict*)
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac b w1 w2)(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac b w1 w2)(*strict*)
    apply(blast)
   apply(rename_tac b w1 w2)(*strict*)
   apply(rule_tac
      ?e1.0 = "None"
      and m = "0"
      and n = "m"
      and ?w1.0 = "w1"
      and ?w2.0 = "w2"
      in terminalStaysInside)
       apply(rename_tac b w1 w2)(*strict*)
       apply(rule cfgSTD.from_to_is_der)
       apply(blast)
      apply(rename_tac b w1 w2)(*strict*)
      apply(rule_tac
      s = "m"
      in ssubst)
       apply(rename_tac b w1 w2)(*strict*)
       apply(arith)
      apply(rename_tac b w1 w2)(*strict*)
      apply(clarsimp)
     apply(rename_tac b w1 w2)(*strict*)
     apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1 @ teB b # w2\<rparr>}. d 0 = Some x")
      apply(rename_tac b w1 w2)(*strict*)
      apply(clarsimp)
     apply(rename_tac b w1 w2)(*strict*)
     apply(rule cfgSTD.derivation_from_starts_from)
     apply(rule cfgSTD.from_to_is_from)
     apply(blast)
    apply(rename_tac b w1 w2)(*strict*)
    apply(arith)
   apply(rename_tac b w1 w2)(*strict*)
   apply(arith)
  apply(rename_tac x)(*strict*)
  apply(rule context_exists_for_elem_of_setB)
  apply(blast)
  done

lemma empty_result_derivation_can_be_decomposed: "
  valid_cfg G
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> \<exists>d1 d2 m1 m2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>} \<and> maximum_of_domain d1 m1 \<and> maximum_of_domain d2 m2 \<and> m1+m2 = m"
  apply(subgoal_tac "\<forall>m d w1 w2. maximum_of_domain d m \<longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>} \<longrightarrow> (\<exists>d1 d2 m1 m2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>} \<and> maximum_of_domain d1 m1 \<and> maximum_of_domain d2 m2 \<and> m1+m2 = m)")
   apply(blast)
  apply(thin_tac "maximum_of_domain d m")
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>}")
  apply(rule allI)
  apply(rename_tac m)(*strict*)
  apply(rule_tac nat.induct)
   apply(rename_tac m)(*strict*)
   apply(auto)
   apply(rename_tac d w1 w2)(*strict*)
   apply(subgoal_tac "w1 @ w2 = []")
    apply(rename_tac d w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac d)(*strict*)
    apply(rule_tac
      x = "der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
     apply(simp add: cfgSTD.der1_is_derivation)
     apply(simp add: cfgSTD.der1_is_derivation der1_def)
    apply(rename_tac d)(*strict*)
    apply(rule_tac
      x = "der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
     apply(simp add: cfgSTD.der1_is_derivation der1_maximum_of_domain)
     apply(simp add: cfgSTD.der1_is_derivation der1_maximum_of_domain der1_def)
    apply(rename_tac d)(*strict*)
    apply(simp add: cfgSTD.der1_is_derivation der1_maximum_of_domain)
   apply(rename_tac d w1 w2)(*strict*)
   apply(subgoal_tac "[]=w1@w2")
    apply(rename_tac d w1 w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w1@w2\<rparr>)")
    apply(rename_tac d w1 w2)(*strict*)
    apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
     apply(rename_tac d w1 w2)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w1 w2)(*strict*)
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac d w1 w2)(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac d w1 w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1@w2\<rparr>}. d 0 = Some x")
    apply(rename_tac d w1 w2)(*strict*)
    apply(blast)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac nat d w1 w2)(*strict*)
  apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w1 @ w2\<rparr>)")
   apply(rename_tac nat d w1 w2)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) \<lparr>cfg_conf = c\<rparr>)")
    apply(rename_tac nat d w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat d w1 w2 e c)(*strict*)
    apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w1 @ w2\<rparr> e \<lparr>cfg_conf = c\<rparr>")
     apply(rename_tac nat d w1 w2 e c)(*strict*)
     apply(erule_tac
      x = "derivation_drop d (Suc 0)"
      in allE)
     apply(erule impE)
      apply(rename_tac nat d w1 w2 e c)(*strict*)
      apply(rule derivation_drop_preserves_generates_maximum_of_domain)
      apply(blast)
     apply(rename_tac nat d w1 w2 e c)(*strict*)
     apply(case_tac "\<not> (\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = c)")
      apply(rename_tac nat d w1 w2 e c)(*strict*)
      apply(subgoal_tac "\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = c")
       apply(rename_tac nat d w1 w2 e c)(*strict*)
       apply(thin_tac "\<not> (\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = c)")
       apply(clarsimp)
       apply(rename_tac nat d w1 w2 e c')(*strict*)
       apply(erule_tac
      x = "w1"
      in allE)
       apply(erule_tac
      x = "c'"
      in allE)
       apply(erule impE)
        apply(rename_tac nat d w1 w2 e c')(*strict*)
        apply(rule_tac
      m = "nat"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
           apply(rename_tac nat d w1 w2 e c')(*strict*)
           apply(blast)
          apply(rename_tac nat d w1 w2 e c')(*strict*)
          apply(rule_tac
      s = "Suc nat"
      in ssubst)
           apply(rename_tac nat d w1 w2 e c')(*strict*)
           apply(arith)
          apply(rename_tac nat d w1 w2 e c')(*strict*)
          apply(blast)
         apply(rename_tac nat d w1 w2 e c')(*strict*)
         apply(blast)
        apply(rename_tac nat d w1 w2 e c')(*strict*)
        apply(rule impI)
        apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
         apply(rename_tac nat d w1 w2 e c')(*strict*)
         apply(clarsimp)
        apply(rename_tac nat d w1 w2 e c')(*strict*)
        apply(rule cfgSTD.reachesToAtMaxDom)
         apply(rename_tac nat d w1 w2 e c')(*strict*)
         apply(rule cfgSTD.from_to_is_to)
         apply(blast)
        apply(rename_tac nat d w1 w2 e c')(*strict*)
        apply(blast)
       apply(rename_tac nat d w1 w2 e c')(*strict*)
       apply(clarsimp)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(rule_tac
      x = "d1"
      in exI)
       apply(rule conjI)
        apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
        apply(blast)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> ) d2 (Suc 0)"
      in exI)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(rule conjI)
        apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
        apply(rule_tac
      dJ = "\<lparr>cfg_conf=c'\<rparr>"
      in cfgSTD.concatIsFromTo)
           apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
           apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation)
           apply(clarsimp)
           apply(rename_tac d w1 w2 e c' d1 d2 m1 m2 n v na nb va vb)(*strict*)
           apply(rule conjI)
            apply(rename_tac d w1 w2 e c' d1 d2 m1 m2 n v na nb va vb)(*strict*)
            apply(simp add: der2_def)
           apply(rename_tac d w1 w2 e c' d1 d2 m1 m2 n v na nb va vb)(*strict*)
           apply(simp add: der2_def)
           apply(force)
          apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
          apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation)
         apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
         apply(simp add: der2_maximum_of_domain)
        apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
        apply(force)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(rule_tac
      x = "m1"
      in exI)
       apply(rule conjI)
        apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
        apply(clarsimp)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(rule_tac
      x = "Suc m2"
      in exI)
       apply(clarsimp)
       apply(rule_tac
      s = "(Suc 0)+m2"
      in ssubst)
        apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
        apply(arith)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(rule_tac concat_has_max_dom)
        apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
        apply(rule der2_maximum_of_domain)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(blast)
      apply(rename_tac nat d w1 w2 e c)(*strict*)
      apply(rule alt_case)
       apply(rename_tac nat d w1 w2 e c)(*strict*)
       apply(blast)
      apply(rename_tac nat d w1 w2 e c)(*strict*)
      apply(blast)
     apply(rename_tac nat d w1 w2 e c)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat d w1 w2 e c')(*strict*)
     apply(erule_tac
      x = "c'"
      in allE)
     apply(erule_tac
      x = "w2"
      in allE)
     apply(erule impE)
      apply(rename_tac nat d w1 w2 e c')(*strict*)
      apply(rule_tac
      m = "nat"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
         apply(rename_tac nat d w1 w2 e c')(*strict*)
         apply(blast)
        apply(rename_tac nat d w1 w2 e c')(*strict*)
        apply(rule_tac
      s = "Suc nat"
      in ssubst)
         apply(rename_tac nat d w1 w2 e c')(*strict*)
         apply(arith)
        apply(rename_tac nat d w1 w2 e c')(*strict*)
        apply(blast)
       apply(rename_tac nat d w1 w2 e c')(*strict*)
       apply(blast)
      apply(rename_tac nat d w1 w2 e c')(*strict*)
      apply(rule impI)
      apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
       apply(rename_tac nat d w1 w2 e c')(*strict*)
       apply(clarsimp)
      apply(rename_tac nat d w1 w2 e c')(*strict*)
      apply(rule cfgSTD.reachesToAtMaxDom)
       apply(rename_tac nat d w1 w2 e c')(*strict*)
       apply(rule cfgSTD.from_to_is_to)
       apply(blast)
      apply(rename_tac nat d w1 w2 e c')(*strict*)
      apply(blast)
     apply(rename_tac nat d w1 w2 e c')(*strict*)
     apply(clarsimp)
     apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
     apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> ) d1 (Suc 0)"
      in exI)
     apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
     apply(rule conjI)
      apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
      prefer 2
      apply(rule_tac
      x = "d2"
      in exI)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(blast)
      apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
      prefer 2
      apply(rule_tac
      dJ = "\<lparr>cfg_conf=c'\<rparr>"
      in cfgSTD.concatIsFromTo)
         apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
         apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation)
         apply(clarsimp)
         apply(rename_tac d w1 w2 e c' d1 d2 m1 m2 n v na nb va vb)(*strict*)
         apply(rule conjI)
          apply(rename_tac d w1 w2 e c' d1 d2 m1 m2 n v na nb va vb)(*strict*)
          apply(simp add: der2_def)
         apply(rename_tac d w1 w2 e c' d1 d2 m1 m2 n v na nb va vb)(*strict*)
         apply(simp add: der2_def)
         apply(force)
        apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
        apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation)
       apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
       apply(rule der2_maximum_of_domain)
      apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
      apply(force)
     apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
     apply(rule_tac
      x = "Suc m1"
      in exI)
     apply(rule conjI)
      apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
      prefer 2
      apply(rule_tac
      x = "m2"
      in exI)
      apply(clarsimp)
     apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
     apply(rule_tac
      s = "(Suc 0)+m1"
      in ssubst)
      apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
      apply(arith)
     apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
     apply(rule_tac concat_has_max_dom)
      apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
      apply(rule der2_maximum_of_domain)
     apply(rename_tac d w1 w2 e c' d1 d2 m1 m2)(*strict*)
     apply(blast)
    apply(rename_tac nat d w1 w2 e c)(*strict*)
    apply(rule cfgSTD.position_change_due_to_step_relation)
      apply(rename_tac nat d w1 w2 e c)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)+
   apply(rename_tac nat d w1 w2)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac nat d w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat d w1 w2 e c)(*strict*)
    apply(case_tac c)
    apply(rename_tac nat d w1 w2 e c cfg_conf)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat d w1 w2)(*strict*)
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac nat d w1 w2)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)+
  apply(rename_tac nat d w1 w2)(*strict*)
  apply(rule cfgSTD.derivation_from_starts_from2)
  apply(rule cfgSTD.from_to_is_from)
  apply(blast)+
  done

lemma emptyDerOfEmpty: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> maximum_of_domain d 0
  \<Longrightarrow> w = []"
  apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
   defer
   apply(rule cfgSTD.fromAtZero)
    apply(blast)+
  apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
   defer
   apply(rule cfgSTD.toAtMaxDom)
    apply(blast)+
  apply(clarsimp)
  done

lemma canElimAll2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> d m = Some (pair xa \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> setB w = {}
  \<Longrightarrow> \<forall>i<length w. \<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [w ! i]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<and> (\<forall>k. maximum_of_domain d k \<longrightarrow> k < m \<or> k = m \<and> length w = 1)"
  apply(subgoal_tac "\<forall>w. \<forall>m d xa. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<longrightarrow> maximum_of_domain d m \<longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>) \<longrightarrow> d m = Some (pair xa \<lparr>cfg_conf = []\<rparr>) \<longrightarrow> setB w = {} \<longrightarrow> (\<forall>i<length w. \<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [w!i]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<and> (\<forall>k. maximum_of_domain d k \<longrightarrow> (k<m \<or> (k = m \<and> length w = 1))))")
   apply(blast)
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}")
  apply(thin_tac "maximum_of_domain d m")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
  apply(thin_tac "d m = Some (pair xa \<lparr>cfg_conf = []\<rparr>)")
  apply(thin_tac "setB w = {}")
  apply(rule allI)
  apply(rename_tac w)(*strict*)
  apply(rule_tac
      xs = "w"
      in length_induct)
  apply(rename_tac w xs)(*strict*)
  apply(auto)
  apply(rename_tac xs m d xa i)(*strict*)
  apply(case_tac xs)
   apply(rename_tac xs m d xa i)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs m d xa i a list)(*strict*)
  apply(case_tac a)
   apply(rename_tac xs m d xa i a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac m d xa i list aa)(*strict*)
   apply(rename_tac w A)
   apply(rename_tac m d xa i w A)(*strict*)
   defer
   apply(rename_tac xs m d xa i a list b)(*strict*)
   apply(clarsimp)
  apply(rename_tac m d xa i w A)(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 m1 m2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>} \<and> maximum_of_domain d1 m1 \<and> maximum_of_domain d2 m2 \<and> m1+m2 = m")
   apply(rename_tac m d xa i w A)(*strict*)
   prefer 2
   apply(rule empty_result_derivation_can_be_decomposed)
     apply(rename_tac m d xa i w A)(*strict*)
     apply(blast)
    apply(rename_tac m d xa i w A)(*strict*)
    apply(blast)
   apply(rename_tac m d xa i w A)(*strict*)
   apply(clarsimp)
  apply(rename_tac m d xa i w A)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa i w A d1 d2 m1 m2)(*strict*)
  apply(case_tac i)
   apply(rename_tac d xa i w A d1 d2 m1 m2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d xa w A d1 d2 m1 m2)(*strict*)
   apply(rule_tac
      x = "d1"
      in exI)
   apply(rule conjI)
    apply(rename_tac d xa w A d1 d2 m1 m2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d xa w A d1 d2 m1 m2)(*strict*)
   apply(rule allI)
   apply(rename_tac d xa w A d1 d2 m1 m2 k)(*strict*)
   apply(rule impI)
   apply(subgoal_tac "k = m1")
    apply(rename_tac d xa w A d1 d2 m1 m2 k)(*strict*)
    apply(case_tac m2)
     apply(rename_tac d xa w A d1 d2 m1 m2 k)(*strict*)
     apply(subgoal_tac "w = []")
      apply(rename_tac d xa w A d1 d2 m1 m2 k)(*strict*)
      apply(clarsimp)
     apply(rename_tac d xa w A d1 d2 m1 m2 k)(*strict*)
     apply(clarsimp)
     apply(rename_tac d xa w A d1 d2 m1)(*strict*)
     apply(rule emptyDerOfEmpty)
      apply(rename_tac d xa w A d1 d2 m1)(*strict*)
      apply(blast)
     apply(rename_tac d xa w A d1 d2 m1)(*strict*)
     apply(blast)
    apply(rename_tac d xa w A d1 d2 m1 m2 k nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac d xa w A d1 d2 m1 m2 k)(*strict*)
   apply(rule_tac
      d="d1"
      in cfgSTD.maximum_of_domainUnique)
     apply(rename_tac d xa w A d1 d2 m1 m2 k)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac d xa w A d1 d2 m1 m2 k)(*strict*)
    apply(blast, blast)
  apply(rename_tac d xa i w A d1 d2 m1 m2 nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
  apply(erule_tac
      x = "w"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x = "m2"
      in allE)
  apply(erule_tac
      x = "d2"
      in allE)
  apply(erule impE)
   apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
   apply(blast)
  apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
   apply(rule cfgSTD.fromAtZero)
    apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
    apply(blast)
   apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
   apply(blast)
  apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
  apply(erule impE)
   apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
   apply(rule cfgSTD.toAtMaxDom)
    apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
    apply(blast)
   apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
   apply(blast)
  apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
  apply(case_tac w)
   apply(rename_tac d xa w A d1 d2 m1 m2 nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d xa w A d1 d2 m1 m2 nat a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa A d1 d2 m1 m2 nat a list)(*strict*)
  apply(case_tac list)
   apply(rename_tac d xa A d1 d2 m1 m2 nat a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d xa A d1 d2 m1 m2 a da)(*strict*)
   apply(rule_tac
      x = "d2"
      in exI)
   apply(clarsimp)
   apply(rename_tac d xa A d1 d2 m1 m2 a da k)(*strict*)
   apply(subgoal_tac "m2 = k")
    apply(rename_tac d xa A d1 d2 m1 m2 a da k)(*strict*)
    apply(clarsimp)
    apply(rename_tac d xa A d1 d2 m1 a da k)(*strict*)
    apply(case_tac m1)
     apply(rename_tac d xa A d1 d2 m1 a da k)(*strict*)
     apply(clarsimp)
     apply(rename_tac d xa A d1 d2 a da k)(*strict*)
     apply(subgoal_tac "[teA A] = []")
      apply(rename_tac d xa A d1 d2 a da k)(*strict*)
      apply(clarsimp)
     apply(rename_tac d xa A d1 d2 a da k)(*strict*)
     apply(rule emptyDerOfEmpty)
      apply(rename_tac d xa A d1 d2 a da k)(*strict*)
      apply(blast)
     apply(rename_tac d xa A d1 d2 a da k)(*strict*)
     apply(blast)
    apply(rename_tac d xa A d1 d2 m1 a da k nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac d xa A d1 d2 m1 m2 a da k)(*strict*)
   apply(rule_tac
      d="d2"
      in cfgSTD.maximum_of_domainUnique)
     apply(rename_tac d xa A d1 d2 m1 m2 a da k)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac d xa A d1 d2 m1 m2 a da k)(*strict*)
    apply(blast)
   apply(rename_tac d xa A d1 d2 m1 m2 a da k)(*strict*)
   apply(blast)
  apply(rename_tac d xa A d1 d2 m1 m2 nat a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac d xa A d1 d2 m1 m2 nat a aa lista)(*strict*)
  apply(rename_tac i A B w)
  apply(rename_tac d xa Aa d1 d2 m1 m2 i A B w)(*strict*)
  apply(erule_tac
      x = "i"
      in allE)
  apply(erule impE)
   apply(rename_tac d xa Aa d1 d2 m1 m2 i A B w)(*strict*)
   apply(clarsimp)
  apply(rename_tac d xa Aa d1 d2 m1 m2 i A B w)(*strict*)
  apply(erule exE, erule conjE)
  apply(rename_tac d xa Aa d1 d2 m1 m2 i A B w da)(*strict*)
  apply(rule_tac
      x = "da"
      in exI)
  apply(rule conjI, clarsimp)
  apply(clarsimp)
  apply(rename_tac d xa Aa d1 d2 m1 m2 i A B w da k)(*strict*)
  apply(erule_tac
      x = "k"
      in allE)
  apply(clarsimp)
  done

lemma canElimAll: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> d m = Some (pair xa \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> setB w = {} \<and> (\<forall>i<length w. \<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [w ! i]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<and> (\<forall>k. maximum_of_domain d k \<longrightarrow> k < m \<or> k = m \<and> length w = 1))"
  apply(subgoal_tac "setB w = {}")
   apply(rule conjI, simp)
   apply(rule canElimAll2)
        apply(blast)+
  apply(rule canElimAll1)
     apply(blast)+
  done

definition DeriveX2 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "DeriveX2 G w1 w2 v1 x v2 n \<equiv>
  \<exists>d1 d2 n1 n2 l1 l2.
    cfgSTD.derivation_from_to G d1
        {pair None \<lparr>cfg_conf = w1\<rparr>}
        {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = l1\<rparr>}
    \<and> cfgSTD.derivation_from_to G d2
          {pair None \<lparr>cfg_conf = w2\<rparr>}
          {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = l2 @ [x] @ v2\<rparr>}
    \<and> maximum_of_domain d1 n1
    \<and> maximum_of_domain d2 n2
    \<and> n1 + n2 = n
    \<and> l1 @ l2 = v1"

definition DeriveX1 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "DeriveX1 G w1 w2 v1 x v2 n \<equiv>
  \<exists>d1 d2 n1 n2 l1 l2.
    cfgSTD.derivation_from_to G d1
        {pair None \<lparr>cfg_conf = w1\<rparr>}
        {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = v1 @ [x] @ l1\<rparr>}
    \<and> cfgSTD.derivation_from_to G d2
          {pair None \<lparr>cfg_conf = w2\<rparr>}
          {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = l2\<rparr>}
    \<and> maximum_of_domain d1 n1
    \<and> maximum_of_domain d2 n2
    \<and> n1 + n2 = n
    \<and> l1 @ l2 = v2"

lemma cfg_derivation_is_concurrent: "
  cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = v1 @ [x] @ v2\<rparr>}
  \<Longrightarrow> maximum_of_domain d1 n
  \<Longrightarrow> (DeriveX1 G w1 w2 v1 x v2 n) \<or> (DeriveX2 G w1 w2 v1 x v2 n)"
  apply(subgoal_tac " \<forall>i d w1 w2 v1 x v2. maximum_of_domain d i \<and> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = v1 @ [x] @ v2\<rparr>} \<longrightarrow> ((DeriveX1 G w1 w2 v1 x v2 i) \<or> (DeriveX2 G w1 w2 v1 x v2 i))")
   apply(blast)
  apply(thin_tac "cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = v1 @ [x] @ v2\<rparr>}")
  apply(thin_tac "maximum_of_domain d1 n")
  apply(rule allI)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      n = "i"
      in nat_induct)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2 v1 x v2)(*strict*)
   apply(subgoal_tac "w1 @ w2 = v1 @ [x] @ v2")
    apply(rename_tac d w1 w2 v1 x v2)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w1 w2 v1 x v2)(*strict*)
    apply(subgoal_tac "prefix w1 v1 \<or> prefix v1 w1")
     apply(rename_tac d w1 w2 v1 x v2)(*strict*)
     prefer 2
     apply(rule mutual_prefix_prefix)
     apply(blast)
    apply(rename_tac d w1 w2 v1 x v2)(*strict*)
    apply(erule disjE)
     apply(rename_tac d w1 w2 v1 x v2)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac d w1 x v2 c)(*strict*)
     apply(simp add: DeriveX2_def)
     apply(erule_tac
      x = "der1 \<lparr>cfg_conf = w1\<rparr>"
      in allE)
     apply(erule_tac
      x = "der1 \<lparr>cfg_conf = c @ x#v2\<rparr>"
      in allE)
     apply(erule_tac
      x = "0"
      in allE)
     apply(erule_tac
      x = "0"
      in allE)
     apply(simp add: der1_maximum_of_domain)
     apply(erule_tac
      x = "w1"
      in allE)
     apply(erule impE)
      apply(rename_tac d w1 x v2 c)(*strict*)
      apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
      apply(clarsimp)
      apply(rename_tac d w1 x v2 c n xa)(*strict*)
      apply(simp add: cfgSTD.der1_is_derivation)
      apply(simp add: der1_def)
     apply(rename_tac d w1 x v2 c)(*strict*)
     apply(erule_tac
      x = "c"
      in allE)
     apply(erule impE)
      apply(rename_tac d w1 x v2 c)(*strict*)
      apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
      apply(clarsimp)
      apply(rename_tac d w1 x v2 c n xa)(*strict*)
      apply(simp add: cfgSTD.der1_is_derivation)
      apply(simp add: der1_def)
     apply(rename_tac d w1 x v2 c)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w1 w2 v1 x v2)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac d w2 v1 x v2 c)(*strict*)
    apply(case_tac c)
     apply(rename_tac d w2 v1 x v2 c)(*strict*)
     apply(clarsimp)
     apply(rename_tac d v1 x v2)(*strict*)
     apply(simp add: DeriveX2_def)
     apply(erule_tac
      x = "der1 \<lparr>cfg_conf = v1\<rparr>"
      in allE)
     apply(erule_tac
      x = "der1 \<lparr>cfg_conf = x#v2\<rparr>"
      in allE)
     apply(erule_tac
      x = "0"
      in allE)
     apply(erule_tac
      x = "0"
      in allE)
     apply(simp add: der1_maximum_of_domain)
     apply(erule_tac
      x = "v1"
      in allE)
     apply(erule impE)
      apply(rename_tac d v1 x v2)(*strict*)
      apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
      apply(clarsimp)
      apply(rename_tac d v1 x v2 n xa)(*strict*)
      apply(simp add: cfgSTD.der1_is_derivation)
      apply(simp add: der1_def)
     apply(rename_tac d v1 x v2)(*strict*)
     apply(erule_tac
      x = "[]"
      in allE)
     apply(erule impE)
      apply(rename_tac d v1 x v2)(*strict*)
      apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
      apply(clarsimp)
      apply(rename_tac d v1 x v2 n xa)(*strict*)
      apply(simp add: cfgSTD.der1_is_derivation)
      apply(simp add: der1_def)
     apply(rename_tac d v1 x v2)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w2 v1 x v2 c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w2 v1 x list)(*strict*)
    apply(simp add: DeriveX1_def)
    apply(rule_tac
      x = "der1 \<lparr>cfg_conf = v1 @ x#list\<rparr>"
      in exI)
    apply(rule_tac
      x = "der1 \<lparr>cfg_conf = w2\<rparr>"
      in exI)
    apply(rule_tac
      x = "0"
      in exI)
    apply(rule_tac
      x = "0"
      in exI)
    apply(rule_tac
      x = "list"
      in exI)
    apply(rule conjI)
     apply(rename_tac d w2 v1 x list)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
     apply(clarsimp)
     apply(rename_tac d w2 v1 x list n xa)(*strict*)
     apply(simp add: cfgSTD.der1_is_derivation)
     apply(simp add: der1_def)
    apply(rename_tac d w2 v1 x list)(*strict*)
    apply(rule_tac
      x = "w2"
      in exI)
    apply(rule conjI)
     apply(rename_tac d w2 v1 x list)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
     apply(clarsimp)
     apply(rename_tac d w2 v1 x list n xa)(*strict*)
     apply(simp add: cfgSTD.der1_is_derivation)
     apply(simp add: der1_def)
    apply(rename_tac d w2 v1 x list)(*strict*)
    apply(simp add: der1_maximum_of_domain)
   apply(rename_tac d w1 w2 v1 x v2)(*strict*)
   apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w1 @ w2\<rparr>)")
    apply(rename_tac d w1 w2 v1 x v2)(*strict*)
    prefer 2
    apply(rule cfgSTD.derivation_from_starts_from2)
    apply(rule cfgSTD.from_to_is_from)
    apply(blast)+
   apply(rename_tac d w1 w2 v1 x v2)(*strict*)
   apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = v1 @ [x] @ v2\<rparr>)")
    apply(rename_tac d w1 w2 v1 x v2)(*strict*)
    prefer 2
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac d w1 w2 v1 x v2)(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(clarsimp)
     apply(blast)+
   apply(rename_tac d w1 w2 v1 x v2)(*strict*)
   apply(force)
  apply(rename_tac i n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
  apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w1 @ w2\<rparr>)")
   apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_from_starts_from2)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
  apply(subgoal_tac "\<exists>A w ds0. d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) \<lparr>cfg_conf = ds0\<rparr>)")
   apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
    prefer 2
    apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
     apply(blast)
    apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
    apply(arith)
   apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d w1 w2 v1 x v2 e c)(*strict*)
   apply(case_tac e)
   apply(rename_tac n d w1 w2 v1 x v2 e c prod_lhs prod_rhs)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d w1 w2 v1 x v2 c prod_lhs prod_rhs)(*strict*)
   apply(case_tac c)
   apply(rename_tac n d w1 w2 v1 x v2 c prod_lhs prod_rhs cfg_conf)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d w1 w2 v1 x v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w1 @ w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = ds0\<rparr>")
   apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
   prefer 2
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
   apply(clarsimp)
   apply(rename_tac n d w1 w2 v1 x v2 A w ds0 na xa)(*strict*)
   apply(erule_tac
      x = "Suc 0"
      in allE)
   apply(clarsimp)
  apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
  apply(subgoal_tac " (\<exists>w11 w12. w1 = w11 @ [teA A] @ w12 \<and> ds0 = w11 @ w @ w12 @ w2) \<or> (\<exists>w21 w22. w2 = w21 @ [teA A] @ w22 \<and> ds0 = w1 @ w21 @ w @ w22) ")
   apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
   prefer 2
   apply(simp add: cfgSTD_step_relation_def)
   apply(erule conjE)
   apply(clarsimp)
   apply(rename_tac n d w1 w2 v1 x v2 A w l r)(*strict*)
   apply(subgoal_tac "prefix w1 l \<or> prefix l w1")
    apply(rename_tac n d w1 w2 v1 x v2 A w l r)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(blast)
   apply(rename_tac n d w1 w2 v1 x v2 A w l r)(*strict*)
   apply(erule disjE)
    apply(rename_tac n d w1 w2 v1 x v2 A w l r)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac n d w1 v1 x v2 A w r c)(*strict*)
    apply(subgoal_tac "False", blast)
    apply(erule_tac
      x = "c"
      in allE)
    apply(erule_tac
      x = "r"
      in allE)
    apply(clarsimp)
   apply(rename_tac n d w1 w2 v1 x v2 A w l r)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n d w2 v1 x v2 A w l r c)(*strict*)
   apply(case_tac c)
    apply(rename_tac n d w2 v1 x v2 A w l r c)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d v1 x v2 A w l r)(*strict*)
    apply(subgoal_tac "False", blast)
    apply(erule_tac
      x = "[]"
      in allE)
    apply(erule_tac
      x = "r"
      in allE)
    apply(clarsimp)
   apply(rename_tac n d w2 v1 x v2 A w l r c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d w2 v1 x v2 A w l list)(*strict*)
   apply(rule_tac
      x = "l"
      in exI)
   apply(rule_tac
      x = "list"
      in exI)
   apply(clarsimp)
  apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
  apply(subgoal_tac "\<exists>d12. cfgSTD.derivation_from_to G d12 {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = ds0\<rparr>} \<and> maximum_of_domain d12 (Suc 0)")
   apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
   prefer 2
   apply(rule_tac
      x = "der2 \<lparr>cfg_conf = w1@w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = ds0\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
    apply(rule context_conjI)
     apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
     apply(rule cfgSTD.der2_is_derivation)
     apply(simp add: cfgSTD_step_relation_def)
    apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
    apply(erule disjE)
     apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d w2 v1 x v2 A w w11 w12 na xa)(*strict*)
     apply(simp add: der2_def)
     apply(rule_tac
      x="Suc 0"
      in exI)
     apply(force)
    apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
    apply(simp add: der2_maximum_of_domain)
    apply(simp add: der2_def)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(force)
   apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
   apply(simp add: der2_maximum_of_domain)
  apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
  apply(subgoal_tac " (\<forall>w11 w12. w1 = w11 @ [teA A] @ w12 \<and> ds0 = w11 @ w @ w12 @ w2 \<longrightarrow> (\<exists>d12R. cfgSTD.derivation_from_to G d12R {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w11 @ w @ w12\<rparr>} \<and> maximum_of_domain d12R (Suc 0))) \<and> (\<forall>w21 w22. w2 = w21 @ [teA A] @ w22 \<and> ds0 = w1 @ w21 @ w @ w22 \<longrightarrow> (\<exists>d12R. cfgSTD.derivation_from_to G d12R {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w21 @ w @ w22\<rparr>} \<and> maximum_of_domain d12R (Suc 0)))")
   apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
    apply(erule disjE)
     apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 w11a w12a)(*strict*)
     apply(rule_tac
      x = "der2 \<lparr>cfg_conf = w11a @ teA A # w12a\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w11a @ w @ w12a\<rparr>"
      in exI)
     apply(rule conjI)
      apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 w11a w12a)(*strict*)
      apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
      apply(rule context_conjI)
       apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 w11a w12a)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(simp add: cfgSTD_step_relation_def)
       apply(force)
      apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 w11a w12a)(*strict*)
      apply(clarsimp)
      apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 w11a w12a na xa nb xaa)(*strict*)
      apply(simp add: der2_def)
      apply(rule_tac
      x="Suc 0"
      in exI)
      apply(force)
     apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 w11a w12a)(*strict*)
     apply(simp add: der2_maximum_of_domain)
    apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d v1 x v2 A w d12 w21 w22 w11 w12)(*strict*)
    apply(rule_tac
      x = "der2 \<lparr>cfg_conf = w11 @ teA A # w12\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w11 @ w @ w12\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac n d v1 x v2 A w d12 w21 w22 w11 w12)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
     apply(rule context_conjI)
      apply(rename_tac n d v1 x v2 A w d12 w21 w22 w11 w12)(*strict*)
      apply(rule cfgSTD.der2_is_derivation)
      apply(simp add: cfgSTD_step_relation_def)
      apply(force)
     apply(rename_tac n d v1 x v2 A w d12 w21 w22 w11 w12)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d v1 x v2 A w d12 w21 w22 w11 w12 na xa nb xaa)(*strict*)
     apply(simp add: der2_def)
     apply(rule_tac
      x="Suc 0"
      in exI)
     apply(force)
    apply(rename_tac n d v1 x v2 A w d12 w21 w22 w11 w12)(*strict*)
    apply(simp add: der2_maximum_of_domain)
   apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22)(*strict*)
   apply(rule_tac
      x = "der2 \<lparr>cfg_conf = w21 @ teA A # w22\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w21 @ w @ w22\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
    apply(rule context_conjI)
     apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22)(*strict*)
     apply(rule cfgSTD.der2_is_derivation)
     apply(simp add: cfgSTD_step_relation_def)
     apply(force)
    apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 na xa nb xaa)(*strict*)
    apply(simp add: der2_def)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(force)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22)(*strict*)
   apply(simp add: der2_maximum_of_domain)
  apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
  apply(erule disjE)
   apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
   apply(erule conjE)
   apply(clarsimp)
   apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12)(*strict*)
   apply(thin_tac "\<forall>w21 w22. w2 = w21 @ teA A # w22 \<and> w @ w12 @ w2 = teA A # w12 @ w21 @ w @ w22 \<longrightarrow> (\<exists>d12R. cfgSTD.derivation_from_to G d12R {pair None \<lparr>cfg_conf = w21 @ teA A # w22\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w21 @ w @ w22\<rparr>}\<and> maximum_of_domain d12R (Suc 0))")
   apply(erule_tac
      x = "w11"
      in allE)
   apply(erule_tac
      x = "w12"
      in allE)
   apply(clarsimp)
   apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
   apply(erule_tac
      x = "derivation_drop d (Suc 0)"
      in allE)
   apply(erule_tac
      x = "w11 @ w @ w12"
      in allE)
   apply(erule_tac
      x = "w2"
      in allE)
   apply(erule_tac
      x = "v1"
      in allE)
   apply(erule_tac
      x = "x"
      in allE)
   apply(erule_tac
      x = "v2"
      in allE)
   apply(erule impE)
    apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
    apply(rule conjI)
     apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
     apply(rule derivation_drop_preserves_generates_maximum_of_domain)
     apply(blast)
    apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
    apply(rule_tac
      m = "n"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
       apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
       apply(blast)
      apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
      apply(rule_tac
      s = "Suc n"
      in ssubst)
       apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
       apply(arith)
      apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
      apply(blast)
     apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
     apply(clarsimp)
     apply(blast)
    apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
    apply(rule impI)
    apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
    apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = v1 @ [x] @ v2\<rparr>)")
     apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
     apply(clarsimp)
    apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(clarsimp)
     apply(rename_tac d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
     apply(force)
    apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
    apply(blast)
   apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
   apply(erule disjE)
    apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
    apply(thin_tac "\<not> DeriveX2 G (w11 @ teA A # w12) w2 v1 x v2 (Suc n)")
    apply(simp add: DeriveX1_def)
    apply(clarsimp)
    apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(rule_tac
      x = "derivation_append d12R d1 (Suc 0)"
      in exI)
    apply(rule_tac
      x = "d2"
      in exI)
    apply(rule_tac
      x = "(Suc 0)+n1"
      in exI)
    apply(rule_tac
      x = "n2"
      in exI)
    apply(rule_tac
      x = "l1"
      in exI)
    apply(rule conjI)
     apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(rule_tac
      dJ = "\<lparr>cfg_conf=w11 @ w @ w12\<rparr>"
      in cfgSTD.concatIsFromTo)
        apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
        apply(blast)
       apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
       apply(blast)
      apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
      apply(blast)
     apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(blast)
    apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(rule_tac
      x = "l2"
      in exI)
    apply(rule conjI)
     apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(blast)
    apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(rule_tac concat_has_max_dom)
      apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
      apply(blast)
     apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(blast)
    apply(rename_tac d w2 v1 x A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d w2 v1 x v2 A w d12 w11 w12 d12R)(*strict*)
   apply(subgoal_tac "DeriveX2 G (w11 @ teA A # w12) w2 v1 x v2 (Suc n)", blast)
   apply(thin_tac "\<not> DeriveX2 G (w11 @ teA A # w12) w2 v1 x v2 (Suc n)")
   apply(simp add: DeriveX2_def)
   apply(clarsimp)
   apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule_tac
      x = "derivation_append d12R d1 (Suc 0)"
      in exI)
   apply(rule_tac
      x = "d2"
      in exI)
   apply(rule_tac
      x = "(Suc 0)+n1"
      in exI)
   apply(rule_tac
      x = "n2"
      in exI)
   apply(rule_tac
      x = "l1"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(rule_tac
      dJ = "\<lparr>cfg_conf=w11 @ w @ w12\<rparr>"
      in cfgSTD.concatIsFromTo)
       apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
       apply(blast)
      apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
      apply(blast)
     apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(blast)
    apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule_tac
      x = "l2"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(rule_tac concat_has_max_dom)
     apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(blast)
    apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w2 x v2 A w d12 w11 w12 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d w1 w2 v1 x v2 A w ds0)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22)(*strict*)
  apply(thin_tac " \<forall>w11 w12. w1 = w11 @ teA A # w12 \<and> w1 @ w21 @ w = w11 @ w @ w12 @ w21 @ [teA A] \<longrightarrow> (\<exists>d12R. cfgSTD.derivation_from_to G d12R {pair None \<lparr>cfg_conf = w11 @ teA A # w12\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w11 @ w @ w12\<rparr>} \<and> maximum_of_domain d12R (Suc 0))")
  apply(erule_tac
      x = "w21"
      in allE)
  apply(erule_tac
      x = "w22"
      in allE)
  apply(clarsimp)
  apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
  apply(erule_tac
      x = "derivation_drop d (Suc 0)"
      in allE)
  apply(erule_tac
      x = "w1"
      in allE)
  apply(erule_tac
      x = "w21 @ w @ w22"
      in allE)
  apply(erule_tac
      x = "v1"
      in allE)
  apply(erule_tac
      x = "x"
      in allE)
  apply(erule_tac
      x = "v2"
      in allE)
  apply(erule impE)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
   apply(rule conjI)
    apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
    apply(rule derivation_drop_preserves_generates_maximum_of_domain)
    apply(blast)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
   apply(rule_tac
      m = "n"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
      apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
      apply(blast)
     apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
     apply(rule_tac
      s = "Suc n"
      in ssubst)
      apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
      apply(arith)
     apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
     apply(blast)
    apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
    apply(clarsimp)
    apply(blast)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
   apply(rule impI)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
   apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = v1 @ [x] @ v2\<rparr>)")
    apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
    apply(rule cfgSTD.from_to_is_to)
    apply(clarsimp)
    apply(rename_tac d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
    apply(force)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
   apply(blast)
  apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
  apply(erule disjE)
   apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
   apply(thin_tac "\<not> DeriveX2 G w1 (w21 @ teA A # w22) v1 x v2 (Suc n)")
   apply(simp add: DeriveX1_def)
   apply(clarsimp)
   apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule_tac
      x = "d1"
      in exI)
   apply(rule_tac
      x = "derivation_append d12R d2 (Suc 0)"
      in exI)
   apply(rule_tac
      x = "n1"
      in exI)
   apply(rule_tac
      x = "(Suc 0)+n2"
      in exI)
   apply(rule_tac
      x = "l1"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule_tac
      x = "l2"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(rule_tac
      dJ = "\<lparr>cfg_conf=w21 @ w @ w22\<rparr>"
      in cfgSTD.concatIsFromTo)
       apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
       apply(blast)
      apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
      apply(blast)
     apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(blast)
    apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(rule_tac concat_has_max_dom)
     apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(blast)
    apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w1 v1 x A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d w1 v1 x v2 A w d12 w21 w22 d12R)(*strict*)
  apply(subgoal_tac "DeriveX2 G w1 (w21 @ teA A # w22) v1 x v2 (Suc n)", blast)
  apply(thin_tac "\<not> DeriveX2 G w1 (w21 @ teA A # w22) v1 x v2 (Suc n)")
  apply(simp add: DeriveX2_def)
  apply(clarsimp)
  apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
  apply(rule_tac
      x = "d1"
      in exI)
  apply(rule_tac
      x = "derivation_append d12R d2 (Suc 0)"
      in exI)
  apply(rule_tac
      x = "n1"
      in exI)
  apply(rule_tac
      x = "(Suc 0)+n2"
      in exI)
  apply(rule_tac
      x = "l1"
      in exI)
  apply(rule conjI)
   apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(blast)
  apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
  apply(rule_tac
      x = "l2"
      in exI)
  apply(rule conjI)
   apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule_tac
      dJ = "\<lparr>cfg_conf=w21 @ w @ w22\<rparr>"
      in cfgSTD.concatIsFromTo)
      apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
      apply(blast)
     apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
     apply(blast)
    apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(blast)
  apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(blast)
  apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
    apply(blast)
   apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
   apply(blast)
  apply(rename_tac d w1 x v2 A w d12 w21 w22 d12R d1 d2 n1 n2 l1 l2)(*strict*)
  apply(clarsimp)
  done

lemma twoCasesOfDerivations: "
  maximum_of_domain d n
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = y # w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w4\<rparr>}
  \<Longrightarrow> (\<exists>d w''. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [y]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w''\<rparr>} \<and> (\<forall>k. maximum_of_domain d k \<longrightarrow> k \<le> n)) \<or> (\<exists>d1 d2 k1 k2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = [y]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<and> maximum_of_domain d1 (Suc k1) \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w4\<rparr>} \<and> maximum_of_domain d2 k2 \<and> Suc k1 + k2 = n)"
  apply(subgoal_tac "(DeriveX1 G [y] w3 [] (teB x) w4 n) \<or> (DeriveX2 G [y] w3 [] (teB x) w4 n)")
   defer
   apply(rule cfg_derivation_is_concurrent)
    apply(clarsimp)
    apply(blast)
   apply(blast)
  apply(erule disjE)
   apply(rule disjI1)
   defer
   apply(rule disjI2)
   defer
   apply(simp add: DeriveX1_def)
   apply(auto)
   apply(rename_tac d1 d2 n1 n2 l1 l2)(*strict*)
   apply(rule_tac
      x = "d1"
      in exI)
   apply(auto)
   apply(rename_tac d1 d2 n1 n2 l1 l2 k)(*strict*)
   apply(subgoal_tac "k = n1")
    apply(rename_tac d1 d2 n1 n2 l1 l2 k)(*strict*)
    apply(auto)
   apply(rename_tac d1 d2 n1 n2 l1 l2 k)(*strict*)
   apply(rule_tac
      d="d1"
      in cfgSTD.maximum_of_domainUnique)
     apply(rename_tac d1 d2 n1 n2 l1 l2 k)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac d1 d2 n1 n2 l1 l2 k)(*strict*)
    apply(blast)
   apply(rename_tac d1 d2 n1 n2 l1 l2 k)(*strict*)
   apply(blast)
  apply(simp add: DeriveX2_def)
  apply(auto)
  apply(rename_tac d1 d2 n1 n2)(*strict*)
  apply(rule_tac
      x = "d1"
      in exI)
  apply(auto)
  apply(rule_tac
      x = "d2"
      in exI)
  apply(auto)
  apply(subgoal_tac "\<exists>n1s. Suc n1s = n1")
   apply(rename_tac d1 d2 n1 n2)(*strict*)
   apply(clarsimp)
   apply(rename_tac d1 d2 n2 n1s)(*strict*)
   apply(rule_tac
      x = "n1s"
      in exI)
   apply(rule conjI, blast)
   apply(rule_tac
      x = "n2"
      in exI)
   apply(rule conjI, blast)
   apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2)(*strict*)
  apply(subgoal_tac "n1\<noteq>0")
   apply(rename_tac d1 d2 n1 n2)(*strict*)
   apply(case_tac n1)
    apply(rename_tac d1 d2 n1 n2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d1 d2 n1 n2 nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2)(*strict*)
  apply(rule_tac
      ?c1.0 = "\<lparr>cfg_conf = [y]\<rparr>"
      in cfgSTD.modifying_derivation_is_not_empty)
    apply(rename_tac d1 d2 n1 n2)(*strict*)
    apply(blast)
   apply(rename_tac d1 d2 n1 n2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d1 d2 n1 n2)(*strict*)
  apply(blast)
  done

lemma derivationCanBeDecomposed: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1@w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}
  \<Longrightarrow> \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w'"
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   apply(erule exE)+
   apply(rename_tac n)(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac n)(*strict*)
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2 w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>} \<and> maximum_of_domain d n \<longrightarrow> (\<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w')")
   apply(rename_tac n)(*strict*)
   apply(blast)
  apply(rename_tac n)(*strict*)
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}")
  apply(rename_tac n)(*strict*)
  apply(thin_tac "maximum_of_domain d n")
  apply(rule allI)
  apply(rename_tac n na)(*strict*)
  apply(induct_tac na)
   apply(rename_tac n na)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2 w')(*strict*)
   apply(case_tac "w1@w2\<noteq>w'")
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(subgoal_tac "0\<noteq>(0::nat)")
     apply(rename_tac d w1 w2 w')(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(rule cfgSTD.modifying_derivation_is_not_empty)
      apply(rename_tac d w1 w2 w')(*strict*)
      apply(blast)
     apply(rename_tac d w1 w2 w')(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2 w')(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = w1\<rparr>"
      in exI)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = w2\<rparr>"
      in exI)
   apply(rule_tac
      x="w1"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
    apply(simp add: cfgSTD.der1_is_derivation)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="w2"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
    apply(simp add: cfgSTD.der1_is_derivation)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2)(*strict*)
   apply(force)
  apply(rename_tac n na nb)(*strict*)
  apply(clarsimp)
  apply(rename_tac nb d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1@w2\<rparr>}. d 0 = Some x")
   apply(rename_tac nb d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac nb d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac nb d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac nb d w1 w2 w')(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac nb d w1 w2 w')(*strict*)
    apply(blast)
   apply(rename_tac nb d w1 w2 w')(*strict*)
   apply(arith)
  apply(rename_tac nb d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e. d (Suc nb) = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac nb d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rename_tac nb d w1 w2 w')(*strict*)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac nb d w1 w2 w')(*strict*)
   apply(clarsimp)
  apply(rename_tac nb d w1 w2 w')(*strict*)
  apply(clarsimp)
  apply(rename_tac nb d w1 w2 w' e ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac nb d w1 w2 w' e ea c cfg_conf)(*strict*)
  apply(rename_tac cv)
  apply(rename_tac nb d w1 w2 w' e ea c cv)(*strict*)
  apply(erule_tac
      x="derivation_drop d (Suc 0)"
      in allE)
  apply(case_tac "\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv")
   apply(rename_tac nb d w1 w2 w' e ea c cv)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = cv")
    apply(rename_tac nb d w1 w2 w' e ea c cv)(*strict*)
    prefer 2
    apply(rule alt_case)
     apply(rename_tac nb d w1 w2 w' e ea c cv)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_def)
     apply(clarsimp)
     apply(rename_tac nb d w1 w2 w' e ea cv)(*strict*)
     apply(erule_tac
      x="Suc 0"
      in allE)
     apply(clarsimp)
    apply(rename_tac nb d w1 w2 w' e ea c cv)(*strict*)
    apply(force)
   apply(rename_tac nb d w1 w2 w' e ea c cv)(*strict*)
   apply(thin_tac "\<not> (\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv)")
   apply(clarsimp)
   apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
   apply(erule_tac
      x="w1"
      in allE)
   apply(erule_tac
      x="c'"
      in allE)
   apply(erule_tac
      x="w'"
      in allE)
   apply(erule impE)
    apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
    apply(rule conjI)
     apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
     apply(rule_tac
      m = "nb"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
        apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
        apply(blast)
       apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
       apply(rule_tac
      s = "Suc nb"
      in ssubst)
        apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
        apply(arith)
       apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
       apply(blast)
      apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
      apply(blast)
     apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
     apply(clarsimp)
    apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
    apply(rule derivation_drop_preserves_generates_maximum_of_domain)
    apply(blast)
   apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
   apply(clarsimp)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
   apply(subgoal_tac "\<exists>n1. maximum_of_domain d1 n1")
    apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
    prefer 2
    apply(rule cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
   apply(subgoal_tac "\<exists>n2. maximum_of_domain d2 n2")
    apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
    prefer 2
    apply(rule cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
   apply(clarsimp)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="d1"
      in exI)
   apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> ) d2 (Suc 0)"
      in exI)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="w1'"
      in exI)
   apply(rule conjI)
    apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="w2'"
      in exI)
   apply(rule conjI)
    apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(rule_tac
      dJ = "\<lparr>cfg_conf=c'\<rparr>"
      in cfgSTD.concatIsFromTo)
       apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
       apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
       apply(simp add: cfgSTD.der2_is_derivation)
       apply(simp add: der2_def)
       apply(rule_tac
      x="Suc 0"
      in exI)
       apply(force)
      apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
      apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
     apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(force)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(force)
  apply(rename_tac nb d w1 w2 w' e ea c cv)(*strict*)
  apply(clarsimp)
  apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
  apply(erule_tac
      x="c'"
      in allE)
  apply(erule_tac
      x="w2"
      in allE)
  apply(erule_tac
      x="w'"
      in allE)
  apply(erule impE)
   apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
   apply(rule conjI)
    apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
    apply(rule_tac
      m = "nb"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
       apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
       apply(blast)
      apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
      apply(rule_tac
      s = "Suc nb"
      in ssubst)
       apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
       apply(arith)
      apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
      apply(blast)
     apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
     apply(blast)
    apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
    apply(clarsimp)
   apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
   apply(rule derivation_drop_preserves_generates_maximum_of_domain)
   apply(blast)
  apply(rename_tac nb d w1 w2 w' e ea c')(*strict*)
  apply(clarsimp)
  apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
  apply(subgoal_tac "\<exists>n1. maximum_of_domain d1 n1")
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
  apply(subgoal_tac "\<exists>n2. maximum_of_domain d2 n2")
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2')(*strict*)
  apply(clarsimp)
  apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> ) d1 (Suc 0)"
      in exI)
  apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(rule_tac
      x="w1'"
      in exI)
  apply(rule conjI)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      dJ = "\<lparr>cfg_conf=c'\<rparr>"
      in cfgSTD.concatIsFromTo)
      apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
      apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
      apply(simp add: cfgSTD.der2_is_derivation)
      apply(simp add: der2_def)
      apply(rule_tac
      x="Suc 0"
      in exI)
      apply(force)
     apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def)
    apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(force)
  apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule_tac
      x="w2'"
      in exI)
  apply(rule conjI)
   apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(force)
  apply(rename_tac nb d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(force)
  done

lemma derivationCanBeDecomposed2: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1@w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> \<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n"
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2 w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>} \<and> maximum_of_domain d n \<longrightarrow> (\<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n)")
   apply(blast)
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}")
  apply(thin_tac "maximum_of_domain d n")
  apply(rule allI)
  apply(rename_tac n)(*strict*)
  apply(induct_tac n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2 w')(*strict*)
   apply(case_tac "w1@w2\<noteq>w'")
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(subgoal_tac "0\<noteq>(0::nat)")
     apply(rename_tac d w1 w2 w')(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(rule cfgSTD.modifying_derivation_is_not_empty)
      apply(rename_tac d w1 w2 w')(*strict*)
      apply(blast)
     apply(rename_tac d w1 w2 w')(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2 w')(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = w1\<rparr>"
      in exI)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = w2\<rparr>"
      in exI)
   apply(rule_tac
      x="w1"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2)(*strict*)
    apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)
    apply(simp add: der1_def der2_def)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="w2"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2)(*strict*)
    apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)
    apply(simp add: der1_def der2_def)
   apply(rename_tac d w1 w2)(*strict*)
   apply(clarsimp)
   apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)
  apply(rename_tac n na)(*strict*)
  apply(simp add: der1_def der2_def)
  apply(rename_tac na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1@w2\<rparr>}. d 0 = Some x")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac na d w1 w2 w')(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2 w')(*strict*)
   apply(arith)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e. d (Suc na) = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac na d w1 w2 w')(*strict*)
   apply(clarsimp)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 w' e ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac na d w1 w2 w' e ea c cfg_conf)(*strict*)
  apply(rename_tac cv)
  apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
  apply(erule_tac
      x="derivation_drop d (Suc 0)"
      in allE)
  apply(case_tac "\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv")
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = cv")
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    prefer 2
    apply(rule alt_case)
     apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_def)
     apply(clarsimp)
     apply(rename_tac na d w1 w2 w' e ea cv)(*strict*)
     apply(erule_tac
      x="Suc 0"
      in allE)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   apply(thin_tac "\<not> (\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv)")
   apply(clarsimp)
   apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
   apply(erule_tac
      x="w1"
      in allE)
   apply(erule_tac
      x="c'"
      in allE)
   apply(erule_tac
      x="w'"
      in allE)
   apply(erule impE)
    apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
    apply(rule conjI)
     apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
     apply(rule_tac
      m = "na"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
        apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
        apply(blast)
       apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
       apply(rule_tac
      s = "Suc na"
      in ssubst)
        apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
        apply(arith)
       apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
       apply(blast)
      apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
      apply(blast)
     apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
    apply(rule derivation_drop_preserves_generates_maximum_of_domain)
    apply(blast)
   apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="d1"
      in exI)
   apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> ) d2 (Suc 0)"
      in exI)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="w1'"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="w2'"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(rule_tac
      dJ = "\<lparr>cfg_conf=c'\<rparr>"
      in cfgSTD.concatIsFromTo)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
       apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)
       apply(simp add: der1_def der2_def)
       apply(rule_tac
      x="Suc 0"
      in exI)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
      apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)+
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="n1"
      in exI)
   apply(clarsimp)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
   apply(rule_tac
      t="Suc n2"
      and s="Suc 0+n2"
      in ssubst)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)+
  apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
  apply(erule_tac
      x="c'"
      in allE)
  apply(erule_tac
      x="w2"
      in allE)
  apply(erule_tac
      x="w'"
      in allE)
  apply(erule impE)
   apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
    apply(rule cfgSTD.derivation_drop_preserves_derivation)
     apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
     apply(force)
    apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
    apply(simp add: derivation_drop_def)
   apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
    apply(rule_tac
      x="na"
      in exI)
    apply(simp add: derivation_drop_def)
    apply(simp add: maximum_of_domain_def)
    apply(case_tac na)
     apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 w' e ea c' n xa nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
   apply(rule derivation_drop_preserves_generates_maximum_of_domain)
   apply(force)
  apply(rename_tac na d w1 w2 w' e ea c' n xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
  apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> ) d1 (Suc 0)"
      in exI)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
     apply(rule cfgSTD.der2_is_derivation)
     apply(force)
    apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
    apply(force)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
   apply(simp add: der2_def)
   apply(case_tac "d1 0")
    apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(rule_tac
      x="w1'"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "n1=nb")
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
   prefer 2
   apply(rule cfgSTD.maximum_of_domainUnique)
     apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
    apply(force)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n1 n2 xab)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab)(*strict*)
  apply(subgoal_tac "maximum_of_domain (derivation_append (der2 \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr>) d1 (Suc 0)) (Suc 0+nb)")
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab)(*strict*)
   prefer 2
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab)(*strict*)
   apply(force)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab)(*strict*)
  apply(clarsimp)
  apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab y ya)(*strict*)
  apply(rule conjI)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab y ya)(*strict*)
   apply(rule_tac
      x="Suc nb"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "nb")
    apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab y ya)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab y ya nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab y ya)(*strict*)
  apply(rule conjI)
   apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab y ya)(*strict*)
   apply(rule_tac
      x="nc"
      in exI)
   apply(clarsimp)
  apply(rename_tac d w1 w2 e ea c' n xa d1 d2 w1' nb xaa w2' nc n2 xab y ya)(*strict*)
  apply(rule_tac
      x="Suc nb"
      in exI)
  apply(clarsimp)
  done

lemma hasSuc0: "
  cfgSTD.derivation_from_to G d {pair None c1} {y. \<exists>xa. y = pair xa c2}
  \<Longrightarrow> maximum_of_domain d (Suc n)
  \<Longrightarrow> \<exists>el er w. d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = el, prod_rhs = er\<rparr>) \<lparr>cfg_conf = w\<rparr>)"
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(case_tac e)
   apply(rename_tac e c prod_lhs prod_rhs)(*strict*)
   apply(clarsimp)
   apply(rename_tac c prod_lhs prod_rhs)(*strict*)
   apply(case_tac c)
   apply(rename_tac c prod_lhs prod_rhs cfg_conf)(*strict*)
   apply(clarsimp)
  apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
    apply(rule cfgSTD.from_to_is_der)
    apply(blast)+
  done

lemma derivation_from_to_noModOnTerminalStart: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = teB b # w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w2\<rparr>}
  \<Longrightarrow> x = b"
  apply(subgoal_tac "\<exists>x. maximum_of_domain d x")
   apply(erule exE)
   apply(rename_tac xa)(*strict*)
   apply(subgoal_tac " \<forall>n. \<forall>d. \<forall>b w1 x w2. maximum_of_domain d n \<and> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = teB b # w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w2\<rparr>} \<longrightarrow> b = x")
    apply(rename_tac xa)(*strict*)
    apply(blast)
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(rule_tac cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac xa)(*strict*)
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = teB b # w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB x # w2\<rparr>}")
  apply(rename_tac x)(*strict*)
  apply(thin_tac "maximum_of_domain d x")
  apply(rule allI)
  apply(rename_tac x n)(*strict*)
  apply(rule nat.induct)
   apply(rename_tac x n)(*strict*)
   apply(clarsimp)
   apply(rename_tac d b w1 x w2)(*strict*)
   apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = teB x # w2\<rparr>)")
    apply(rename_tac d b w1 x w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac d b w1 x w2 e)(*strict*)
    apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = teB b # w1\<rparr>}. d 0 = Some x")
     apply(rename_tac d b w1 x w2 e)(*strict*)
     apply(clarsimp)
    apply(rename_tac d b w1 x w2 e)(*strict*)
    apply(rule cfgSTD.derivation_from_starts_from)
    apply(rule cfgSTD.from_to_is_from)
    apply(blast)
   apply(rename_tac d b w1 x w2)(*strict*)
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rename_tac d b w1 x w2)(*strict*)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac d b w1 x w2)(*strict*)
   apply(blast)
  apply(rename_tac x n nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat d b w1 x w2)(*strict*)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = teB b # w1\<rparr>}. d 0 = Some x")
   apply(rename_tac nat d b w1 x w2)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac nat d b w1 x w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>A v w1'. (cfgSTD_step_relation G \<lparr>cfg_conf = teB b#w1\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = teB b#w1'\<rparr> \<and> d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>) \<lparr>cfg_conf = teB b#w1'\<rparr>) \<and> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G)")
   apply(rename_tac nat d b w1 x w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
   apply(erule_tac
      x = "derivation_drop d (Suc 0)"
      in allE)
   apply(erule_tac
      x = "b"
      in allE)
   apply(erule_tac
      x = "w1'"
      in allE)
   apply(erule_tac
      x = "x"
      in allE)
   apply(erule impE)
    apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
    apply(rule derivation_drop_preserves_generates_maximum_of_domain)
    apply(blast)
   apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
   apply(rule_tac
      x = "w2"
      in exI)
   apply(rule_tac
      m = "nat"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
      apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
      apply(blast)
     apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
     apply(rule_tac
      s = "Suc nat"
      in ssubst)
      apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
      apply(arith)
     apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
     apply(blast)
    apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
    apply(blast)
   apply(rename_tac nat d b w1 x w2 A v w1')(*strict*)
   apply(clarsimp)
   apply(rename_tac d b w1 x w2 A v w1')(*strict*)
   apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = teB x # w2\<rparr>)")
    apply(rename_tac d b w1 x w2 A v w1')(*strict*)
    prefer 2
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac d b w1 x w2 A v w1')(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac d b w1 x w2 A v w1')(*strict*)
    apply(blast)
   apply(rename_tac d b w1 x w2 A v w1')(*strict*)
   apply(clarsimp)
  apply(rename_tac nat d b w1 x w2)(*strict*)
  apply(subgoal_tac "\<exists>el er w. d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = el, prod_rhs = er\<rparr>) \<lparr>cfg_conf = w\<rparr>)")
   apply(rename_tac nat d b w1 x w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat d b w1 x w2 el er w)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = teB b#w1\<rparr> \<lparr>prod_lhs = el, prod_rhs = er\<rparr> \<lparr>cfg_conf = w\<rparr>")
    apply(rename_tac nat d b w1 x w2 el er w)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac nat d b w1 x w2 el er l r)(*strict*)
    apply(case_tac l)
     apply(rename_tac nat d b w1 x w2 el er l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac nat d b w1 x w2 el er l r a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat d b x w2 el er r list)(*strict*)
    apply(rule_tac
      x="teB b#list"
      in exI)
    apply(rule_tac
      x="r"
      in exI)
    apply(clarsimp)
   apply(rename_tac nat d b w1 x w2 el er w)(*strict*)
   apply(rule cfgSTD.stepOnlyDueToStepRelation)
      apply(rename_tac nat d b w1 x w2 el er w)(*strict*)
      apply(blast)
     apply(rename_tac nat d b w1 x w2 el er w)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac nat d b w1 x w2 el er w)(*strict*)
    apply(blast)
   apply(rename_tac nat d b w1 x w2 el er w)(*strict*)
   apply(blast)
  apply(rename_tac nat d b w1 x w2)(*strict*)
  apply(rule hasSuc0)
   apply(rename_tac nat d b w1 x w2)(*strict*)
   apply(blast)+
  done

lemma ZeroLengthDeriStartIsEnd: "
  valid_cfg G
  \<Longrightarrow> maximum_of_domain d 0
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>}
  \<Longrightarrow> w1 = w2"
  apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf=w2\<rparr>)")
   prefer 2
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1\<rparr>}. d 0 = Some x")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  done

lemma canElimCombine: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> \<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}"
  apply(subgoal_tac "\<forall>w. setA w \<subseteq> cfgSTD_Nonblockingness_nonterminals G \<longrightarrow> (\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {})")
   apply(erule_tac
      x="w"
      in allE)
   apply(clarsimp)
  apply(thin_tac "setA w \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
  apply(rule allI)
  apply(rename_tac w)(*strict*)
  apply(rule length_induct)
  apply(rename_tac w xs)(*strict*)
  apply(auto)
  apply(rename_tac xs)(*strict*)
  apply(case_tac "xs=[]")
   apply(rename_tac xs)(*strict*)
   apply(auto)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule conjI)
    apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)
    apply(simp add: der1_def der2_def)
   apply(clarsimp)
  apply(rename_tac xs)(*strict*)
  apply(subgoal_tac "\<exists>w' y. xs=w'@[y]")
   apply(rename_tac xs)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' y)(*strict*)
   apply(case_tac y)
    apply(rename_tac w' y a)(*strict*)
    defer
    apply(rename_tac w' y b)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' b)(*strict*)
    apply(erule_tac
      x="w'"
      in allE)
    apply(auto)
     apply(rename_tac w' b x)(*strict*)
     apply(rule_tac
      A="setA w'"
      in set_mp)
      apply(rename_tac w' b x)(*strict*)
      apply(rule_tac
      B="setA (w' @ [teB b])"
      in subset_trans)
       apply(rename_tac w' b x)(*strict*)
       apply(thin_tac "x \<in> setA w'")
       apply(thin_tac "setA (w' @ [teB b]) \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
       apply(thin_tac "\<forall>d w'nonterminal. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w' @ [teB b]\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'nonterminal\<rparr>} \<longrightarrow> setA w'nonterminal \<noteq> {}")
       apply(rename_tac w' b x)(*strict*)
       apply(induct_tac w')
        apply(rename_tac w' b x)(*strict*)
        apply(force)
       apply(rename_tac w' b x a list)(*strict*)
       apply(force)
      apply(rename_tac w' b x)(*strict*)
      apply(clarsimp)
     apply(rename_tac w' b x)(*strict*)
     apply(force)
    apply(rename_tac w' b d w'nonterminal)(*strict*)
    apply(erule_tac
      x = "derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ [teB b]\<rparr>)"
      in allE)
    apply(erule_tac
      x = "w'nonterminal @ [teB b]"
      in allE)
    apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
     apply(rename_tac w' b d w'nonterminal)(*strict*)
     apply(clarsimp)
     apply(rename_tac w' b d w'nonterminal n)(*strict*)
     apply(erule impE)
      apply(rename_tac w' b d w'nonterminal n)(*strict*)
      apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_map d (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [teB b]\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [teB b]\<rparr>) \<lparr>cfg_conf = w'\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ [teB b]\<rparr>) \<lparr>cfg_conf = w'nonterminal\<rparr>)}")
       apply(rename_tac w' b d w'nonterminal n)(*strict*)
       apply(clarsimp)
      apply(rename_tac w' b d w'nonterminal n)(*strict*)
      apply(rule contextExtendIsFromTo)
         apply(rename_tac w' b d w'nonterminal n)(*strict*)
         apply(clarsimp)
        apply(rename_tac w' b d w'nonterminal n)(*strict*)
        apply(blast)
       apply(rename_tac w' b d w'nonterminal n)(*strict*)
       apply(blast)
      apply(rename_tac w' b d w'nonterminal n)(*strict*)
      apply(blast)
     apply(rename_tac w' b d w'nonterminal n)(*strict*)
     apply(subgoal_tac "setA w'nonterminal = {} \<longrightarrow> setA (w'nonterminal @ [teB b]) = {}")
      apply(rename_tac w' b d w'nonterminal n)(*strict*)
      apply(clarsimp)
     apply(rename_tac w' b d w'nonterminal n)(*strict*)
     apply(thin_tac "setA w'nonterminal = {}")
     apply(thin_tac "setA (w'nonterminal @ [teB b]) \<noteq> {}")
     apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w'\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'nonterminal\<rparr>}")
     apply(induct_tac "w'nonterminal")
      apply(rename_tac w' b d w'nonterminal n)(*strict*)
      apply(clarsimp)
     apply(rename_tac w' b d w'nonterminal n a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' b d w'nonterminal)(*strict*)
    apply(rule cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac xs)(*strict*)
   apply(subgoal_tac "xs \<noteq> [] \<longrightarrow> (\<exists>w' y. xs = w' @ [y])")
    apply(rename_tac xs)(*strict*)
    apply(blast)
   apply(rename_tac xs)(*strict*)
   apply(thin_tac "setA xs \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
   apply(thin_tac "xs \<noteq> []")
   apply(thin_tac "\<forall>ys. length ys < length xs \<longrightarrow> setA ys \<subseteq> cfgSTD_Nonblockingness_nonterminals G \<longrightarrow> (\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = ys\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {})")
   apply(rename_tac xs)(*strict*)
   apply(induct_tac xs)
    apply(rename_tac xs)(*strict*)
    apply(clarsimp)
   apply(rename_tac xs a list)(*strict*)
   apply(auto)
  apply(rename_tac w' a)(*strict*)
  apply(erule_tac
      x="w'"
      in allE)
  apply(auto)
   apply(rename_tac w' a x)(*strict*)
   apply(rule_tac
      A="setA w'"
      in set_mp)
    apply(rename_tac w' a x)(*strict*)
    apply(rule_tac
      B="setA (w' @ [teA a])"
      in subset_trans)
     apply(rename_tac w' a x)(*strict*)
     apply(thin_tac "x \<in> setA w'")
     apply(thin_tac "setA (w' @ [teA a]) \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
     apply(thin_tac "\<forall>d w'nonterminal. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w' @ [teA a]\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'nonterminal\<rparr>} \<longrightarrow> setA w'nonterminal \<noteq> {}")
     apply(rename_tac w' a x)(*strict*)
     apply(induct_tac w')
      apply(rename_tac w' a x)(*strict*)
      apply(force)
     apply(rename_tac w' a x aa list)(*strict*)
     apply(force)
    apply(rename_tac w' a x)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' a x)(*strict*)
   apply(force)
  apply(rename_tac w' a d w'nonterminal)(*strict*)
  apply(subgoal_tac "a\<in> cfgSTD_Nonblockingness_nonterminals G")
   apply(rename_tac w' a d w'nonterminal)(*strict*)
   apply(thin_tac "setA (w' @ [teA a]) \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
   apply(auto)
   apply(rename_tac w' a d w'nonterminal da w'event)(*strict*)
   apply(rename_tac w1 A d1 w2 d2 w3)
   apply(rename_tac w1 A d1 w2 d2 w3)(*strict*)
   apply(subgoal_tac "\<exists>x. maximum_of_domain d1 x")
    apply(rename_tac w1 A d1 w2 d2 w3)(*strict*)
    apply(subgoal_tac "\<exists>x. maximum_of_domain d2 x")
     apply(rename_tac w1 A d1 w2 d2 w3)(*strict*)
     apply(erule_tac exE)+
     apply(rename_tac w1 A d1 w2 d2 w3 x xa)(*strict*)
     apply(rename_tac m1 m2)
     apply(rename_tac w1 A d1 w2 d2 w3 m1 m2)(*strict*)
     apply(erule_tac
      x = "derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ [teA A]\<rparr>)) (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = w2 @ (cfg_conf v)\<rparr>)) m1"
      in allE)
     apply(rename_tac w1 A d1 w2 d2 w3 m1 m2)(*strict*)
     apply(erule_tac
      x = "w2@w3"
      in allE)
     apply(erule impE)
      apply(rename_tac w1 A d1 w2 d2 w3 m1 m2)(*strict*)
      defer
      apply(simp add: setAConcat)
     apply(rename_tac w1 A d1 w2 d2 w3)(*strict*)
     apply(rule_tac cfgSTD.to_has_maximum_of_domain)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac w1 A d1 w2 d2 w3)(*strict*)
    apply(rule_tac cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac w' a d w'nonterminal)(*strict*)
   apply(rule_tac
      A="setA (w' @ [teA a])"
      in set_mp)
    apply(rename_tac w' a d w'nonterminal)(*strict*)
    apply(blast)
   apply(rename_tac w' a d w'nonterminal)(*strict*)
   apply(rule elemInsetA)
  apply(rename_tac w1 A d1 w2 d2 w3 m1 m2)(*strict*)
  apply(rule concatExtendIsFromToBoth)
      apply(rename_tac w1 A d1 w2 d2 w3 m1 m2)(*strict*)
      apply(blast)+
  done

lemma From_To_Derivation_Set_independent_from_Initial: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> A \<in> setA w
  \<Longrightarrow> cfgSTD.derivation_from_to G d FS TS \<longleftrightarrow> cfgSTD.derivation_from_to (G\<lparr>cfg_initial := A\<rparr>) d FS TS"
  apply(auto)
   apply(subgoal_tac "cfgSTD.derivation (G\<lparr>cfg_initial := A\<rparr>) d")
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(simp add: cfgSTD.derivation_def)
   apply(clarsimp)
   apply(rename_tac i n y)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(case_tac i)
    apply(rename_tac i n y)(*strict*)
    apply(clarsimp)
   apply(rename_tac i n y nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac n y nat)(*strict*)
   apply(case_tac "d (Suc nat)")
    apply(rename_tac n y nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac n y nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n y nat a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n y nat option b)(*strict*)
   apply(case_tac "d nat")
    apply(rename_tac n y nat option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac n y nat option b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac n y nat option b a optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac n y nat option b optiona ba)(*strict*)
   apply(case_tac option)
    apply(rename_tac n y nat option b optiona ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac n y nat option b optiona ba a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n y nat b optiona ba a)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
  apply(subgoal_tac "cfgSTD.derivation G d")
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(simp add: cfgSTD.derivation_def)
  apply(clarsimp)
  apply(rename_tac i n y)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(case_tac i)
   apply(rename_tac i n y)(*strict*)
   apply(clarsimp)
  apply(rename_tac i n y nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac n y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac n y nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n y nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y nat option b)(*strict*)
  apply(case_tac "d nat")
   apply(rename_tac n y nat option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac n y nat option b a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n y nat option b a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y nat option b optiona ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac n y nat option b optiona ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac n y nat option b optiona ba a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y nat b optiona ba a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  done

lemma cfg_subInheritsDerivation: "
  cfg_sub G1 G2
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> cfgSTD.derivation_from_to G1 d FS TS
  \<Longrightarrow> cfgSTD.derivation_from_to G2 d FS TS"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule cfgSTD.some_position_has_details_at_0)
   apply(rule cfgSTD.from_to_is_der)
   apply(blast)
  apply(subgoal_tac "cfgSTD.derivation G2 d")
   apply(simp (no_asm) add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   defer
   apply(simp (no_asm) add: cfgSTD.derivation_def)
   apply(clarsimp)
   apply(rename_tac c i)(*strict*)
   apply(case_tac i)
    apply(rename_tac c i)(*strict*)
    apply(clarsimp)
   apply(rename_tac c i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac c nat)(*strict*)
   apply(case_tac "d (Suc nat)")
    apply(rename_tac c nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac c nat a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac c nat a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac c nat option b)(*strict*)
   apply(case_tac "d nat")
    apply(rename_tac c nat option b)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      n="nat"
      in cfgSTD.derivationNoFromNone)
      apply(rename_tac c nat option b)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac c nat option b)(*strict*)
     apply(blast)
    apply(rename_tac c nat option b)(*strict*)
    apply(blast)
   apply(rename_tac c nat option b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac c nat option b a optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac c nat option b optiona ba)(*strict*)
   apply(case_tac option)
    apply(rename_tac c nat option b optiona ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac c nat b optiona ba)(*strict*)
    apply(rule cfgSTD.derivation_Always_PreEdge_prime)
     apply(rename_tac c nat b optiona ba)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac c nat b optiona ba)(*strict*)
    apply(blast)
   apply(rename_tac c nat option b optiona ba a)(*strict*)
   apply(clarsimp)
   apply(rename_tac c nat b optiona ba a)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G1 ba a b")
    apply(rename_tac c nat b optiona ba a)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac c nat b optiona ba a l r)(*strict*)
    apply(simp add: cfg_sub_def)
    apply(clarsimp)
    apply(force)
   apply(rename_tac c nat b optiona ba a)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
   apply(clarsimp)
   apply(rename_tac c nat b optiona ba a na y)(*strict*)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
  done

lemma canElimCombine2: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> \<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}
  \<Longrightarrow> setA w \<subseteq> cfgSTD_Nonblockingness_nonterminals G"
  apply(clarsimp)
  apply(rename_tac x d w')(*strict*)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(rule conjI)
   apply(rename_tac x d w')(*strict*)
   apply(force)
  apply(rename_tac x d w')(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1@[teA x]@w2=w")
   apply(rename_tac x d w')(*strict*)
   apply(clarsimp)
   apply(rename_tac x d w' w1 w2)(*strict*)
   apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1@[teA x]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w'")
    apply(rename_tac x d w' w1 w2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      in derivationCanBeDecomposed)
    apply(clarsimp)
   apply(rename_tac x d w' w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d w1 w2 d1 d2 w1' w2')(*strict*)
   apply(rename_tac w1p w2p)
   apply(rename_tac x d w1 w2 d1 d2 w1p w2p)(*strict*)
   apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = [teA x]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w1p")
    apply(rename_tac x d w1 w2 d1 d2 w1p w2p)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      in derivationCanBeDecomposed)
    apply(clarsimp)
   apply(rename_tac x d w1 w2 d1 d2 w1p w2p)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d w1 w2 d1 d2 w2p d1a d2a w1' w2')(*strict*)
   apply(rule_tac
      x="d2a"
      in exI)
   apply(rule_tac
      x="w2'"
      in exI)
   apply(clarsimp)
   apply(rule order_antisym)
    apply(rename_tac x d w1 w2 d1 d2 w2p d1a d2a w1' w2')(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac x d w1 w2 d1 d2 w2p d1a d2a w1' w2')(*strict*)
   apply(rule_tac
      B="setA (w1' @ w2' @ w2p)"
      in subset_trans)
    apply(rename_tac x d w1 w2 d1 d2 w2p d1a d2a w1' w2')(*strict*)
    apply(rule_tac
      s="setA w1' \<union> setA w2' \<union> setA w2p "
      and t="setA (w1' @ w2' @ w2p)"
      in ssubst)
     apply(rename_tac x d w1 w2 d1 d2 w2p d1a d2a w1' w2')(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac x d w1 w2 d1 d2 w2p d1a d2a w1' w2')(*strict*)
    apply(simp (no_asm) only: setAConcat concat_asso)
   apply(rename_tac x d w1 w2 d1 d2 w2p d1a d2a w1' w2')(*strict*)
   apply(blast)
  apply(rename_tac x d w')(*strict*)
  apply(rule setA_decomp)
  apply(blast)
  done

lemma derivation_drop_Transfer_to_Other_Grammar_first_Step: "
  cfgSTD.derivation G' (derivation_drop d (Suc 0))
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow> d (Suc 0) = Some (pair (Some e) c2)
  \<Longrightarrow> cfgSTD_step_relation G' c1 e c2
  \<Longrightarrow> maximum_of_domain d (Suc n)
  \<Longrightarrow> cfgSTD.derivation G' d"
  apply(simp (no_asm) add: cfgSTD.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "Suc nat\<le>Suc n")
   apply(rename_tac nat)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc nat) = Some (pair (Some e) c)")
    apply(rename_tac nat)(*strict*)
    prefer 2
    apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac nat)(*strict*)
      apply(blast)
     apply(rename_tac nat)(*strict*)
     apply(blast)
    apply(rename_tac nat)(*strict*)
    apply(arith)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat ea c)(*strict*)
   apply(subgoal_tac "\<exists>e c. d nat = Some (pair e c)")
    apply(rename_tac nat ea c)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in cfgSTD.pre_some_position_is_some_position)
      apply(rename_tac nat ea c)(*strict*)
      apply(blast)
     apply(rename_tac nat ea c)(*strict*)
     apply(blast)
    apply(rename_tac nat ea c)(*strict*)
    apply(arith)
   apply(rename_tac nat ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat ea c eaa ca)(*strict*)
   apply(simp add: cfgSTD.derivation_def)
   apply(erule_tac
      x="nat"
      and P="\<lambda>nat. case nat of 0 \<Rightarrow> case derivation_drop d (Suc 0) 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False | Suc i' \<Rightarrow> case derivation_drop d (Suc 0) nat of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> case derivation_drop d (Suc 0) i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G' i'2 i1v i2"
      in allE)
   apply(rename_tac nat ea c eaa ca)(*strict*)
   apply(case_tac nat)
    apply(rename_tac nat ea c eaa ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat ea c eaa ca nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea c eaa ca nata)(*strict*)
   apply(subgoal_tac "derivation_drop d (Suc 0) (Suc nata) = d (Suc (Suc nata))")
    apply(rename_tac ea c eaa ca nata)(*strict*)
    prefer 2
    apply(rule_tac
      t="Suc (Suc nata)"
      and s="Suc nata+Suc 0"
      in ssubst)
     apply(rename_tac ea c eaa ca nata)(*strict*)
     apply(arith)
    apply(rename_tac ea c eaa ca nata)(*strict*)
    apply(rule derivation_dropPosTransfer1)
    apply(arith)
   apply(rename_tac ea c eaa ca nata)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e. derivation_drop d (Suc 0) nata = Some (pair e ca)")
    apply(rename_tac ea c eaa ca nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac ea c eaa ca nata)(*strict*)
   apply(case_tac nata)
    apply(rename_tac ea c eaa ca nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac ea c)(*strict*)
    apply(rule_tac
      x="None"
      in exI)
    apply(rule derivation_dropPosTransfer2)
    apply(clarsimp)
    apply(blast)
   apply(rename_tac ea c eaa ca nata nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea c eaa ca nat)(*strict*)
   apply(simp add: derivation_drop_def)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "\<forall>x. x>Suc n \<longrightarrow> d x = None")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule cfgSTD.noSomeAfterMaxDom)
    apply(rename_tac nat)(*strict*)
    apply(blast)
   apply(rename_tac nat)(*strict*)
   apply(blast)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  done

lemma canElimFirstOfTwo: "
  valid_cfg G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> (\<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>})"
  apply(subgoal_tac " \<forall>n. \<forall>w1 w2 d G. valid_cfg G \<and> maximum_of_domain d n \<and> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>} \<longrightarrow> (\<exists>d. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>})")
   apply(blast)
  apply(thin_tac "valid_cfg G")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>}")
  apply(rule allI)
  apply(rename_tac n)(*strict*)
  apply(rule_tac nat.induct)
   apply(rename_tac n)(*strict*)
   apply(auto)
   apply(rename_tac w1 w2 d G)(*strict*)
   apply(rule_tac
      x = "d"
      in exI)
   apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w1@w2\<rparr>)")
    apply(rename_tac w1 w2 d G)(*strict*)
    apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
     apply(rename_tac w1 w2 d G)(*strict*)
     apply(clarsimp)
    apply(rename_tac w1 w2 d G)(*strict*)
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac w1 w2 d G)(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac w1 w2 d G)(*strict*)
    apply(clarsimp)
   apply(rename_tac w1 w2 d G)(*strict*)
   apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1@w2\<rparr>}. d 0 = Some x")
    apply(rename_tac w1 w2 d G)(*strict*)
    apply(blast)
   apply(rename_tac w1 w2 d G)(*strict*)
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac nat w1 w2 d G)(*strict*)
  apply(rename_tac n w1 w2 d G)
  apply(rename_tac n w1 w2 d G)(*strict*)
  apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = w1 @ w2\<rparr>)")
   apply(rename_tac n w1 w2 d G)(*strict*)
   apply(subgoal_tac "d (Suc 0)\<noteq>None")
    apply(rename_tac n w1 w2 d G)(*strict*)
    apply(subgoal_tac "\<exists>e. d (Suc n) = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
     apply(rename_tac n w1 w2 d G)(*strict*)
     prefer 2
     apply(rule cfgSTD.reachesToAtMaxDom)
      apply(rename_tac n w1 w2 d G)(*strict*)
      apply(rule cfgSTD.from_to_is_to)
      apply(blast)
     apply(rename_tac n w1 w2 d G)(*strict*)
     apply(clarsimp)
    apply(rename_tac n w1 w2 d G)(*strict*)
    apply(subgoal_tac "\<exists>A w l r. d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) \<lparr>cfg_conf = l @ w @ r\<rparr>) \<and> w1 @ w2 = l @ [teA A] @ r ")
     apply(rename_tac n w1 w2 d G)(*strict*)
     apply(auto)
     apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
     defer
     apply(rename_tac n w1 w2 d G y e)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_def)
     apply(auto)
     apply(erule_tac
      x = "Suc 0"
      in allE)
     apply(auto)
     apply(case_tac y)
     apply(rename_tac n w1 w2 d G y e option b)(*strict*)
     apply(auto)
     apply(rename_tac n w1 w2 d G e option b)(*strict*)
     apply(case_tac option)
      apply(rename_tac n w1 w2 d G e option b)(*strict*)
      apply(auto)
     apply(rename_tac n w1 w2 d G e b a)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(auto)
     apply(rename_tac n w1 w2 d G e b a l r)(*strict*)
     apply(case_tac a)
     apply(rename_tac n w1 w2 d G e b a l r prod_lhsa prod_rhsa)(*strict*)
     apply(auto)
     apply(rename_tac n w1 w2 d G e b l r prod_lhs prod_rhs)(*strict*)
     apply(case_tac b)
     apply(rename_tac n w1 w2 d G e b l r prod_lhs prod_rhs cfg_confa)(*strict*)
     apply(auto)
    apply(rename_tac n w1 w2 d G)(*strict*)
    apply(subgoal_tac "\<forall>i\<le>(Suc n). d i \<noteq> None")
     apply(rename_tac n w1 w2 d G)(*strict*)
     apply(erule_tac
      x="Suc 0"
      in allE)
     apply(force)
    apply(rename_tac n w1 w2 d G)(*strict*)
    apply(rule cfgSTD.allPreMaxDomSome)
     apply(rename_tac n w1 w2 d G)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac n w1 w2 d G)(*strict*)
    apply(blast)
   apply(rename_tac n w1 w2 d G)(*strict*)
   apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1@w2\<rparr>}. d 0 = Some x")
    apply(rename_tac n w1 w2 d G)(*strict*)
    apply(blast)
   apply(rename_tac n w1 w2 d G)(*strict*)
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
  apply(subgoal_tac "prefix w1 l \<or> prefix l w1")
   apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
   defer
   apply(rule mutual_prefix_prefix)
   apply(blast)
  apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
  apply(subgoal_tac "(prefix w1 l)\<or>(strict_prefix l w1)")
   apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
   prefer 2
   apply(erule disjE)
    apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
    apply(blast)
   apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
   apply(case_tac "w1 = l")
    apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
    apply(rule_tac disjI1)
    apply(simp add: strict_prefix_def prefix_def)
   apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
   apply(rule_tac disjI2)
   apply(simp add: strict_prefix_def prefix_def)
   apply(blast)
  apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
  apply(thin_tac "w1 \<sqsubseteq> l \<or> l \<sqsubseteq> w1")
  apply(simp add: strict_prefix_def prefix_def)
  apply(erule disjE)
   apply(rename_tac n w1 w2 d G e A w l r)(*strict*)
   defer
   apply(auto)
   apply(rename_tac n w2 d G e A w l r c)(*strict*)
   apply(subgoal_tac "\<exists>x. r = x @ w2")
    apply(rename_tac n w2 d G e A w l r c)(*strict*)
    apply(auto)
    apply(rename_tac n w2 d G e A w l x)(*strict*)
    apply(case_tac n)
     apply(rename_tac n w2 d G e A w l x)(*strict*)
     apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
      apply(rename_tac n w2 d G e A w l x)(*strict*)
      prefer 2
      apply(rule cfgSTD.reachesToAtMaxDom)
       apply(rename_tac n w2 d G e A w l x)(*strict*)
       apply(rule cfgSTD.from_to_is_to)
       apply(blast)
      apply(rename_tac n w2 d G e A w l x)(*strict*)
      apply(blast)
     apply(rename_tac n w2 d G e A w l x)(*strict*)
     apply(clarsimp)
     apply(rename_tac d G A)(*strict*)
     apply(rule_tac
      x = "d"
      in exI)
     apply(blast)
    apply(rename_tac n w2 d G e A w l x nat)(*strict*)
    apply(erule_tac
      x = "l @ w @ x"
      in allE)
    apply(erule_tac
      x = "w2"
      in allE)
    apply(erule_tac
      x = "derivation_drop d (Suc 0)"
      in allE)
    apply(erule_tac
      x = "G"
      in allE)
    apply(erule impE)
     apply(rename_tac n w2 d G e A w l x nat)(*strict*)
     apply(auto)
      apply(rename_tac w2 d G e A w l x nat)(*strict*)
      apply(rule derivation_drop_preserves_generates_maximum_of_domain)
      apply(blast)
     apply(rename_tac w2 d G e A w l x nat)(*strict*)
     apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_drop d (Suc 0)) {pair None \<lparr>cfg_conf = l @ w @ x @ w2\<rparr>} (if Suc nat = 0 then {pair None \<lparr>cfg_conf = l @ w @ x @ w2\<rparr>} else {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>})")
      apply(rename_tac w2 d G e A w l x nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac w2 d G e A w l x nat)(*strict*)
     apply(rule cfgSTD.derivation_drop_preserves_derivation_from_to)
       apply(rename_tac w2 d G e A w l x nat)(*strict*)
       apply(blast)
      apply(rename_tac w2 d G e A w l x nat)(*strict*)
      apply(auto)
    apply(rename_tac w2 d G e A w l x nat da)(*strict*)
    apply(subgoal_tac "\<exists>m. maximum_of_domain da m")
     apply(rename_tac w2 d G e A w l x nat da)(*strict*)
     apply(erule exE)+
     apply(rename_tac w2 d G e A w l x nat da m)(*strict*)
     apply(rule_tac
      x = "derivation_append (\<lambda>n. if (n = 0)then Some (pair None \<lparr>cfg_conf = l @ teA A # x\<rparr>) else (if n = Suc 0 then Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) \<lparr>cfg_conf = l @ w @ x\<rparr>) else None)) da (Suc 0)"
      in exI)
     apply(rename_tac w2 d G e A w l x nat da m)(*strict*)
     apply(rule cfgSTD.concatIsFromTo)
        apply(rename_tac w2 d G e A w l x nat da m)(*strict*)
        apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
        apply(auto)
       apply(rename_tac w2 d G e A w l x nat da m n v na va)(*strict*)
       apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = l @ teA A # x @ w2\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = l @ w @ x @ w2\<rparr> ")
        apply(rename_tac w2 d G e A w l x nat da m n v na va)(*strict*)
        apply(simp add: cfgSTD_step_relation_def)
        apply(auto)
       apply(rename_tac w2 d G e A w l x nat da m n v na va)(*strict*)
       apply(erule_tac
      x = "Suc 0"
      and P="\<lambda>x. case x of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (d 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G i'2 i1v i2)) (d i'))) (d x)"
      in allE)
       apply(rename_tac w2 d G e A w l x nat da m n v na va)(*strict*)
       apply(clarsimp)
      apply(rename_tac w2 d G e A w l x nat da m n v na va i)(*strict*)
      apply(case_tac i)
       apply(rename_tac w2 d G e A w l x nat da m n v na va i)(*strict*)
       apply(auto)
     apply(rename_tac w2 d G e A w l x nat da m)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac w2 d G e A w l x nat da)(*strict*)
    apply(rule_tac cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac n w2 d G e A w l r c)(*strict*)
   apply(case_tac c)
    apply(rename_tac n w2 d G e A w l r c)(*strict*)
    apply(force, force)
  apply(rename_tac n w1 d G e A w r c)(*strict*)
  apply(case_tac n)
   apply(rename_tac n w1 d G e A w r c)(*strict*)
   apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = []\<rparr>)")
    apply(rename_tac n w1 d G e A w r c)(*strict*)
    prefer 2
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac n w1 d G e A w r c)(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac n w1 d G e A w r c)(*strict*)
    apply(blast)
   apply(rename_tac n w1 d G e A w r c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d G A)(*strict*)
   apply(rule_tac
      x = "\<lambda>n. (if n = 0 then Some (pair None \<lparr>cfg_conf = []\<rparr>) else None)"
      in exI)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
   apply(auto)
   apply(rename_tac d G A i n v)(*strict*)
   apply(case_tac i)
    apply(rename_tac d G A i n v)(*strict*)
    apply(auto)
  apply(rename_tac w1 d G e A w r c nat)(*strict*)
  apply(erule_tac
      x = "w1"
      in allE)
  apply(erule_tac
      x = "c @ w @ r"
      in allE)
  apply(erule_tac
      x = "derivation_drop d (Suc 0)"
      in allE)
  apply(erule_tac
      x = "G"
      in allE)
  apply(erule impE)
   apply(rename_tac w1 d G e A w r c nat)(*strict*)
   apply(auto)
   apply(rule derivation_drop_preserves_generates_maximum_of_domain)
   apply(blast)
  apply(rename_tac w1 d G e A w r c nat)(*strict*)
  apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_drop d (Suc 0)) {pair None \<lparr>cfg_conf = w1 @ c @ w @ r\<rparr>} (if (Suc nat) = 0 then {pair None \<lparr>cfg_conf = w1 @ c @ w @ r\<rparr>} else {y. \<exists>v. y = pair v \<lparr>cfg_conf = []\<rparr>})")
   apply(rename_tac w1 d G e A w r c nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1 d G e A w r c nat)(*strict*)
  apply(rule cfgSTD.derivation_drop_preserves_derivation_from_to)
    apply(rename_tac w1 d G e A w r c nat)(*strict*)
    apply(blast)
   apply(rename_tac w1 d G e A w r c nat)(*strict*)
   apply(auto)
  done

lemma fromNoneThenToNone: "
  cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = []\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w\<rparr>}
  \<Longrightarrow> w = []"
  apply(subgoal_tac "maximum_of_domain d 0")
   apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = []\<rparr>)")
    apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = w\<rparr>)")
     apply(clarsimp)
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(clarsimp)
   apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = []\<rparr>}. d 0 = Some x")
    apply(blast)
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
  apply(auto)
  apply(rename_tac n xa)(*strict*)
  apply(erule_tac
      x="Suc 0"
      in allE)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(rename_tac n xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n xa)(*strict*)
  apply(case_tac "d (Suc 0)")
   apply(rename_tac n xa)(*strict*)
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac n xa a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n xa a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n xa option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac n xa option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac n xa option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n xa b a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  done

lemma modifyNonterminalOnlyIfInCFG: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w\<rparr>}
  \<Longrightarrow> w\<noteq>[teA A]
  \<Longrightarrow> A \<in> cfg_nonterminals G"
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "d 0 = Some(pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
    apply(rename_tac n)(*strict*)
    apply(subgoal_tac "\<exists>e. d n = Some(pair e \<lparr>cfg_conf = w\<rparr>)")
     apply(rename_tac n)(*strict*)
     apply(erule_tac exE)+
     apply(rename_tac n e)(*strict*)
     defer
     apply(rename_tac n)(*strict*)
     apply(rule cfgSTD.toAtMaxDom)
      apply(rename_tac n)(*strict*)
      apply(blast)+
    apply(rename_tac n)(*strict*)
    apply(rule cfgSTD.fromAtZero)
     apply(rename_tac n)(*strict*)
     apply(blast)+
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac n e)(*strict*)
  apply(case_tac n)
   apply(rename_tac n e)(*strict*)
   apply(auto)
  apply(rename_tac e nat)(*strict*)
  apply(subgoal_tac "\<exists>el er w. d (Suc 0) = Some (pair (Some \<lparr>prod_lhs = el, prod_rhs = er\<rparr>) \<lparr>cfg_conf = w\<rparr>)")
   apply(rename_tac e nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac e nat el er wa)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = el, prod_rhs = er\<rparr> \<lparr>cfg_conf = wa\<rparr>")
    apply(rename_tac e nat el er wa)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac e nat el er l r)(*strict*)
    apply(case_tac l)
     apply(rename_tac e nat el er l r)(*strict*)
     apply(clarsimp)
     apply(rename_tac e nat er)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(force)
    apply(rename_tac e nat el er l r a list)(*strict*)
    apply(force)
   apply(rename_tac e nat el er wa)(*strict*)
   apply(rule cfgSTD.stepOnlyDueToStepRelation)
      apply(rename_tac e nat el er wa)(*strict*)
      apply(blast)
     apply(rename_tac e nat el er wa)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac e nat el er wa)(*strict*)
    apply(blast)
   apply(rename_tac e nat el er wa)(*strict*)
   apply(blast)
  apply(rename_tac e nat)(*strict*)
  apply(rule hasSuc0)
   apply(rename_tac e nat)(*strict*)
   apply(blast)+
  done

lemma staysInNonterms2: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>)
  \<Longrightarrow> setA w' \<subseteq> cfg_nonterminals G"
  apply(subgoal_tac "setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G")
   apply(force)
  apply(rule staysInAlpha2)
       apply(force)+
  done

lemma EliminatingDerivationImpliesExistenceOfEndProduction: "
  valid_cfg G
  \<Longrightarrow> A\<in> cfg_nonterminals G
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w\<rparr>}
  \<Longrightarrow> setA w = {}
  \<Longrightarrow> \<exists>p. p \<in> cfg_productions G \<and> setA (prod_rhs p) = {}"
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(case_tac n)
    apply(rename_tac n)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
     apply(subgoal_tac "\<exists>e. d 0 = Some (pair e \<lparr>cfg_conf = w\<rparr>)")
      apply(erule exE)
      apply(rename_tac e)(*strict*)
      apply(clarsimp)
     apply(rule cfgSTD.reachesToAtMaxDom)
      apply(rule cfgSTD.from_to_is_to)
      apply(blast)
     apply(clarsimp)
    apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = [teA A]\<rparr>}. d 0 = Some x")
     apply(blast)
    apply(rule cfgSTD.derivation_from_starts_from)
    apply(rule cfgSTD.from_to_is_from)
    apply(blast)
   apply(rename_tac n nat)(*strict*)
   apply(subgoal_tac "\<exists>e. d (Suc nat) = Some (pair e \<lparr>cfg_conf = w\<rparr>)")
    apply(rename_tac n nat)(*strict*)
    prefer 2
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac n nat)(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac n nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac n nat)(*strict*)
   apply(subgoal_tac "\<exists>e c. d nat = Some (pair e c)")
    apply(rename_tac n nat)(*strict*)
    prefer 2
    apply(rule cfgSTD.some_position_has_details_before_max_dom)
      apply(rename_tac n nat)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac n nat)(*strict*)
     apply(blast)
    apply(rename_tac n nat)(*strict*)
    apply(arith)
   apply(rename_tac n nat)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
   apply(clarsimp)
   apply(rename_tac nat e ea c na x)(*strict*)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(case_tac e)
    apply(rename_tac nat e ea c na x)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat e ea c na x a)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat ea c na x a)(*strict*)
   apply(rule_tac
      x="a"
      in exI)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac nat ea c na x a l r)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
  apply(rule_tac cfgSTD.to_has_maximum_of_domain)
  apply(rule cfgSTD.from_to_is_to)
  apply(blast)
  done

lemma TailTerminalStringsGrow_1Step: "
  cfgSTD.derivation G d
  \<Longrightarrow> setA w2a = {}
  \<Longrightarrow> d (Suc ia) = Some (pair (Some e1) c)
  \<Longrightarrow> d ia = Some (pair e \<lparr>cfg_conf = v @ w2a\<rparr>)
  \<Longrightarrow> \<exists>v e. d (Suc ia) = Some (pair e \<lparr>cfg_conf = v @ w2a\<rparr>)"
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = v @ w2a\<rparr> e1 c")
   apply(simp add: cfgSTD_step_relation_def)
   apply(auto)
   apply(rename_tac l r)(*strict*)
   apply(case_tac c)
   apply(rename_tac l r cfg_confa)(*strict*)
   apply(auto)
   apply(rename_tac l r)(*strict*)
   apply(case_tac e1)
   apply(rename_tac l r prod_lhsa prod_rhsa)(*strict*)
   apply(auto)
   apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac l r A w)(*strict*)
   apply(subgoal_tac "\<exists>x. r = x @ w2a")
    apply(rename_tac l r A w)(*strict*)
    prefer 2
    apply(case_tac "setA r={}")
     apply(rename_tac l r A w)(*strict*)
     apply(rule_tac
      ?v1.0="l"
      and ?v2.0="v"
      and u="[]"
      in terminalTailEquals2)
       apply(rename_tac l r A w)(*strict*)
       apply(blast)
      apply(rename_tac l r A w)(*strict*)
      apply(blast)
     apply(rename_tac l r A w)(*strict*)
     apply(clarsimp)
     apply(blast)
    apply(rename_tac l r A w)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac l r A w)(*strict*)
   prefer 2
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(rename_tac l r A w)(*strict*)
  apply(subgoal_tac "\<exists>r1 r2 A. r1@[teA A]@r2=r \<and> setA r2={}")
   apply(rename_tac l r A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac l A w r1 r2 Aa)(*strict*)
   apply(subgoal_tac "\<exists>x. r2 = x @ w2a")
    apply(rename_tac l A w r1 r2 Aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac l A w r1 r2 Aa)(*strict*)
   apply(rule_tac
      ?v1.0="l@teA A#r1"
      and ?v2.0="v"
      and u="[]"
      in terminalTailEquals2)
     apply(rename_tac l A w r1 r2 Aa)(*strict*)
     apply(blast)
    apply(rename_tac l A w r1 r2 Aa)(*strict*)
    apply(blast)
   apply(rename_tac l A w r1 r2 Aa)(*strict*)
   apply(clarsimp)
   apply(blast)
  apply(rename_tac l r A w)(*strict*)
  apply(rule setA_decomp_R)
  apply(blast)
  done

lemma HeadTerminalStringsGrow_1Step: "
  cfgSTD.derivation G d
  \<Longrightarrow> setA w2a = {}
  \<Longrightarrow> d (Suc ia) = Some (pair (Some e1) c)
  \<Longrightarrow> d ia = Some (pair e \<lparr>cfg_conf = w2a@v\<rparr>)
  \<Longrightarrow> \<exists>v e. d (Suc ia) = Some (pair e \<lparr>cfg_conf = w2a@v\<rparr>)"
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w2a@v\<rparr> e1 c")
   apply(simp add: cfgSTD_step_relation_def)
   apply(auto)
   apply(rename_tac l r)(*strict*)
   apply(case_tac c)
   apply(rename_tac l r cfg_confa)(*strict*)
   apply(auto)
   apply(rename_tac l r)(*strict*)
   apply(case_tac e1)
   apply(rename_tac l r prod_lhsa prod_rhsa)(*strict*)
   apply(auto)
   apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac l r A w)(*strict*)
   apply(subgoal_tac "\<exists>x. l = w2a@x")
    apply(rename_tac l r A w)(*strict*)
    apply(clarsimp)
   apply(rename_tac l r A w)(*strict*)
   prefer 2
   apply(rule cfgSTD.position_change_due_to_step_relation)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(rename_tac l r A w)(*strict*)
  apply(rule_tac
      x="drop (length w2a) l"
      in exI)
  apply(rule border_left)
   apply(rename_tac l r A w)(*strict*)
   apply(force)
  apply(rename_tac l r A w)(*strict*)
  apply(force)
  done

lemma TailTerminalStringsGrow: "
  cfgSTD.derivation G d
  \<Longrightarrow> setA w2={}
  \<Longrightarrow> d i = Some (pair e \<lparr>cfg_conf=w1@w2\<rparr>)
  \<Longrightarrow> d (i+j)\<noteq>None
  \<Longrightarrow> \<exists>v e. d (i+j) = Some (pair e \<lparr>cfg_conf=v@w2\<rparr>)"
  apply(subgoal_tac " \<forall>w1 w2 e. setA w2={} \<and> d i = Some (pair e \<lparr>cfg_conf=w1@w2\<rparr>) \<and> d (i+j)\<noteq>None \<longrightarrow> (\<exists>v e. d (i+j) = Some (pair e \<lparr>cfg_conf=v@w2\<rparr>))")
   apply(clarsimp)
  apply(rule_tac
      m="i"
      and n="j"
      in cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(blast)
     apply(blast)
    apply(arith)
   apply(clarsimp)
  apply(rule allI)
  apply(rename_tac ia)(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(rule allI)+
  apply(rename_tac ia w1a w2a ea)(*strict*)
  apply(rule impI)
  apply(erule conjE)
  apply(subgoal_tac "\<exists>e c. d (Suc ia) = Some (pair e c)")
   apply(rename_tac ia w1a w2a ea)(*strict*)
   apply(erule exE)+
   apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
   apply(subgoal_tac "\<exists>e c. d ia = Some (pair e c)")
    apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
    apply(erule_tac
      x="w1a"
      in allE)
    apply(erule_tac
      x="w2a"
      in allE)
    apply(erule_tac
      x="ea"
      in allE)
    apply(erule impE)
     apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
     apply(clarsimp)
    apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc ia"
      in cfgSTD.pre_some_position_is_some_position)
      apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
      apply(blast)
     apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
     apply(blast)
    apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
    apply(arith)
   apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
   prefer 2
   apply(rename_tac ia w1a w2a ea)(*strict*)
   apply(erule conjE)+
   apply(case_tac "d (Suc ia)")
    apply(rename_tac ia w1a w2a ea)(*strict*)
    apply(blast)
   apply(rename_tac ia w1a w2a ea a)(*strict*)
   apply(case_tac a)
   apply(rename_tac ia w1a w2a ea a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
  apply(thin_tac "\<exists>e c. d ia = Some (pair e c)")
  apply(erule conjE)+
  apply(clarsimp)
  apply(rename_tac ia w1a w2a ea c y v eb)(*strict*)
  apply(subgoal_tac "\<forall>c. d(Suc ia)\<noteq>Some (pair None c)")
   apply(rename_tac ia w1a w2a ea c y v eb)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_Always_PreEdge)
   apply(blast)
  apply(rename_tac ia w1a w2a ea c y v eb)(*strict*)
  apply(case_tac ea)
   apply(rename_tac ia w1a w2a ea c y v eb)(*strict*)
   apply(force)
  apply(rename_tac ia w1a w2a ea c y v eb a)(*strict*)
  apply(subgoal_tac "\<exists>v e. d (Suc ia) = Some (pair e \<lparr>cfg_conf = v @ w2a\<rparr>)")
   apply(rename_tac ia w1a w2a ea c y v eb a)(*strict*)
   apply(force)
  apply(rename_tac ia w1a w2a ea c y v eb a)(*strict*)
  apply(rule TailTerminalStringsGrow_1Step)
     apply(rename_tac ia w1a w2a ea c y v eb a)(*strict*)
     apply(force)+
  done

lemma HeadTerminalStringsGrow: "
  cfgSTD.derivation G d
  \<Longrightarrow> setA w2={}
  \<Longrightarrow> d i = Some (pair e \<lparr>cfg_conf=w2@w1\<rparr>)
  \<Longrightarrow> d (i+j)\<noteq>None
  \<Longrightarrow> \<exists>v e. d (i+j) = Some (pair e \<lparr>cfg_conf=w2@v\<rparr>)"
  apply(subgoal_tac " \<forall>w1 w2 e. setA w2={} \<and> d i = Some (pair e \<lparr>cfg_conf=w2@w1\<rparr>) \<and> d (i+j)\<noteq>None \<longrightarrow> (\<exists>v e. d (i+j) = Some (pair e \<lparr>cfg_conf=w2@v\<rparr>))")
   apply(clarsimp)
  apply(rule_tac
      m="i"
      and n="j"
      in cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(blast)
     apply(blast)
    apply(arith)
   apply(clarsimp)
  apply(rule allI)
  apply(rename_tac ia)(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(rule allI)+
  apply(rename_tac ia w1a w2a ea)(*strict*)
  apply(rule impI)
  apply(erule conjE)
  apply(subgoal_tac "\<exists>e c. d (Suc ia) = Some (pair e c)")
   apply(rename_tac ia w1a w2a ea)(*strict*)
   apply(erule exE)+
   apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
   apply(subgoal_tac "\<exists>e c. d ia = Some (pair e c)")
    apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
    apply(erule_tac
      x="w1a"
      in allE)
    apply(erule_tac
      x="w2a"
      in allE)
    apply(erule_tac
      x="ea"
      in allE)
    apply(erule impE)
     apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
     apply(clarsimp)
    apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc ia"
      in cfgSTD.pre_some_position_is_some_position)
      apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
      apply(blast)
     apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
     apply(blast)
    apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
    apply(arith)
   apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
   prefer 2
   apply(rename_tac ia w1a w2a ea)(*strict*)
   apply(erule conjE)+
   apply(case_tac "d (Suc ia)")
    apply(rename_tac ia w1a w2a ea)(*strict*)
    apply(blast)
   apply(rename_tac ia w1a w2a ea a)(*strict*)
   apply(case_tac a)
   apply(rename_tac ia w1a w2a ea a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac ia w1a w2a ea eaa c)(*strict*)
  apply(thin_tac "\<exists>e c. d ia = Some (pair e c)")
  apply(erule conjE)+
  apply(clarsimp)
  apply(rename_tac ia w1a w2a ea c y v eb)(*strict*)
  apply(subgoal_tac "\<forall>c. d(Suc ia)\<noteq>Some (pair None c)")
   apply(rename_tac ia w1a w2a ea c y v eb)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_Always_PreEdge)
   apply(blast)
  apply(rename_tac ia w1a w2a ea c y v eb)(*strict*)
  apply(case_tac ea)
   apply(rename_tac ia w1a w2a ea c y v eb)(*strict*)
   apply(force)
  apply(rename_tac ia w1a w2a ea c y v eb a)(*strict*)
  apply(subgoal_tac "\<exists>v e. d (Suc ia) = Some (pair e \<lparr>cfg_conf = w2a@v\<rparr>)")
   apply(rename_tac ia w1a w2a ea c y v eb a)(*strict*)
   apply(force)
  apply(rename_tac ia w1a w2a ea c y v eb a)(*strict*)
  apply(rule HeadTerminalStringsGrow_1Step)
     apply(rename_tac ia w1a w2a ea c y v eb a)(*strict*)
     apply(force)+
  done

lemma TailTerminal_can_be_removed_from_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = \<beta> @ liftB y\<rparr>)
  \<Longrightarrow> d n = Some (pair e1 \<lparr>cfg_conf = x\<rparr>)
  \<Longrightarrow> \<exists>d x'. cfgSTD.derivation G d
  \<and> maximum_of_domain d n
  \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>)
  \<and> d n = Some (pair e1 \<lparr>cfg_conf = x'\<rparr>)
  \<and> x' @ liftB y = x"
  apply(subgoal_tac "\<forall>i. d i \<noteq> None \<longrightarrow> (\<exists>v e. d (0+i) = Some (pair e \<lparr>cfg_conf=v@(liftB y)\<rparr>))")
   prefer 2
   apply(rule allI, rule impI)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      d="d"
      in TailTerminalStringsGrow)
      apply(rename_tac i)(*strict*)
      apply(blast)
     apply(rename_tac i)(*strict*)
     apply(rule setA_liftB_empty)
    apply(rename_tac i)(*strict*)
    apply(blast)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rule_tac
      x="derivation_map d ((\<lambda>v. \<lparr>cfg_conf=take (length(cfg_conf v)-(length y)) (cfg_conf v)\<rparr>))"
      in exI)
  apply(rule_tac
      x="take (length x - length y) x"
      in exI)
  apply(rule conjI)
   apply(rule_tac
      P="\<lambda>c. \<exists>v. (cfg_conf c)=v@(liftB y)"
      in cfgSTD.derivation_map_preserves_derivation)
     apply(blast)
    apply(rename_tac i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e c)(*strict*)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
   apply(rename_tac c1 e c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a e b v va)(*strict*)
   apply(case_tac a)
   apply(rename_tac a e b v va cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e b v va)(*strict*)
   apply(case_tac b)
   apply(rename_tac e b v va cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e v va)(*strict*)
   apply(rule_tac
      s="length y"
      and t="length (liftB y)"
      in ssubst)
    apply(rename_tac e v va)(*strict*)
    apply(rule sym)
    apply(rule liftB_reflects_length)
   apply(rename_tac e v va)(*strict*)
   apply(clarsimp)
   apply(case_tac e)
   apply(rename_tac e v va prod_lhs prod_rhs)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac e v va A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac v va A w)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac v va A w l r)(*strict*)
   apply(rule_tac
      grr="liftB y"
      in StepCanDismissTerminalTail)
     apply(rename_tac v va A w l r)(*strict*)
     apply(rule setA_liftB_empty)
    apply(rename_tac v va A w l r)(*strict*)
    apply(blast)
   apply(rename_tac v va A w l r)(*strict*)
   apply(blast)
  apply(rule conjI)
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(blast)
  apply(rule conjI)
   apply(simp add: derivation_map_def)
   apply(rule_tac
      s="length y"
      and t="length (liftB y)"
      in ssubst)
    apply(rule sym)
    apply(rule liftB_reflects_length)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp add: derivation_map_def)
  apply(rule_tac
      s="length y"
      and t="length (liftB y)"
      in ssubst)
   apply(rule sym)
   apply(rule liftB_reflects_length)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rename_tac v)(*strict*)
  apply(rule_tac
      s="length y"
      and t="length (liftB y)"
      in ssubst)
   apply(rename_tac v)(*strict*)
   apply(rule sym)
   apply(rule liftB_reflects_length)
  apply(rename_tac v)(*strict*)
  apply(clarsimp)
  done

lemma HeadTerminal_can_be_removed_from_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = liftB y@\<beta>\<rparr>)
  \<Longrightarrow> d n = Some (pair e1 \<lparr>cfg_conf = x\<rparr>)
  \<Longrightarrow> \<exists>d x'. cfgSTD.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf = x'\<rparr>) \<and> liftB y @ x' = x"
  apply(subgoal_tac "\<forall>i. d i \<noteq> None \<longrightarrow> (\<exists>v e. d (0+i) = Some (pair e \<lparr>cfg_conf=(liftB y)@v\<rparr>))")
   prefer 2
   apply(rule allI, rule impI)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      d="d"
      in HeadTerminalStringsGrow)
      apply(rename_tac i)(*strict*)
      apply(blast)
     apply(rename_tac i)(*strict*)
     apply(rule setA_liftB_empty)
    apply(rename_tac i)(*strict*)
    apply(blast)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rule_tac
      x="derivation_map d ((\<lambda>v. \<lparr>cfg_conf=drop (length y) (cfg_conf v)\<rparr>))"
      in exI)
  apply(rule_tac
      x="drop (length y) x"
      in exI)
  apply(rule conjI)
   apply(rule_tac
      P="\<lambda>c. \<exists>v. (cfg_conf c)=(liftB y)@v"
      in cfgSTD.derivation_map_preserves_derivation)
     apply(blast)
    apply(rename_tac i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e c)(*strict*)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
   apply(rename_tac c1 e c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a e b v va)(*strict*)
   apply(case_tac a)
   apply(rename_tac a e b v va cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e b v va)(*strict*)
   apply(case_tac b)
   apply(rename_tac e b v va cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e v va)(*strict*)
   apply(case_tac e)
   apply(rename_tac e v va prod_lhs prod_rhs)(*strict*)
   apply(rename_tac A w)
   apply(rename_tac e v va A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac v va A w)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac v va A w l r)(*strict*)
   apply(rule_tac
      t="drop (length y) (liftB y)"
      and s="[]"
      in ssubst)
    apply(rename_tac v va A w l r)(*strict*)
    apply(rule_tac
      t="length y"
      and s="length (liftB y)"
      in ssubst)
     apply(rename_tac v va A w l r)(*strict*)
     apply(rule liftB_reflects_length)
    apply(rename_tac v va A w l r)(*strict*)
    apply(force)
   apply(rename_tac v va A w l r)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="length y - length (liftB y)"
      and s="0"
      in ssubst)
    apply(rename_tac v va A w l r)(*strict*)
    apply(rule_tac
      t="length y"
      and s="length (liftB y)"
      in ssubst)
     apply(rename_tac v va A w l r)(*strict*)
     apply(rule liftB_reflects_length)
    apply(rename_tac v va A w l r)(*strict*)
    apply(force)
   apply(rename_tac v va A w l r)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="drop (length y) l"
      in exI)
   apply(rule_tac
      x="r"
      in exI)
   apply(rule_tac
      t="l"
      and s="liftB y @ drop (length (liftB y)) l"
      in ssubst)
    apply(rename_tac v va A w l r)(*strict*)
    apply(rule border_left)
     apply(rename_tac v va A w l r)(*strict*)
     apply(rule setA_liftB)
    apply(rename_tac v va A w l r)(*strict*)
    apply(force)
   apply(rename_tac v va A w l r)(*strict*)
   apply(rule_tac
      t="drop (length y) (liftB y @ drop (length (liftB y)) l)"
      and s="drop (length (liftB y)) l"
      in ssubst)
    apply(rename_tac v va A w l r)(*strict*)
    apply(rule_tac
      t="length y"
      and s="length(liftB y)"
      in ssubst)
     apply(rename_tac v va A w l r)(*strict*)
     apply(rule liftB_reflects_length)
    apply(rename_tac v va A w l r)(*strict*)
    apply(rule drop_prefix_closureise)
   apply(rename_tac v va A w l r)(*strict*)
   apply(rule conjI)
    apply(rename_tac v va A w l r)(*strict*)
    apply(rule_tac
      w="liftB y"
      and v="liftB y"
      in append_injective2)
     apply(rename_tac v va A w l r)(*strict*)
     apply(clarsimp)
     apply(rule border_left)
      apply(rename_tac v va A w l r)(*strict*)
      apply(rule setA_liftB)
     apply(rename_tac v va A w l r)(*strict*)
     apply(force)
    apply(rename_tac v va A w l r)(*strict*)
    apply(force)
   apply(rename_tac v va A w l r)(*strict*)
   apply(rule_tac
      w="liftB y"
      and v="liftB y"
      in append_injective2)
    apply(rename_tac v va A w l r)(*strict*)
    apply(clarsimp)
    apply(rule border_left)
     apply(rename_tac v va A w l r)(*strict*)
     apply(rule setA_liftB)
    apply(rename_tac v va A w l r)(*strict*)
    apply(force)
   apply(rename_tac v va A w l r)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(blast)
  apply(rule conjI)
   apply(simp add: derivation_map_def)
   apply(rule_tac
      t="length y"
      and s="length (liftB y)"
      in ssubst)
    apply(rule liftB_reflects_length)
   apply(rule_tac
      t="drop (length (liftB y)) (liftB y)"
      and s="[]"
      in ssubst)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(simp add: derivation_map_def)
  apply(rule_tac
      s="length y"
      and t="length (liftB y)"
      in ssubst)
   apply(rule sym)
   apply(rule liftB_reflects_length)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rename_tac v)(*strict*)
  apply(rule_tac
      s="length y"
      and t="length (liftB y)"
      in ssubst)
   apply(rename_tac v)(*strict*)
   apply(rule sym)
   apply(rule liftB_reflects_length)
  apply(rename_tac v)(*strict*)
  apply(rule_tac
      t="length y"
      and s="length (liftB y)"
      in ssubst)
   apply(rename_tac v)(*strict*)
   apply(rule liftB_reflects_length)
  apply(rename_tac v)(*strict*)
  apply(rule_tac
      t="drop (length (liftB y)) (liftB y)"
      and s="[]"
      in ssubst)
   apply(rename_tac v)(*strict*)
   apply(force)
  apply(rename_tac v)(*strict*)
  apply(force)
  done

lemma cfgSTD_first_drop_head_terminal: "
  valid_cfg G
  \<Longrightarrow> take (ord_class.max k 1) (x # v) \<in> cfgSTD_first G (ord_class.max k 1) (teB x # w)
  \<Longrightarrow> take (k - Suc 0) v \<in> cfgSTD_first G (k - 1) w"
  apply(simp add: cfgSTD_first_def)
  apply(auto)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule inMap)
  apply(subgoal_tac "\<exists>d x'. cfgSTD.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf = x'\<rparr>) \<and> liftB [x] @ x' = liftB xa")
   apply(rename_tac xa d e1 n)(*strict*)
   prefer 2
   apply(rule HeadTerminal_can_be_removed_from_derivation)
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
  apply(clarsimp)
  apply(rename_tac xa d e1 n da x')(*strict*)
  apply(rule_tac
      x="filterB x'"
      in exI)
  apply(subgoal_tac "setA x'={}")
   apply(rename_tac xa d e1 n da x')(*strict*)
   prefer 2
   apply(rule_tac order_antisym)
    apply(rename_tac xa d e1 n da x')(*strict*)
    apply(rule_tac
      B="setA (teB x#x')"
      in subset_trans)
     apply(rename_tac xa d e1 n da x')(*strict*)
     apply(rule setA_take_head)
    apply(rename_tac xa d e1 n da x')(*strict*)
    apply(rule_tac
      t="teB x#x'"
      and s="liftB xa"
      in ssubst)
     apply(rename_tac xa d e1 n da x')(*strict*)
     apply(force)
    apply(rename_tac xa d e1 n da x')(*strict*)
    apply(rule_tac
      t="setA (liftB xa)"
      and s="{}"
      in ssubst)
     apply(rename_tac xa d e1 n da x')(*strict*)
     apply(rule setA_liftB)
    apply(rename_tac xa d e1 n da x')(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n da x')(*strict*)
   apply(blast)
  apply(rename_tac xa d e1 n da x')(*strict*)
  apply(rule conjI)
   apply(rename_tac xa d e1 n da x')(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="e1"
      in exI)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(rule sym)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac xa d e1 n da x')(*strict*)
  apply(case_tac k)
   apply(rename_tac xa d e1 n da x')(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n da x' nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      w="[x]"
      and v="[x]"
      in append_injective2)
   apply(rename_tac xa d e1 n da x' nat)(*strict*)
   apply(clarsimp)
   apply(rule liftB_inj)
   apply(clarsimp)
   apply(rule_tac
      t="liftB (take nat (filterB x'))"
      and s="take nat x'"
      in subst)
    apply(rename_tac xa d e1 n da x' nat)(*strict*)
    apply(rule liftB_take_prime)
    apply(force)
   apply(rename_tac xa d e1 n da x' nat)(*strict*)
   apply(rule_tac
      t="liftB (take (Suc nat) xa)"
      and s="(take (Suc nat) (liftB xa))"
      in ssubst)
    apply(rename_tac xa d e1 n da x' nat)(*strict*)
    apply(rule sym)
    apply(rule take_liftB)
   apply(rename_tac xa d e1 n da x' nat)(*strict*)
   apply(rule_tac
      a="drop nat x'"
      and b="drop nat x'"
      in append_injective1)
    apply(rename_tac xa d e1 n da x' nat)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="liftB xa"
      and s="teB x#x'"
      in ssubst)
     apply(rename_tac xa d e1 n da x' nat)(*strict*)
     apply(force)
    apply(rename_tac xa d e1 n da x' nat)(*strict*)
    apply(rule_tac
      t="take (Suc nat) (teB x # x')"
      and s="teB x#take nat x'"
      in ssubst)
     apply(rename_tac xa d e1 n da x' nat)(*strict*)
     apply(rule take_Suc_Cons)
    apply(rename_tac xa d e1 n da x' nat)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n da x' nat)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n da x' nat)(*strict*)
  apply(force)
  done

lemma cfgSTD_first_pull_out_terimal_tail_string: "
  valid_cfg G
  \<Longrightarrow> (kPrefix k) ` (append_language (cfgSTD_first G k w) {v}) = cfgSTD_first G k (w@(liftB v))"
  apply(rule_tac
      t="cfgSTD_first G k w"
      and s="(\<lambda>x. take k x) ` {r. \<exists>d e1 n. cfgSTD.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf=w\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=liftB r\<rparr>) }"
      in ssubst)
   apply(rule cfgSTD_first_sound)
  apply(rule_tac
      t="cfgSTD_first G k (w@(liftB v))"
      and s="(\<lambda>x. take k x) ` {r. \<exists>d e1 n. cfgSTD.derivation G d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf=w@(liftB v)\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=liftB r\<rparr>) }"
      in ssubst)
   apply(rule cfgSTD_first_sound)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(auto)
   apply(rename_tac xa)(*strict*)
   apply(rule inMap)
   apply(auto)
   apply(simp add: append_language_def)
   apply(auto)
   apply(rename_tac a d e1 n)(*strict*)
   apply(rule_tac
      x="a@v"
      in exI)
   apply(auto)
    apply(rename_tac a d e1 n)(*strict*)
    apply(rule_tac
      x="derivation_map d (\<lambda>x. \<lparr>cfg_conf=(cfg_conf x) @ (liftB v)\<rparr>)"
      in exI)
    apply(rule conjI)
     apply(rename_tac a d e1 n)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(rule contextExtendIsFromTo)
        apply(rename_tac a d e1 n)(*strict*)
        apply(force)
       apply(rename_tac a d e1 n)(*strict*)
       apply(rule_tac
      n="n"
      in cfgSTD.derivation_from_to_from_derivation)
          apply(rename_tac a d e1 n)(*strict*)
          apply(force)
         apply(rename_tac a d e1 n)(*strict*)
         apply(force)
        apply(rename_tac a d e1 n)(*strict*)
        apply(force)
       apply(rename_tac a d e1 n)(*strict*)
       apply(simp add: maximum_of_domain_def)
      apply(rename_tac a d e1 n)(*strict*)
      apply(force)
     apply(rename_tac a d e1 n)(*strict*)
     apply(force)
    apply(rename_tac a d e1 n)(*strict*)
    apply(rule_tac
      x="e1"
      in exI)
    apply(rule_tac
      x="n"
      in exI)
    apply(rule conjI)
     apply(rename_tac a d e1 n)(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(blast)
    apply(rename_tac a d e1 n)(*strict*)
    apply(simp add: derivation_map_def)
    apply(rule sym)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac a d e1 n)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "length a \<le> k")
    apply(rename_tac a d e1 n)(*strict*)
    apply(rule_tac
      t="ord_class.min (length a) k"
      and s="length a"
      in ssubst)
     apply(rename_tac a d e1 n)(*strict*)
     apply(force)
    apply(rename_tac a d e1 n)(*strict*)
    apply(force)
   apply(rename_tac a d e1 n)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(rule inMap)
  apply(subgoal_tac "\<exists>e w. d n = Some (pair e \<lparr>cfg_conf = w @ (liftB v)\<rparr>)")
   apply(rename_tac xa d e1 n)(*strict*)
   prefer 2
   apply(rule_tac
      m="0"
      in terminals_at_ending_are_never_modified_list)
        apply(rename_tac xa d e1 n)(*strict*)
        apply(force)
       apply(rename_tac xa d e1 n)(*strict*)
       apply(force)
      apply(rename_tac xa d e1 n)(*strict*)
      apply(rule setA_liftB_empty)
     apply(rename_tac xa d e1 n)(*strict*)
     apply(force)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(subgoal_tac "\<forall>m>n. d m = None")
   apply(rename_tac xa d e1 n)(*strict*)
   prefer 2
   apply(rule cfgSTD.noSomeAfterMaxDom)
    apply(rename_tac xa d e1 n)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(simp add: kPrefix_def)
  apply(simp add: append_language_def)
  apply(rule_tac
      x="take k (filterB wa) @ v"
      in exI)
  apply(rule propSym)
  apply(rule conjI)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(rule_tac
      t="take k (take k (filterB wa) @ v)"
      and s="take k (take k ((filterB wa) @ v))"
      in ssubst)
    apply(rename_tac xa d e1 n wa)(*strict*)
    apply(subgoal_tac "kPrefix k (kPrefix k (filterB wa) @ v) = kPrefix k (kPrefix k (filterB wa @ v))")
     apply(rename_tac xa d e1 n wa)(*strict*)
     prefer 2
     apply(rule sym)
     apply(rule_tac
      t="kPrefix k (kPrefix k ((filterB wa) @ v))"
      and s="(kPrefix k ((filterB wa) @ v))"
      in ssubst)
      apply(rename_tac xa d e1 n wa)(*strict*)
      apply(rule kPrefix_idemp)
     apply(rename_tac xa d e1 n wa)(*strict*)
     apply(rule kPrefix_append2)
    apply(rename_tac xa d e1 n wa)(*strict*)
    apply(simp add: kPrefix_def)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(rule_tac
      t="v"
      and s="filterB (liftB v)"
      in subst)
    apply(rename_tac xa d e1 n wa)(*strict*)
    apply(rule liftBDeConv1)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(rule_tac
      t="filterB wa @ filterB (liftB v)"
      and s="filterB (wa @ liftB v)"
      in ssubst)
    apply(rename_tac xa d e1 n wa)(*strict*)
    apply(rule sym)
    apply(rule filterB_commutes_over_concat)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(rule_tac
      t="wa @ liftB v"
      and s="liftB xa"
      in ssubst)
    apply(rename_tac xa d e1 n wa)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(rule_tac
      s="xa"
      and t="filterB (liftB xa)"
      in ssubst)
    apply(rename_tac xa d e1 n wa)(*strict*)
    apply(rule liftBDeConv1)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(rule_tac
      x="filterB wa"
      in exI)
  apply(rule propSym)
  apply(rule conjI)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(rule_tac
      x="derivation_map d (\<lambda>x. \<lparr>cfg_conf=take (length (cfg_conf x) - (length v)) (cfg_conf x)\<rparr>)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(subgoal_tac "\<forall>i\<le>n. \<exists>e w. d i = Some (pair e \<lparr>cfg_conf = w @ (liftB v)\<rparr>)")
    apply(rename_tac xa d e1 n wa)(*strict*)
    prefer 2
    apply(rule allI)
    apply(rename_tac xa d e1 n wa i)(*strict*)
    apply(rule impI)
    apply(rule_tac
      m="0"
      in terminals_at_ending_are_never_modified_list)
         apply(rename_tac xa d e1 n wa i)(*strict*)
         apply(force)
        apply(rename_tac xa d e1 n wa i)(*strict*)
        apply(force)
       apply(rename_tac xa d e1 n wa i)(*strict*)
       apply(rule setA_liftB_empty)
      apply(rename_tac xa d e1 n wa i)(*strict*)
      apply(force)
     apply(rename_tac xa d e1 n wa i)(*strict*)
     apply(force)
    apply(rename_tac xa d e1 n wa i)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(simp add: cfgSTD.derivation_def)
   apply(auto)
   apply(rename_tac xa d e1 n wa i)(*strict*)
   apply(erule_tac
      x="i"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case d 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False | Suc i' \<Rightarrow> case d i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> case d i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G i'2 i1v i2"
      in allE)
   apply(rename_tac xa d e1 n wa i)(*strict*)
   apply(case_tac i)
    apply(rename_tac xa d e1 n wa i)(*strict*)
    apply(auto)
    apply(rename_tac xa d e1 n wa)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac xa d e1 n wa nat)(*strict*)
   apply(simp add: derivation_map_def)
   apply(case_tac "d (Suc nat)")
    apply(rename_tac xa d e1 n wa nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat a)(*strict*)
   apply(subgoal_tac "Suc nat\<le>n")
    apply(rename_tac xa d e1 n wa nat a)(*strict*)
    prefer 2
    apply(erule_tac
      x="Suc nat"
      and P="\<lambda>x. n < x \<longrightarrow> d x = None"
      in allE)
    apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat a)(*strict*)
   apply(subgoal_tac "\<exists>e w. d (Suc nat) = Some (pair e \<lparr>cfg_conf = w @ liftB v\<rparr>)")
    apply(rename_tac xa d e1 n wa nat a)(*strict*)
    prefer 2
    apply(erule_tac
      x="Suc nat"
      and P="\<lambda>x. x \<le> n \<longrightarrow> (\<exists>e w. d x = Some (pair e \<lparr>cfg_conf = w @ liftB v\<rparr>))"
      in allE)
    apply(rename_tac xa d e1 n wa nat a)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat e waa)(*strict*)
   apply(simp add: derivation_map_def)
   apply(case_tac "d nat")
    apply(rename_tac xa d e1 n wa nat e waa)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat e waa a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac xa d e1 n wa nat e waa a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat e waa option b)(*strict*)
   apply(case_tac e)
    apply(rename_tac xa d e1 n wa nat e waa option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat e waa option b a)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat waa option b a)(*strict*)
   apply(subgoal_tac "\<exists>e w. d nat = Some (pair e \<lparr>cfg_conf = w @ liftB v\<rparr>)")
    apply(rename_tac xa d e1 n wa nat waa option b a)(*strict*)
    prefer 2
    apply(erule_tac
      x="nat"
      and P="\<lambda>x. x \<le> n \<longrightarrow> (\<exists>e w. d x = Some (pair e \<lparr>cfg_conf = w @ liftB v\<rparr>))"
      in allE)
    apply(rename_tac xa d e1 n wa nat waa option b a)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat waa option b a)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat waa option a wb)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac xa d e1 n wa nat waa option a wb l r)(*strict*)
   apply(rule_tac
      t="length (liftB v)"
      and s="length v"
      in subst)
    apply(rename_tac xa d e1 n wa nat waa option a wb l r)(*strict*)
    apply(rule liftB_reflects_length)
   apply(rename_tac xa d e1 n wa nat waa option a wb l r)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      grr="liftB v"
      in StepCanDismissTerminalTail)
     apply(rename_tac xa d e1 n wa nat waa option a wb l r)(*strict*)
     apply(rule setA_liftB_empty)
    apply(rename_tac xa d e1 n wa nat waa option a wb l r)(*strict*)
    apply(force)
   apply(rename_tac xa d e1 n wa nat waa option a wb l r)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="n"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(force)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rule_tac
      t="length (liftB v)"
      and s="length v"
      in subst)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(rule liftB_reflects_length)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule liftBDeConv2)
  apply(rule order_antisym)
   apply(rename_tac xa d e1 n wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(rule_tac
      B="setA (wa @ liftB v)"
      in subset_trans)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(clarsimp)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(rule_tac
      t="wa @ liftB v"
      and s="liftB xa"
      in ssubst)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(force)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(rule_tac
      t="setA (liftB xa)"
      and s="{}"
      in ssubst)
   apply(rename_tac xa d e1 n wa)(*strict*)
   apply(rule setA_liftB_empty)
  apply(rename_tac xa d e1 n wa)(*strict*)
  apply(force)
  done

lemma CFG_nonterm_free_conf_at_maximum_of_domain: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> d n=Some (pair e \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> setA w={}
  \<Longrightarrow> maximum_of_domain d n"
  apply(simp add: maximum_of_domain_def)
  apply(simp add: cfgSTD.derivation_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(auto)
  apply(case_tac "d (Suc n)")
   apply(auto)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(auto)
  apply(rename_tac option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac option b)(*strict*)
   apply(auto)
  apply(rename_tac b a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac b a l r)(*strict*)
  apply(subgoal_tac "prod_lhs a \<in> setA (l @ teA (prod_lhs a) # r)")
   apply(rename_tac b a l r)(*strict*)
   apply(force)
  apply(rename_tac b a l r)(*strict*)
  apply(rule elemInsetA)
  done

lemma CFG_earliest_word_generated_position: "
  cfgSTD.derivation G d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w@v\<rparr>)
  \<Longrightarrow> P = (\<lambda>c. \<exists>z. w@z=cfg_conf c)
  \<Longrightarrow> \<exists>k\<le>n. (\<forall>i<k. \<not> (case d i of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)) \<and>
                  (case d k of None \<Rightarrow> False
 | Some (pair e c) \<Rightarrow> P c)"
  apply(rule cfgSTD.existence_of_earliest_satisfaction_point)
    apply(force)
   apply(force)
  apply(force)
  done

lemma CFG_Nonblockingness2: "
  valid_cfg G
  \<Longrightarrow> Nonblockingness2 (cfgSTD.unmarked_language G) (cfgSTD.marked_language G)"
  apply(simp add: Nonblockingness2_def)
  apply(simp add: cfgSTD.marked_language_def cfgSTD.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(simp add: cfg_marked_effect_def cfg_marking_condition_def cfg_initial_configurations_def cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea cb ia)(*strict*)
  apply(case_tac cb)
  apply(rename_tac x d c e i ca ea cb ia cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea ia cfg_confa)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(case_tac "d 0")
   apply(rename_tac x d c e i ca ea ia cfg_confa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d c e i ca ea ia cfg_confa a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d c e i ca ea ia cfg_confa a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea ia cfg_confa b)(*strict*)
  apply(subgoal_tac "\<exists>k\<le>ia. (\<forall>i<k. \<not> (case d i of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> (\<lambda>c. \<exists>z. (liftB x)@z=cfg_conf c) c)) \<and> (case d k of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> (\<lambda>c. \<exists>z. (liftB x)@z=cfg_conf c) c)")
   apply(rename_tac x d c e i ca ea ia cfg_confa b)(*strict*)
   prefer 2
   apply(rule_tac
      e="e"
      and w="liftB x"
      and v="liftB c"
      in CFG_earliest_word_generated_position)
      apply(rename_tac x d c e i ca ea ia cfg_confa b)(*strict*)
      apply(force)
     apply(rename_tac x d c e i ca ea ia cfg_confa b)(*strict*)
     apply(force)
    apply(rename_tac x d c e i ca ea ia cfg_confa b)(*strict*)
    apply(clarsimp)
    apply(case_tac ca)
    apply(rename_tac x d c e i ca ea ia cfg_confa b cfg_confaa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d c e i ea ia cfg_conf b)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac x d c e i ca ea ia cfg_confa b)(*strict*)
   apply(force)
  apply(rename_tac x d c e i ca ea ia cfg_confa b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea ia cfg_confa b k)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(case_tac "d k")
   apply(rename_tac x d c e i ca ea ia cfg_confa b k)(*strict*)
   apply(force)
  apply(rename_tac x d c e i ca ea ia cfg_confa b k a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d c e i ca ea ia cfg_confa b k a option ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea ia cfg_confa b k option ba z)(*strict*)
  apply(rule_tac
      x="option"
      in exI)
  apply(rule_tac
      x="ba"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d c e i ca ea ia cfg_confa b k option ba z)(*strict*)
   apply(rule_tac
      x="k"
      in exI)
   apply(force)
  apply(rename_tac x d c e i ca ea ia cfg_confa b k option ba z)(*strict*)
  apply(force)
  done

lemma terminals_at_beginning_are_never_modified: "
  cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d (m + n)
  \<Longrightarrow> d m = Some (pair e1 \<lparr>cfg_conf = (liftB b) @ w\<rparr>)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<exists>e w. d x = Some (pair e \<lparr>cfg_conf = (liftB b) @ w\<rparr>)"
  apply(rule cfgSTD.property_preseved_under_steps_is_invariant2)
      apply(blast)+
  apply(auto)
  apply(rename_tac i e wa)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i e wa)(*strict*)
   apply(clarsimp, case_tac c)
   apply(rename_tac i e wa ea c cfg_conf)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = (liftB b) @ wa\<rparr> ea c")
    apply(rename_tac i e wa ea c cfg_conf)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(auto)
    apply(rename_tac i e wa ea l r)(*strict*)
    apply(case_tac l)
     apply(rename_tac i e wa ea l r)(*strict*)
     apply(auto)
     apply(rename_tac i e wa ea r)(*strict*)
     apply(case_tac b)
      apply(rename_tac i e wa ea r)(*strict*)
      apply(clarsimp)
     apply(rename_tac i e wa ea r a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac i e wa ea r a list)(*strict*)
    defer
    apply(rename_tac i e wa ea cfg_conf)(*strict*)
    apply(rule cfgSTD.position_change_due_to_step_relation)
      apply(rename_tac i e wa ea cfg_conf)(*strict*)
      apply(blast)+
   apply(rename_tac i e wa)(*strict*)
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac i e wa)(*strict*)
     apply(blast)+
   apply(rename_tac i e wa)(*strict*)
   apply(arith)
  apply(rename_tac i e wa ea r a list)(*strict*)
  apply(subgoal_tac "prefix (liftB b) (a#list) \<or> prefix (a#list) (liftB b)")
   apply(rename_tac i e wa ea r a list)(*strict*)
   prefer 2
   apply(rule_tac
      b="wa"
      and d="teA (prod_lhs ea) # r"
      in mutual_prefix_prefix)
   apply(force)
  apply(rename_tac i e wa ea r a list)(*strict*)
  apply(erule disjE)
   apply(rename_tac i e wa ea r a list)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac i e wa ea r a list c)(*strict*)
   apply(rule_tac
      t="a # list @ prod_rhs ea @ r"
      and s="(a # list) @ prod_rhs ea @ r"
      in ssubst)
    apply(rename_tac i e wa ea r a list c)(*strict*)
    apply(force)
   apply(rename_tac i e wa ea r a list c)(*strict*)
   apply(rule_tac
      t="a#list"
      and s="liftB b @ c"
      in ssubst)
    apply(rename_tac i e wa ea r a list c)(*strict*)
    apply(force)
   apply(rename_tac i e wa ea r a list c)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac i e wa ea r a list)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac i e wa ea r a list c)(*strict*)
  apply(subgoal_tac "(a # list @ c) @ wa = a # list @ teA (prod_lhs ea) # r")
   apply(rename_tac i e wa ea r a list c)(*strict*)
   prefer 2
   apply(simp (no_asm_simp))
  apply(rename_tac i e wa ea r a list c)(*strict*)
  apply(subgoal_tac "c @ wa = teA (prod_lhs ea) # r")
   apply(rename_tac i e wa ea r a list c)(*strict*)
   prefer 2
   apply(simp (no_asm_use))
  apply(rename_tac i e wa ea r a list c)(*strict*)
  apply(case_tac c)
   apply(rename_tac i e wa ea r a list c)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e ea r a list)(*strict*)
   apply(rule_tac
      x="prod_rhs ea @ r"
      in exI)
   apply(simp (no_asm_simp))
  apply(rename_tac i e wa ea r a list c aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e wa ea a list lista)(*strict*)
  apply(rule_tac
      w="a # list @ teA (prod_lhs ea) # lista"
      and v="liftB b"
      in unequal_setA)
   apply(rename_tac i e wa ea a list lista)(*strict*)
   apply(force)
  apply(rename_tac i e wa ea a list lista)(*strict*)
  apply(rule_tac
      t="setA (liftB b)"
      and s="{}"
      in ssubst)
   apply(rename_tac i e wa ea a list lista)(*strict*)
   apply(rule setA_liftB)
  apply(rename_tac i e wa ea a list lista)(*strict*)
  apply(rule_tac
      t="a # list @ teA (prod_lhs ea) # lista"
      and s="[a] @ list @ [teA (prod_lhs ea)] @ lista"
      in ssubst)
   apply(rename_tac i e wa ea a list lista)(*strict*)
   apply(force)
  apply(rename_tac i e wa ea a list lista)(*strict*)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(force)
  done

lemma F_CFG_EBSound1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G = cfg_nonterminals G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD_first_symbol_of_derivable_effect G w = cfgSTD_first_symbol_of_derivable_marked_effect G w"
  apply(rule order_antisym)
   defer
   apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def cfgSTD_first_symbol_of_derivable_marked_effect_def)
   apply(clarsimp)
   apply(rename_tac v d w')(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule_tac
      x="w'"
      in exI)
   apply(clarsimp)
  apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def cfgSTD_first_symbol_of_derivable_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac v d w')(*strict*)
  apply(subgoal_tac "setA w'\<subseteq> cfg_nonterminals G")
   apply(rename_tac v d w')(*strict*)
   apply(subgoal_tac "setA w'\<subseteq> cfgSTD_Nonblockingness_nonterminals G")
    apply(rename_tac v d w')(*strict*)
    apply(subgoal_tac "\<exists>d w''. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w'\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w''\<rparr>} \<and> setA w'' = {}")
     apply(rename_tac v d w')(*strict*)
     defer
     apply(rule canElimCombine)
      apply(rename_tac v d w')(*strict*)
      apply(blast)
     apply(rename_tac v d w')(*strict*)
     apply(force)
    apply(rename_tac v d w')(*strict*)
    apply(force)
   apply(rename_tac v d w')(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(case_tac "d 0")
    apply(rename_tac v d w')(*strict*)
    apply(clarsimp del: subsetI)
   apply(rename_tac v d w' a)(*strict*)
   apply(clarsimp del: subsetI)
   apply(rename_tac v d w' n x)(*strict*)
   apply(rule_tac
      B="setA ([teB v]@w')"
      in subset_trans)
    apply(rename_tac v d w' n x)(*strict*)
    apply(clarsimp)
   apply(rename_tac v d w' n x)(*strict*)
   apply(rule staysInNonterms2)
        apply(rename_tac v d w' n x)(*strict*)
        apply(blast)+
   apply(rename_tac v d w' n x)(*strict*)
   apply(force)
  apply(rename_tac v d w')(*strict*)
  apply(clarsimp)
  apply(rename_tac v d w' da w'')(*strict*)
  apply(rename_tac x d1 w1 d2 w2)
  apply(rename_tac x d1 w1 d2 w2)(*strict*)
  apply(subgoal_tac "\<exists>n1. maximum_of_domain d1 n1")
   apply(rename_tac x d1 w1 d2 w2)(*strict*)
   apply(erule exE)+
   apply(rename_tac x d1 w1 d2 w2 n1)(*strict*)
   apply(subgoal_tac "\<exists>n2. maximum_of_domain d2 n2")
    apply(rename_tac x d1 w1 d2 w2 n1)(*strict*)
    apply(erule exE)+
    apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
    apply(rule_tac
      x=" derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = [teB x] @ (cfg_conf v)\<rparr>)) n1"
      in exI)
    apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
    apply(rule_tac
      x="w2"
      in exI)
    apply(rule conjI)
     apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
    defer
    apply(rename_tac x d1 w1 d2 w2 n1)(*strict*)
    apply(rule cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac x d1 w1 d2 w2)(*strict*)
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
  apply(rule_tac
      dJ="\<lparr>cfg_conf=teB x # w1\<rparr>"
      in cfgSTD.concatIsFromTo)
     apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
     apply(blast)
    apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
    apply(subgoal_tac " cfgSTD.derivation_from_to G (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = [teB x] @ (cfg_conf v)\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = [teB x] @ (cfg_conf v)\<rparr>) \<lparr>cfg_conf=w1\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = [teB x] @ (cfg_conf v)\<rparr>) \<lparr>cfg_conf=w2\<rparr>)}")
     apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
     apply(clarsimp)
    apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
    apply(rule contextExtendIsFromTo2)
       apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
       apply(blast)+
  apply(rename_tac x d1 w1 d2 w2 n1 n2)(*strict*)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  done

lemma cfgSTD_first_symbol_of_derivable_marked_effect_independent_from_Initial: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> A \<in> setA w
  \<Longrightarrow> cfgSTD_first_symbol_of_derivable_marked_effect G w = cfgSTD_first_symbol_of_derivable_marked_effect (G\<lparr>cfg_initial := A\<rparr>) w"
  apply(simp add: cfgSTD_first_symbol_of_derivable_marked_effect_def)
  apply(subgoal_tac "\<forall>FS TS d. cfgSTD.derivation_from_to G d FS TS \<longleftrightarrow> cfgSTD.derivation_from_to (G\<lparr>cfg_initial := A\<rparr>) d FS TS")
   prefer 2
   apply(rule allI)+
   apply(rename_tac FS TS d)(*strict*)
   apply(rule From_To_Derivation_Set_independent_from_Initial)
      apply(rename_tac FS TS d)(*strict*)
      apply(blast, blast, blast)
   apply(rename_tac FS TS d)(*strict*)
   apply(blast)
  apply(auto)
  done

lemma table_domainContext: "
  valid_cfg G
  \<Longrightarrow> option_to_setMap (cfgSTD_first_symbol_of_derivable_effect G v) \<subseteq> option_to_setMap (cfgSTD_first_symbol_of_derivable_effect G (v @ w))"
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(simp add: option_to_setMap_def)
  apply(simp add: cfgSTD_first_symbol_of_derivable_effect_def)
  apply(auto)
  apply(rename_tac x d w')(*strict*)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   apply(rename_tac x d w')(*strict*)
   apply(erule exE)+
   apply(rename_tac x d w' n)(*strict*)
   prefer 2
   apply(rename_tac x d w')(*strict*)
   apply(rule_tac cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac x d w' n)(*strict*)
  apply(rule_tac
      x = "derivation_map d (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w\<rparr>)"
      in exI)
  apply(rule_tac
      x = "w' @ w"
      in exI)
  apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_map d (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ w\<rparr>)) {pair None ((\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ w\<rparr>) \<lparr>cfg_conf = v\<rparr>)} {y. \<exists>xa. y = pair xa ((\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ w\<rparr>) \<lparr>cfg_conf = teB x # w'\<rparr>)}")
   apply(rename_tac x d w' n)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d w' n)(*strict*)
  apply(rule contextExtendIsFromTo)
     apply(rename_tac x d w' n)(*strict*)
     apply(blast)+
  done

lemma cfgSTD_first_symbol_of_derivable_marked_effect_Nil: "
  {None} = cfgSTD_first_symbol_of_derivable_marked_effect G []"
  apply(simp add: cfgSTD_first_symbol_of_derivable_marked_effect_def)
  apply(auto)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(simp add: der1_maximum_of_domain der2_maximum_of_domain cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def cfgSTD.derivation_from_def cfgSTD.der2_is_derivation cfgSTD.der1_is_derivation)
   apply(simp add: der1_def der2_def)
  apply(rename_tac v d w')(*strict*)
  apply(rule noStepFromNone)
  apply(blast)
  done

lemma CFG_AcceptingDerivation_has_no_Nonterms_at_maximum_of_domain: "
  cfgSTD.derivation M d
  \<Longrightarrow> cfg_marking_condition M d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> (\<exists>e w. d n = Some (pair e \<lparr>cfg_conf=w\<rparr>) \<and> setA w={})"
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac i e c)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(subgoal_tac "n=i")
   apply(rename_tac i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(case_tac c)
   apply(rename_tac e c cfg_confa)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(rule cfgSTD.maximum_of_domainUnique)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   defer
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac i e c y)(*strict*)
  apply(case_tac "d (Suc i)")
   apply(rename_tac i e c y)(*strict*)
   apply(force)
  apply(rename_tac i e c y a)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac i e c y a)(*strict*)
   apply(force)
  apply(rename_tac i e c y a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i e c y a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c y option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e c y b)(*strict*)
   apply(rule cfgSTD.derivation_Always_PreEdge_prime)
    apply(rename_tac i e c y b)(*strict*)
    apply(force)
   apply(rename_tac i e c y b)(*strict*)
   apply(force)
  apply(rename_tac i e c y option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c y b a)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation M c a b")
   apply(rename_tac i e c y b a)(*strict*)
   prefer 2
   apply(rule_tac cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac i e c y b a)(*strict*)
     apply(force)
    apply(rename_tac i e c y b a)(*strict*)
    apply(force)
   apply(rename_tac i e c y b a)(*strict*)
   apply(force)
  apply(rename_tac i e c y b a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i e c y b a l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac i e c y b a l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e y b a l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma CFG_AcceptingDerivation_has_maximum_of_domain: "
  cfgSTD.derivation M d
  \<Longrightarrow> cfg_marking_condition M d
  \<Longrightarrow> \<exists>n. maximum_of_domain d n"
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac i e c)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(rule_tac
      x="i"
      in exI)
  apply(simp add: maximum_of_domain_def)
  apply(case_tac "d (Suc i)")
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c a)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac i e c a)(*strict*)
   apply(force)
  apply(rename_tac i e c a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i e c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac i e c option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e c b)(*strict*)
   apply(rule cfgSTD.derivation_Always_PreEdge_prime)
    apply(rename_tac i e c b)(*strict*)
    apply(force)
   apply(rename_tac i e c b)(*strict*)
   apply(force)
  apply(rename_tac i e c option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c b a)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation M c a b")
   apply(rename_tac i e c b a)(*strict*)
   prefer 2
   apply(rule_tac cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac i e c b a)(*strict*)
     apply(force)
    apply(rename_tac i e c b a)(*strict*)
    apply(force)
   apply(rename_tac i e c b a)(*strict*)
   apply(force)
  apply(rename_tac i e c b a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i e c b a l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac i e c b a l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e b a l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma cfg_marked_effect_is_at_maximum_of_domain: "
  x \<in> cfg_marked_effect G d
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> liftB x = w"
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac ea c i)(*strict*)
  apply(case_tac c)
  apply(rename_tac ea c i cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea i)(*strict*)
  apply(subgoal_tac "i=n")
   apply(rename_tac ea i)(*strict*)
   apply(clarsimp)
  apply(rename_tac ea i)(*strict*)
  apply(rule cfgSTD.maximum_of_domainUnique)
    apply(rename_tac ea i)(*strict*)
    apply(force)
   apply(rename_tac ea i)(*strict*)
   apply(force)
  apply(rename_tac ea i)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(case_tac "d (Suc i)")
   apply(rename_tac ea i)(*strict*)
   apply(force)
  apply(rename_tac ea i a)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac ea i a)(*strict*)
   apply(force)
  apply(rename_tac ea i a)(*strict*)
  apply(case_tac a)
  apply(rename_tac ea i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea i option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac ea i option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac ea i b)(*strict*)
   apply(rule cfgSTD.derivation_Always_PreEdge_prime)
    apply(rename_tac ea i b)(*strict*)
    apply(force)
   apply(rename_tac ea i b)(*strict*)
   apply(force)
  apply(rename_tac ea i option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea i b a)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = liftB x\<rparr> a b")
   apply(rename_tac ea i b a)(*strict*)
   prefer 2
   apply(rule_tac cfgSTD.position_change_due_to_step_relation)
     apply(rename_tac ea i b a)(*strict*)
     apply(force)
    apply(rename_tac ea i b a)(*strict*)
    apply(force)
   apply(rename_tac ea i b a)(*strict*)
   apply(force)
  apply(rename_tac ea i b a)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ea i b a l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma CFG_Nonblockingness_intro: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G = cfg_nonterminals G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G"
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom)
     apply(rename_tac dh n)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e cfg_conf)(*strict*)
  apply(rename_tac w1)
  apply(rename_tac dh n e w1)(*strict*)
  apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
   apply(rename_tac dh n e w1)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_at_0)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(force)
  apply(rename_tac dh n e w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w1 c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e w1 c cfg_conf)(*strict*)
  apply(rename_tac w2)
  apply(rename_tac dh n e w1 c w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
   apply(rename_tac dh n e w1 w2)(*strict*)
   prefer 2
   apply(rule canElimCombine)
    apply(rename_tac dh n e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac dh n e w1 w2)(*strict*)
   apply(rule_tac
      t="cfgSTD_Nonblockingness_nonterminals G"
      and s="cfg_nonterminals G"
      in ssubst)
    apply(rename_tac dh n e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac dh n e w1 w2)(*strict*)
   apply(rule_tac
      j="n"
      and i="0"
      and w="w2"
      in staysInNonterms2)
        apply(rename_tac dh n e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac dh n e w1 w2)(*strict*)
       apply(simp add: cfgSTD.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def)
       apply(rule cfg_initial_in_nonterms)
       apply(force)
      apply(rename_tac dh n e w1 w2)(*strict*)
      apply(simp add: cfgSTD.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def)
     apply(rename_tac dh n e w1 w2)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
     apply(force)
    apply(rename_tac dh n e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac dh n e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac dh n e w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w1 w2 d w')(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e w1 w2 d w' na x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
      apply(force)
     apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
     apply(force)
    apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
    apply(rule cfgSTD.belongs_configurations)
     apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
     apply(rule cfgSTD.derivation_initial_belongs)
      apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
      apply(force)
     apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
     apply(force)
    apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
    apply(force)
   apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
   apply(force)
  apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
   apply(rule_tac
      x="na"
      in exI)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
   apply(simp add: derivation_append_fit_def)
  apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
  apply(simp add: cfg_marking_condition_def derivation_append_def)
  apply(rule_tac
      x="n+na"
      in exI)
  apply(clarsimp)
  apply(simp add: cfg_marking_configuration_def)
  apply(case_tac na)
   apply(rename_tac dh n e w1 w2 d w' na x)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e w2 d w')(*strict*)
   apply(rule cfgSTD.belongs_configurations)
    apply(rename_tac dh n e w2 d w')(*strict*)
    apply(rule cfgSTD.derivation_initial_belongs)
     apply(rename_tac dh n e w2 d w')(*strict*)
     apply(force)
    apply(rename_tac dh n e w2 d w')(*strict*)
    apply(force)
   apply(rename_tac dh n e w2 d w')(*strict*)
   apply(force)
  apply(rename_tac dh n e w1 w2 d w' na x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
  apply(rule_tac
      d="d"
      in cfgSTD.belongs_configurations)
   apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
      apply(force)
     apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
     apply(force)
    apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
    defer
    apply(force)
   apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
   apply(force)
  apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
  apply(rule cfgSTD.belongs_configurations)
   apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
   apply(rule cfgSTD.derivation_initial_belongs)
    apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
    apply(force)
   apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
   apply(force)
  apply(rename_tac dh n e w1 w2 d w' x nat)(*strict*)
  apply(force)
  done

lemma cfgSTD_inst_lang_sound: "
  (\<forall>M. valid_cfg M \<longrightarrow> cfgSTD.unmarked_language M \<subseteq> cfg_effects M)"
  apply(simp add: cfg_effects_def cfgSTD.unmarked_language_def cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac M x xa d e c i z)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(case_tac "d 0")
   apply(rename_tac M x xa d e c i z)(*strict*)
   apply(clarsimp)
  apply(rename_tac M x xa d e c i z a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac M x xa d e c i z a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac M x xa d e c i z b)(*strict*)
  apply(case_tac c)
  apply(rename_tac M x xa d e c i z b cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M x xa d e i z b)(*strict*)
  apply(rule_tac
      A="setB (liftB x @ z)"
      in set_mp)
   apply(rename_tac M x xa d e i z b)(*strict*)
   prefer 2
   apply(simp only: concat_asso setBConcat)
   apply(rule_tac
      t="setB (liftB x)"
      and s="set x"
      in subst)
    apply(rename_tac M x xa d e i z b)(*strict*)
    apply(rule liftB_BiElem)
   apply(rename_tac M x xa d e i z b)(*strict*)
   apply(force)
  apply(rename_tac M x xa d e i z b)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(rule_tac
      j="i"
      and w="[teA (cfg_initial M)]"
      in staysInSigma2)
       apply(rename_tac M x xa d e i z b)(*strict*)
       apply(force)
      apply(rename_tac M x xa d e i z b)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac M x xa d e i z b)(*strict*)
     apply(force)
    apply(rename_tac M x xa d e i z b)(*strict*)
    apply(force)
   apply(rename_tac M x xa d e i z b)(*strict*)
   apply(force)
  apply(rename_tac M x xa d e i z b)(*strict*)
  apply(force)
  done

lemma cfgSTD_inst_AX_marking_condition_implies_existence_of_effect: "
  \<forall>M. valid_cfg M \<longrightarrow> (\<forall>f. cfgSTD.derivation_initial M f \<longrightarrow> cfg_marking_condition M f \<longrightarrow> cfg_marked_effect M f \<noteq> {})"
  apply(simp add: cfg_marking_condition_def cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M f i e c)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(rule_tac
      x="filterB (cfg_conf c)"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac M f i e c)(*strict*)
   apply(force)
  apply(rename_tac M f i e c)(*strict*)
  apply(rule liftBDeConv2)
  apply(force)
  done

lemma cfgSTD_inst_AX_string_state_increases: "
  \<forall>G. valid_cfg G \<longrightarrow>
        (\<forall>c1. c1 \<in> cfg_configurations G \<longrightarrow>
              (\<forall>e c2. cfgSTD_step_relation G c1 e c2 \<longrightarrow>
                      (\<exists>w. cfg_get_history c1 @ w = cfg_get_history c2)))"
  apply(simp add: cfg_get_history_def maxTermPrefix_def cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac M c1 e c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac M c1 e c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M c1 e l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac M c1 e l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e l r)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = l \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   apply(rename_tac M e l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac M e r w1 w2)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = (prod_rhs e@r) \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
    apply(rename_tac M e r w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac M e r w1 w2 w1a w2a)(*strict*)
    apply(rule_tac
      t="(THE y. (\<exists>w. liftB y @ w = liftB w1 @ w2 @ teA (prod_lhs e) # r) \<and> (\<forall>w. liftB y @ w = liftB w1 @ w2 @ teA (prod_lhs e) # r \<longrightarrow> (case w of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False)))"
      and s="w1"
      in ssubst)
     apply(rename_tac M e r w1 w2 w1a w2a)(*strict*)
     apply(case_tac w2)
      apply(rename_tac M e r w1 w2 w1a w2a)(*strict*)
      apply(clarsimp)
      apply(rename_tac M e r w1 w1a w2a)(*strict*)
      apply(rule maximal_terminal_prefix_THE)
       apply(rename_tac M e r w1 w1a w2a)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac M e r w1 w1a w2a)(*strict*)
      apply(rule sym)
      apply(rule liftBDeConv1)
     apply(rename_tac M e r w1 w2 w1a w2a a list)(*strict*)
     apply(case_tac a)
      apply(rename_tac M e r w1 w2 w1a w2a a list aa)(*strict*)
      apply(clarsimp)
      apply(rename_tac M e r w1 w1a w2a list aa)(*strict*)
      apply(rule maximal_terminal_prefix_THE)
       apply(rename_tac M e r w1 w1a w2a list aa)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac M e r w1 w1a w2a list aa)(*strict*)
      apply(rule sym)
      apply(rule liftBDeConv1)
     apply(rename_tac M e r w1 w2 w1a w2a a list b)(*strict*)
     apply(clarsimp)
    apply(rename_tac M e r w1 w2 w1a w2a)(*strict*)
    apply(case_tac w2)
     apply(rename_tac M e r w1 w2 w1a w2a)(*strict*)
     apply(clarsimp)
     apply(rename_tac M e r w1 w1a w2a)(*strict*)
     apply(rule_tac
      t="(THE y. (\<exists>w. liftB y @ w = liftB w1 @ prod_rhs e @ r) \<and> (\<forall>w. liftB y @ w = liftB w1 @ prod_rhs e @ r \<longrightarrow> (case w of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False)))"
      and s="w1@w1a"
      in ssubst)
      apply(rename_tac M e r w1 w1a w2a)(*strict*)
      apply(case_tac w2a)
       apply(rename_tac M e r w1 w1a w2a)(*strict*)
       apply(clarsimp)
       apply(rename_tac M e r w1 w1a)(*strict*)
       apply(rule_tac
      t="prod_rhs e @ r"
      and s="liftB w1a"
      in ssubst)
        apply(rename_tac M e r w1 w1a)(*strict*)
        apply(force)
       apply(rename_tac M e r w1 w1a)(*strict*)
       apply(rule maximal_terminal_prefix_THE_prime)
        apply(rename_tac M e r w1 w1a)(*strict*)
        apply(thin_tac "liftB w1a = prod_rhs e @ r")
        apply(simp only: setAConcat concat_asso setBConcat)
        apply(clarsimp)
        apply(rename_tac M e w1 w1a)(*strict*)
        apply(rule conjI)
         apply(rename_tac M e w1 w1a)(*strict*)
         apply(rule setA_liftB)
        apply(rename_tac M e w1 w1a)(*strict*)
        apply(rule setA_liftB)
       apply(rename_tac M e r w1 w1a)(*strict*)
       apply(rule_tac
      t="filterB (liftB w1 @ liftB w1a)"
      and s="filterB (liftB w1) @ (filterB (liftB w1a))"
      in ssubst)
        apply(rename_tac M e r w1 w1a)(*strict*)
        apply(rule filterB_commutes_over_concat)
       apply(rename_tac M e r w1 w1a)(*strict*)
       apply(rule_tac
      t="filterB (liftB w1)"
      and s="w1"
      in ssubst)
        apply(rename_tac M e r w1 w1a)(*strict*)
        apply(rule liftBDeConv1)
       apply(rename_tac M e r w1 w1a)(*strict*)
       apply(rule_tac
      t="filterB (liftB w1a)"
      and s="w1a"
      in ssubst)
        apply(rename_tac M e r w1 w1a)(*strict*)
        apply(rule liftBDeConv1)
       apply(rename_tac M e r w1 w1a)(*strict*)
       apply(clarsimp)
      apply(rename_tac M e r w1 w1a w2a a list)(*strict*)
      apply(case_tac a)
       apply(rename_tac M e r w1 w1a w2a a list aa)(*strict*)
       apply(clarsimp)
       apply(rename_tac M e r w1 w1a list aa)(*strict*)
       apply(rule_tac
      t="prod_rhs e @ r"
      and s="liftB w1a @ teA aa # list"
      in ssubst)
        apply(rename_tac M e r w1 w1a list aa)(*strict*)
        apply(force)
       apply(rename_tac M e r w1 w1a list aa)(*strict*)
       apply(thin_tac "liftB w1a @ teA aa # list=prod_rhs e@r")
       apply(rule_tac
      t="liftB w1 @ liftB w1a @ teA aa # list"
      and s="(liftB w1 @ liftB w1a) @ teA aa # list"
      in ssubst)
        apply(rename_tac M e r w1 w1a list aa)(*strict*)
        apply(force)
       apply(rename_tac M e r w1 w1a list aa)(*strict*)
       apply(rule_tac
      t="liftB w1 @ liftB w1a"
      and s="liftB (w1@w1a)"
      in ssubst)
        apply(rename_tac M e r w1 w1a list aa)(*strict*)
        apply(rule sym)
        apply(rule liftB_commutes_over_concat)
       apply(rename_tac M e r w1 w1a list aa)(*strict*)
       apply(rule maximal_terminal_prefix_THE)
        apply(rename_tac M e r w1 w1a list aa)(*strict*)
        apply(rule setA_liftB)
       apply(rename_tac M e r w1 w1a list aa)(*strict*)
       apply(rule sym)
       apply(rule liftBDeConv1)
      apply(rename_tac M e r w1 w1a w2a a list b)(*strict*)
      apply(clarsimp)
     apply(rename_tac M e r w1 w1a w2a)(*strict*)
     apply(force)
    apply(rename_tac M e r w1 w2 w1a w2a a list)(*strict*)
    apply(case_tac a)
     apply(rename_tac M e r w1 w2 w1a w2a a list aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac M e r w1 w1a w2a list aa)(*strict*)
     apply(rule_tac
      t="(THE y. (\<exists>w. liftB y @ w = liftB w1 @ teA aa # list @ prod_rhs e @ r) \<and> (\<forall>w. liftB y @ w = liftB w1 @ teA aa # list @ prod_rhs e @ r \<longrightarrow> (case w of [] \<Rightarrow> True | teA A # y \<Rightarrow> True | teB X # y \<Rightarrow> False)))"
      and s="w1"
      in ssubst)
      apply(rename_tac M e r w1 w1a w2a list aa)(*strict*)
      apply(rule maximal_terminal_prefix_THE)
       apply(rename_tac M e r w1 w1a w2a list aa)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac M e r w1 w1a w2a list aa)(*strict*)
      apply(rule sym)
      apply(rule liftBDeConv1)
     apply(rename_tac M e r w1 w1a w2a list aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac M e r w1 w2 w1a w2a a list b)(*strict*)
    apply(clarsimp)
   apply(rename_tac M e r w1 w2)(*strict*)
   apply(rule maxSplit)
  apply(rename_tac M e l r)(*strict*)
  apply(rule maxSplit)
  done

lemma cfgSTD_inst_ATS_axioms: "
  ATS_Language_axioms valid_cfg cfg_initial_configurations
     cfgSTD_step_relation cfg_effects cfg_marking_condition
     cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: cfgBASE_inst_AX_effect_inclusion1 cfgSTD_inst_lang_sound cfgSTD_inst_AX_marking_condition_implies_existence_of_effect cfgSTD_inst_AX_unmarked_effect_persists )
  done

lemma cfgSTD_inst_ATS_String_State_Modification_axioms: "
  ATS_String_State_Modification_axioms valid_cfg cfg_configurations cfgSTD_step_relation False cfg_get_history"
  apply(simp add: ATS_String_State_Modification_axioms_def)
  apply(simp add: cfgSTD_inst_AX_string_state_increases )
  done

interpretation "cfgSTD" : loc_cfg_1
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgSTD_step_relation"
  (* effects *)
  "cfg_effects"
  (* marking_condition *)
  "cfg_marking_condition"
  (* marked_effect *)
  "cfg_marked_effect"
  (* unmarked_effect *)
  "cfg_unmarked_effect"
  (* destinations *)
  "cfg_destination"
  (* get_destinations *)
  "cfg_get_destinations"
  (* decreasing *)
  "False"
  (* string_state *)
  "cfg_get_history"
  apply(simp add: LOCALE_DEFS_ALL LOCALE_DEFS_cfg)
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgSTD_inst_AX_step_relation_preserves_belongs )
  apply(simp add: cfgSTD_inst_ATS_String_State_Modification_axioms cfgSTD_inst_ATS_axioms )
  done

lemma cfgSTD_inst_Nonblockingness2: "
  \<forall>M. valid_cfg M \<longrightarrow> Nonblockingness2 (cfgSTD.unmarked_language M) (cfgSTD.marked_language M)"
  apply(rule allI)
  apply(rename_tac M)(*strict*)
  apply(clarsimp)
  apply(rule CFG_Nonblockingness2)
  apply(force)
  done

lemma CFG_concat_latter_is_accepting: "
  cfg_marking_condition G d
  \<Longrightarrow> d = derivation_append d1 d2 n
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> cfgSTD.derivation G d1
  \<Longrightarrow> d1 n \<noteq> None
  \<Longrightarrow> cfgSTD.derivation G d2
  \<Longrightarrow> d2 (Suc 0) \<noteq> None
  \<Longrightarrow> cfg_marking_condition G d2"
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac i y ya e c)(*strict*)
  apply(simp add: derivation_append_def)
  apply(case_tac "i\<le>n")
   apply(rename_tac i y ya e c)(*strict*)
   apply(clarsimp)
   apply(simp add: cfg_marking_configuration_def)
   apply(clarsimp)
   apply(simp add: cfgSTD.derivation_def)
   apply(erule_tac
      x="Suc i"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case if 0 \<le> n then d1 0 else d2 (0 - n) of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False | Suc i' \<Rightarrow> case if i \<le> n then d1 i else d2 (i - n) of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> case if i' \<le> n then d1 i' else d2 (i' - n) of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G i'2 i1v i2"
      in allE)
   apply(rename_tac i y ya e c)(*strict*)
   apply(fold cfgSTD.derivation_def)
   apply(clarsimp)
   apply(case_tac "Suc i\<le>n")
    apply(rename_tac i y ya e c)(*strict*)
    apply(subgoal_tac "\<exists>e c. d1 i = Some (pair e c)")
     apply(rename_tac i y ya e c)(*strict*)
     prefer 2
     apply(rule_tac
      m="n"
      in cfgSTD.pre_some_position_is_some_position)
       apply(rename_tac i y ya e c)(*strict*)
       apply(force)
      apply(rename_tac i y ya e c)(*strict*)
      apply(force)
     apply(rename_tac i y ya e c)(*strict*)
     apply(force)
    apply(rename_tac i y ya e c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e c. d1 (Suc i) = Some (pair (Some e) c)")
     apply(rename_tac i y ya e c)(*strict*)
     prefer 2
     apply(rule_tac
      m="n"
      in cfgSTD.pre_some_position_is_some_position_prime)
        apply(rename_tac i y ya e c)(*strict*)
        apply(force)
       apply(rename_tac i y ya e c)(*strict*)
       apply(force)
      apply(rename_tac i y ya e c)(*strict*)
      apply(force)
     apply(rename_tac i y ya e c)(*strict*)
     apply(force)
    apply(rename_tac i y ya e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac i y ya e c ea ca)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac i y ya e c ea ca l r)(*strict*)
    apply(case_tac c)
    apply(rename_tac i y ya e c ea ca l r cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i y ya e ea ca l r)(*strict*)
    apply(simp only: setAConcat concat_asso setBConcat)
    apply(clarsimp)
   apply(rename_tac i y ya e c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "i=n")
    apply(rename_tac i y ya e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac i y ya e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac ya e c)(*strict*)
   apply(case_tac ya)
   apply(rename_tac ya e c option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac e c option b)(*strict*)
   apply(subgoal_tac "\<exists>e c. d2 (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac e c option b)(*strict*)
    prefer 2
    apply(rule_tac
      m="(Suc 0)"
      in cfgSTD.pre_some_position_is_some_position_prime)
       apply(rename_tac e c option b)(*strict*)
       apply(force)
      apply(rename_tac e c option b)(*strict*)
      apply(force)
     apply(rename_tac e c option b)(*strict*)
     apply(force)
    apply(rename_tac e c option b)(*strict*)
    apply(force)
   apply(rename_tac e c option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac e c b ea)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e c b ea l r)(*strict*)
   apply(simp only: setAConcat concat_asso setBConcat)
   apply(clarsimp)
  apply(rename_tac i y ya e c)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="i-n"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(clarsimp)
  done

lemma cfg_unmarked_effect_two_position_derivation: "
  cfgSTD_step_relation M c1 e c2
  \<Longrightarrow> cfg_unmarked_effect M (\<lambda>n. if n = 0 then Some (pair None c1) else if n = Suc 0 then Some (pair (Some e) c2) else None) = prefix_closure {maxTermPrefix (cfg_conf c2)}"
  apply(rule order_antisym)
   apply(simp add: cfg_unmarked_effect_def)
   apply(clarsimp)
   apply(rename_tac x ea c i z)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(case_tac i)
    apply(rename_tac x ea c i z)(*strict*)
    apply(clarsimp)
    apply(rename_tac x z)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac x z l r)(*strict*)
    apply(case_tac c1)
    apply(rename_tac x z l r cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x z l r)(*strict*)
    apply(case_tac c2)
    apply(rename_tac x z l r cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x z l r)(*strict*)
    apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = l \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
     apply(rename_tac x z l r)(*strict*)
     prefer 2
     apply(rule maxSplit)
    apply(rename_tac x z l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac x z r w1 w2)(*strict*)
    apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = z \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
     apply(rename_tac x z r w1 w2)(*strict*)
     prefer 2
     apply(rule maxSplit)
    apply(rename_tac x z r w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac x r w1 w2 w1a w2a)(*strict*)
    apply(case_tac w2)
     apply(rename_tac x r w1 w2 w1a w2a)(*strict*)
     apply(clarsimp)
     apply(rename_tac x r w1 w1a w2a)(*strict*)
     apply(case_tac w2a)
      apply(rename_tac x r w1 w1a w2a)(*strict*)
      apply(clarsimp)
      apply(rename_tac x r w1 w1a)(*strict*)
      apply(subgoal_tac "liftB w1 @ teA (prod_lhs e) # r \<noteq> liftB x @ liftB w1a")
       apply(rename_tac x r w1 w1a)(*strict*)
       apply(force)
      apply(rename_tac x r w1 w1a)(*strict*)
      apply(rule_tac
      A="prod_lhs e"
      in unequal_by_setA)
       apply(rename_tac x r w1 w1a)(*strict*)
       apply(rule elemInsetA)
      apply(rename_tac x r w1 w1a)(*strict*)
      apply(thin_tac "liftB x @ liftB w1a = liftB w1 @ teA (prod_lhs e) # r")
      apply(simp only: setAConcat concat_asso setBConcat)
      apply(rule_tac
      t="setA (liftB x)"
      and s="{}"
      in ssubst)
       apply(rename_tac x r w1 w1a)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac x r w1 w1a)(*strict*)
      apply(rule_tac
      t="setA (liftB w1a)"
      and s="{}"
      in ssubst)
       apply(rename_tac x r w1 w1a)(*strict*)
       apply(rule setA_liftB)
      apply(rename_tac x r w1 w1a)(*strict*)
      apply(force)
     apply(rename_tac x r w1 w1a w2a a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x r w1 w1a a list)(*strict*)
     apply(case_tac a)
      apply(rename_tac x r w1 w1a a list aa)(*strict*)
      apply(clarsimp)
      apply(rename_tac x r w1 w1a list aa)(*strict*)
      apply(rule_tac
      t="w1"
      and s="x@w1a"
      in ssubst)
       apply(rename_tac x r w1 w1a list aa)(*strict*)
       prefer 2
       apply(rule_tac
      t="maxTermPrefix (liftB (x @ w1a) @ prod_rhs e @ r)"
      and s="(x @ w1a) @ (maxTermPrefix (prod_rhs e @ r))"
      in ssubst)
        apply(rename_tac x r w1 w1a list aa)(*strict*)
        apply(rule maxTermPrefix_shift)
       apply(rename_tac x r w1 w1a list aa)(*strict*)
       apply(force)
      apply(rename_tac x r w1 w1a list aa)(*strict*)
      apply(rule sym)
      apply(rule_tac
      A="aa"
      and ?v1.0="list"
      and B="(prod_lhs e)"
      and ?v2.0="r"
      in identical_temrinal_maximal_prefix)
      apply(rule_tac
      t="liftB (x @ w1a)"
      and s="liftB x @ liftB w1a"
      in ssubst)
       apply(rename_tac x r w1 w1a list aa)(*strict*)
       apply(rule liftB_commutes_over_concat)
      apply(rename_tac x r w1 w1a list aa)(*strict*)
      apply(force)
     apply(rename_tac x r w1 w1a a list b)(*strict*)
     apply(clarsimp)
    apply(rename_tac x r w1 w2 w1a w2a a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x r w1 w1a w2a a list)(*strict*)
    apply(case_tac a)
     apply(rename_tac x r w1 w1a w2a a list aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac x r w1 w1a w2a list aa)(*strict*)
     prefer 2
     apply(rename_tac x r w1 w1a w2a a list b)(*strict*)
     apply(clarsimp)
    apply(rename_tac x r w1 w1a w2a list aa)(*strict*)
    apply(rule_tac
      t="maxTermPrefix (liftB w1 @ teA aa # list @ prod_rhs e @ r)"
      and s="w1"
      in ssubst)
     apply(rename_tac x r w1 w1a w2a list aa)(*strict*)
     apply(rule maxTermPrefix_mixed_string)
    apply(rename_tac x r w1 w1a w2a list aa)(*strict*)
    apply(case_tac w2a)
     apply(rename_tac x r w1 w1a w2a list aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac x r w1 w1a list aa)(*strict*)
     apply(subgoal_tac "liftB w1 @ teA aa # list @ teA (prod_lhs e) # r \<noteq> liftB x @ liftB w1a")
      apply(rename_tac x r w1 w1a list aa)(*strict*)
      apply(force)
     apply(rename_tac x r w1 w1a list aa)(*strict*)
     apply(rule_tac
      A="aa"
      in unequal_by_setA)
      apply(rename_tac x r w1 w1a list aa)(*strict*)
      apply(rule elemInsetA)
     apply(rename_tac x r w1 w1a list aa)(*strict*)
     apply(thin_tac "liftB x @ liftB w1a = liftB w1 @ teA aa # list @ teA (prod_lhs e) # r")
     apply(simp only: setAConcat concat_asso setBConcat)
     apply(rule_tac
      t="setA (liftB x)"
      and s="{}"
      in ssubst)
      apply(rename_tac x r w1 w1a list aa)(*strict*)
      apply(rule setA_liftB)
     apply(rename_tac x r w1 w1a list aa)(*strict*)
     apply(rule_tac
      t="setA (liftB w1a)"
      and s="{}"
      in ssubst)
      apply(rename_tac x r w1 w1a list aa)(*strict*)
      apply(rule setA_liftB)
     apply(rename_tac x r w1 w1a list aa)(*strict*)
     apply(force)
    apply(rename_tac x r w1 w1a w2a list aa a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac x r w1 w1a list aa a lista)(*strict*)
    apply(case_tac a)
     apply(rename_tac x r w1 w1a list aa a lista ab)(*strict*)
     apply(clarsimp)
     apply(rename_tac x r w1 w1a list aa lista ab)(*strict*)
     apply(rule_tac
      t="w1"
      and s="x@w1a"
      in ssubst)
      apply(rename_tac x r w1 w1a list aa lista ab)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x r w1 w1a list aa lista ab)(*strict*)
     apply(rule_tac
      A="aa"
      and ?v1.0="list @ teA (prod_lhs e) # r"
      and B="ab"
      and ?v2.0="lista"
      in identical_temrinal_maximal_prefix)
     apply(rule_tac
      t="liftB (x @ w1a)"
      and s="liftB x @ liftB w1a"
      in ssubst)
      apply(rename_tac x r w1 w1a list aa lista ab)(*strict*)
      apply(rule liftB_commutes_over_concat)
     apply(rename_tac x r w1 w1a list aa lista ab)(*strict*)
     apply(force)
    apply(rename_tac x r w1 w1a list aa a lista b)(*strict*)
    apply(clarsimp)
   apply(rename_tac x ea c i z nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x z)(*strict*)
   apply(case_tac c2)
   apply(rename_tac x z cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x z)(*strict*)
   apply(rule_tac
      t="maxTermPrefix (liftB x @ z)"
      and s="x@maxTermPrefix z"
      in ssubst)
    apply(rename_tac x z)(*strict*)
    apply(rule maxTermPrefix_shift)
   apply(rename_tac x z)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x c)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(rule_tac
      x="Some e"
      in exI)
  apply(rule_tac
      x="c2"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac x c)(*strict*)
   apply(force)
  apply(rename_tac x c)(*strict*)
  apply(subgoal_tac "\<exists>z. liftB (maxTermPrefix (cfg_conf c2)) @ z = (cfg_conf c2)")
   apply(rename_tac x c)(*strict*)
   prefer 2
   apply(rule maxTermPrefix_prefix)
  apply(rename_tac x c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c z)(*strict*)
  apply(rule_tac
      x="liftB c@ z"
      in exI)
  apply(rule_tac
      t="cfg_conf c2"
      and s="liftB (maxTermPrefix (cfg_conf c2)) @ z"
      in ssubst)
   apply(rename_tac x c z)(*strict*)
   apply(force)
  apply(rename_tac x c z)(*strict*)
  apply(rule_tac
      t="maxTermPrefix (cfg_conf c2)"
      and s="x @ c"
      in ssubst)
   apply(rename_tac x c z)(*strict*)
   apply(force)
  apply(rename_tac x c z)(*strict*)
  apply(rule_tac
      t="liftB (x @ c)"
      and s="liftB x @ liftB c"
      in ssubst)
   apply(rename_tac x c z)(*strict*)
   apply(rule liftB_commutes_over_concat)
  apply(rename_tac x c z)(*strict*)
  apply(force)
  done

lemma CFG_derivation_map_preserves_and_reflects_mset: "
  cfgSTD.derivation M d
  \<Longrightarrow> d 0 = Some (pair None c0)
  \<Longrightarrow> mset (cfg_conf c0) = mset (cfg_conf (C c0))
  \<Longrightarrow> cfgSTD.derivation M d'
  \<Longrightarrow> d' = derivation_map d C
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> mset (cfg_conf c) = mset (cfg_conf (C c))"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgSTD.pre_some_position_is_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(blast)
    apply(rename_tac n e c)(*strict*)
    apply(blast)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e c ea ca)(*strict*)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(erule_tac
      x="ca"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac n e c ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgSTD.pre_some_position_is_some_position_prime)
      apply(rename_tac n e c ea ca)(*strict*)
      apply(blast)
     apply(rename_tac n e c ea ca)(*strict*)
     apply(blast)
    apply(rename_tac n e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac n e c ea ca)(*strict*)
   apply(force)
  apply(rename_tac n e c ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c ea ca eb)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation M ca eb c")
   apply(rename_tac n c ea ca eb)(*strict*)
   prefer 2
   apply(simp add: cfgSTD.derivation_def)
   apply(erule_tac
      x="Suc n"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case d 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False | Suc i' \<Rightarrow> case d i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> case d i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation M i'2 i1v i2"
      in allE)
   apply(rename_tac n c ea ca eb)(*strict*)
   apply(clarsimp)
  apply(rename_tac n c ea ca eb)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation M (C ca) eb (C c)")
   apply(rename_tac n c ea ca eb)(*strict*)
   prefer 2
   apply(simp add: cfgSTD.derivation_def)
   apply(erule_tac
      x="Suc n"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case derivation_map d C 0 of None \<Rightarrow> False | Some (pair None c) \<Rightarrow> True | Some (pair (Some e) c) \<Rightarrow> False | Suc i' \<Rightarrow> case derivation_map d C i of None \<Rightarrow> True | Some (pair i1 i2) \<Rightarrow> case derivation_map d C i' of None \<Rightarrow> False | Some (pair i'1 i'2) \<Rightarrow> case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation M i'2 i1v i2"
      in allE)
   apply(rename_tac n c ea ca eb)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac n c ea ca eb)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c ea ca eb l r la ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac n c ea ca eb l r la ra cfg_confa)(*strict*)
  apply(case_tac ca)
  apply(rename_tac n c ea ca eb l r la ra cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ea eb l r la ra)(*strict*)
  apply(subgoal_tac "mset (la @ ra) = mset (l @ r)")
   apply(rename_tac n ea eb l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="[teA (prod_lhs eb)]"
      in mset_drop_part)
   apply(force)
  apply(rename_tac n ea eb l r la ra)(*strict*)
  apply(rule mset_add_part)
  apply(force)
  done

lemma CFG_derivation_map_preserves_and_reflects_empty_setA: "
  cfgSTD.derivation M d
  \<Longrightarrow> d 0 = Some (pair None c0)
  \<Longrightarrow> mset (cfg_conf c0) = mset (cfg_conf (C c0))
  \<Longrightarrow> cfgSTD.derivation M d'
  \<Longrightarrow> d' = derivation_map d C
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> (setA (cfg_conf c) = {}) = (setA (cfg_conf (C c)) = {})"
  apply(rule_tac
      t="setA (cfg_conf c) = {}"
      and s="(\<forall>A. mset (cfg_conf c) (teA A) = 0)"
      in ssubst)
   apply(rule setA_vs_mset_empty)
  apply(rule_tac
      t="setA (cfg_conf (C c)) = {}"
      and s="(\<forall>A. mset (cfg_conf (C c)) (teA A) = 0)"
      in ssubst)
   apply(rule setA_vs_mset_empty)
  apply(rule_tac
      t="mset (cfg_conf c)"
      and s="mset (cfg_conf (C c))"
      in ssubst)
   apply(rule CFG_derivation_map_preserves_and_reflects_mset)
        prefer 5
        apply(force)+
  done

lemma cfgSTD_inst_Nonblockingness_branching_correspond1: "
  (\<forall>M. valid_cfg M \<longrightarrow> cfgSTD.Nonblockingness_branching M \<longrightarrow> nonblockingness_language (cfgSTD.unmarked_language M) (cfgSTD.marked_language M))"
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(simp add: nonblockingness_language_def cfgSTD.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac M xa d)(*strict*)
  apply(subgoal_tac "cfgSTD.belongs M d")
   apply(rename_tac M xa d)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_initial_belongs)
    apply(rename_tac M xa d)(*strict*)
    apply(force)
   apply(rename_tac M xa d)(*strict*)
   apply(force)
  apply(rename_tac M xa d)(*strict*)
  apply(subgoal_tac "\<exists>v. v \<in> cfgSTD.marked_language M \<and> (\<exists>c. xa @ c = v)")
   apply(rename_tac M xa d)(*strict*)
   apply(clarsimp)
  apply(rename_tac M xa d)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z)(*strict*)
  apply(erule_tac
      x="derivation_take d i"
      in allE)
  apply(erule impE)
   apply(rename_tac M xa d e c i z)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac M xa d e c i z)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac M xa d e c i z)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M xa d e c i z)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac M xa d e c i z)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac M xa d e c i z)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x)(*strict*)
  apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
   apply(rename_tac M xa d e c i z dc x)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac M xa d e c i z dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac M xa d e c i z dc x ca)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac M xa d e c i z dc x ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
  apply(subgoal_tac "cfgSTD.derivation M (derivation_append (derivation_take d i) dc i)")
   apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
   prefer 2
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
     apply(rule cfgSTD.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
    apply(force)
   apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: derivation_append_fit_def)
  apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
  apply(subgoal_tac "maximum_of_domain (derivation_append (derivation_take d i) dc i) (i + x)")
   apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
   prefer 2
   apply(rule concat_has_max_dom)
    apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
   apply(force)
  apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
  apply(subgoal_tac "\<exists>e c. (derivation_append (derivation_take d i) dc i) (i+x) = Some (pair e c)")
   apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
   prefer 2
   apply(rule_tac
      n="i+x"
      in cfgSTD.some_position_has_details_before_max_dom)
     apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
    apply(force)
   apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
   apply(force)
  apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca cb ea cc)(*strict*)
  apply(case_tac cc)
  apply(rename_tac M xa d e c i z dc x ca cb ea cc cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca cb ea cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
  apply(rule_tac
      x="filterB w"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
   apply(simp add: cfgSTD.marked_language_def)
   apply(rule_tac
      x="derivation_append (derivation_take d i) dc i"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
    apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
      apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
      apply(force)
     apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
     apply(rule cfgSTD.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
    apply(force)
   apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
   apply(simp add: cfg_marked_effect_def)
   apply(rule_tac
      x="ea"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf = w\<rparr>"
      in exI)
   apply(clarsimp)
   apply(simp add: cfg_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc)(*strict*)
   apply(simp add: cfg_marking_configuration_def)
   apply(clarsimp)
   apply(subgoal_tac "ia=i+x")
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc)(*strict*)
    prefer 2
    apply(rule_tac
      d="derivation_append (derivation_take d i) dc i"
      in cfgSTD.maximum_of_domainUnique)
      apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc)(*strict*)
      apply(force)
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc)(*strict*)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc)(*strict*)
    apply(simp add: maximum_of_domain_def)
    apply(case_tac "derivation_append (derivation_take d i) dc i (Suc ia) = None")
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc)(*strict*)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_append (derivation_take d i) dc i) ia = Some (pair e1 c1) \<and> (derivation_append (derivation_take d i) dc i) (Suc ia) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation M c1 e2 c2")
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc ia"
      in cfgSTD.step_detail_before_some_position)
       apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
       apply(simp add: cfgSTD.derivation_initial_def)
      apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
      apply(force)
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc ya e2 c2)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc ya e2 c2 l r)(*strict*)
    apply(subgoal_tac "prod_lhs e2 \<in> setA (l @ teA (prod_lhs e2) # r)")
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc ya e2 c2 l r)(*strict*)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc ya e2 c2 l r)(*strict*)
    apply(simp only: setAConcat concat_asso setBConcat)
    apply(force)
   apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac M xa d e c i z dc x ca cb w eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac M xa d e c i z dc x ca cb w eb)(*strict*)
    apply(rule_tac
      x="i+x"
      in exI)
    apply(clarsimp)
   apply(rename_tac M xa d e c i z dc x ca cb w eb)(*strict*)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
  apply(subgoal_tac "\<exists>e w. (derivation_append (derivation_take d i) dc i) (i+x) = Some (pair e \<lparr>cfg_conf = (liftB xa) @ w\<rparr>)")
   apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
   prefer 2
   apply(rule terminals_at_beginning_are_never_modified)
       apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
       apply(force)
      apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
      apply(force)
     apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
     apply(simp add: derivation_append_def derivation_take_def derivation_append_fit_def)
     apply(clarsimp)
     apply(rename_tac M xa d e i z dc x ca cb ea w)(*strict*)
     apply(case_tac ca)
     apply(rename_tac M xa d e i z dc x ca cb ea w cfg_confa)(*strict*)
     apply(clarsimp)
     apply(rename_tac M xa d e i z dc x cb ea w)(*strict*)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
    apply(force)
   apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
   apply(force)
  apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca cb ea wa)(*strict*)
  apply(rule_tac
      x="filterB wa"
      in exI)
  apply(rule_tac
      t="filterB (liftB xa @ wa)"
      and s="filterB (liftB xa) @ filterB wa"
      in ssubst)
   apply(rename_tac M xa d e c i z dc x ca cb ea wa)(*strict*)
   apply(rule filterB_commutes_over_concat)
  apply(rename_tac M xa d e c i z dc x ca cb ea wa)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule liftBDeConv1)
  done

lemma cfgSTD_inst_lang_finite: "
  (\<forall>G. valid_cfg G \<longrightarrow> cfgSTD.finite_marked_language G = cfgSTD.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x)(*strict*)
   apply(simp add: cfgSTD.marked_language_def cfgSTD.finite_marked_language_def)
   apply(clarsimp)
   apply(rename_tac G x d xa)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgSTD.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: cfgSTD.marked_language_def cfgSTD.finite_marked_language_def)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G x d e c i)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G x d e c i)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G x d e c i)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac G x d e c i)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G x d e c i)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G x d e c i)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="i"
      in exI)
   apply(simp add: derivation_take_def)
  apply(rename_tac G x d e c i)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d e c i ea ca ia)(*strict*)
  apply(rule conjI)
   apply(rename_tac G x d e c i ea ca ia)(*strict*)
   apply(simp add: cfg_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(simp add: derivation_take_def)
   apply(simp add: cfg_marking_configuration_def)
   apply(clarsimp)
   apply(case_tac "ia \<le> i")
    apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
   apply(clarsimp)
   apply(rule cfgSTD.belongs_configurations)
    apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
    apply(rule cfgSTD.derivation_initial_belongs)
     apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
     apply(force)
    apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
    apply(force)
   apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
   apply(force)
  apply(rename_tac G x d e c i ea ca ia)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma cfgSTD_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_cfg G \<longrightarrow> cfgSTD.finite_unmarked_language G = cfgSTD.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x)(*strict*)
   apply(simp add: cfgSTD.unmarked_language_def cfgSTD.finite_unmarked_language_def)
   apply(clarsimp)
   apply(rename_tac G x d xa)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgSTD.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: cfgSTD.unmarked_language_def cfgSTD.finite_unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G x d e c i z)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G x d e c i z)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G x d e c i z)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac G x d e c i z)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G x d e c i z)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G x d e c i z)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G x d e c i z)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(simp add: derivation_take_def)
   apply(rename_tac G x d e c i z)(*strict*)
   apply(force)
  apply(rename_tac G x d e c i z)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma cfgSTD_inst_accept: "
  (\<forall>G d. cfgSTD.derivation_initial G d \<longrightarrow> cfg_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> cfg_marking_configuration G))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  done

lemma cfgSTD_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_cfg
     cfg_initial_configurations cfgSTD_step_relation cfg_marking_condition
     cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(simp add: cfgSTD_inst_lang_finite cfgSTD_inst_AX_unmarked_language_finite )
  done

lemma cfgSTD_inst_BF_Bra_OpLa_axioms: "
  BF_Bra_OpLa_axioms valid_cfg cfg_configurations
     cfg_initial_configurations cfg_step_labels cfgSTD_step_relation
     cfg_marking_condition cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: BF_Bra_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: cfgSTD_inst_Nonblockingness_branching_correspond1 )
  done

lemma cfgSTD_inst_AX_marked_configuration_effect_coincides_with_marked_effect: "
(\<forall>G. valid_cfg G \<longrightarrow>
         (\<forall>d. cfgSTD.derivation_initial
               G d \<longrightarrow>
              cfg_marked_effect G d =
              \<Union>{cfg_marked_configuration_effect G c |c.
                 (\<exists>i e. d i = Some (pair e c)) \<and>
                 c \<in> cfg_marking_configuration G}))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: cfg_marked_effect_def cfg_marking_configuration_def cfg_marked_configuration_effect_def)
  apply(rule antisym)
   apply(rename_tac G d)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d x e c i)(*strict*)
   apply(rule_tac
      x="{x}"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G d x e c i)(*strict*)
    apply(rule antisym)
     apply(rename_tac G d x e c i)(*strict*)
     apply(force)
    apply(rename_tac G d x e c i)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d x e c i xa)(*strict*)
    apply (metis liftB_inj)
   apply(rename_tac G d x e c i)(*strict*)
   apply(rule conjI)
    apply(rename_tac G d x e c i)(*strict*)
    apply(force)
   apply(rename_tac G d x e c i)(*strict*)
   apply(rule cfgSTD.belongs_configurations)
    apply(rename_tac G d x e c i)(*strict*)
    apply(rule cfgSTD.derivation_initial_belongs)
     apply(rename_tac G d x e c i)(*strict*)
     apply(force)
    apply(rename_tac G d x e c i)(*strict*)
    apply(force)
   apply(rename_tac G d x e c i)(*strict*)
   apply(force)
  apply(rename_tac G d)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d x c i e)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(force)
  done

lemma cfgSTD_inst_AX_unmarked_configuration_effect_coincides_with_unmarked_effect: "
  \<forall>G. valid_cfg G \<longrightarrow>
        (\<forall>d. cfgSTD.derivation_initial
              G d \<longrightarrow>
             cfg_unmarked_effect G d =
             \<Union>{cfg_unmarked_configuration_effect G c |c.
                \<exists>i e. d i = Some (pair e c)})"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(rule antisym)
   apply(rename_tac G d)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d x e c i z)(*strict*)
   apply(rule_tac
      x="cfg_unmarked_configuration_effect G c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G d x e c i z)(*strict*)
    apply(rule_tac
      x="c"
      in exI)
    apply(force)
   apply(rename_tac G d x e c i z)(*strict*)
   apply(simp add: cfg_unmarked_configuration_effect_def)
   apply(rule_tac
      x="z"
      in exI)
   apply(force)
  apply(rename_tac G d)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d x c i e)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule conjI)
   apply(rename_tac G d x c i e)(*strict*)
   apply(force)
  apply(rename_tac G d x c i e)(*strict*)
  apply(simp add: cfg_unmarked_configuration_effect_def)
  apply(force)
  done

interpretation "cfgSTD" : loc_cfg_2
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgSTD_step_relation"
  (* effects *)
  "cfg_effects"
  (* marking_condition *)
  "cfg_marking_condition"
  (* marked_effect *)
  "cfg_marked_effect"
  (* unmarked_effect *)
  "cfg_unmarked_effect"
  (* destinations *)
  "cfg_destination"
  (* get_destinations *)
  "cfg_get_destinations"
  (* decreasing *)
  "False"
  (* string_state *)
  "cfg_get_history"
  apply(simp add: LOCALE_DEFS_ALL LOCALE_DEFS_cfg)
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgSTD_inst_AX_step_relation_preserves_belongs )
  apply(simp add: cfgSTD_inst_ATS_String_State_Modification_axioms cfgSTD_inst_ATS_axioms )
  apply(simp add: cfgSTD_inst_ATS_Language_by_Finite_Derivations_axioms cfgSTD_inst_BF_Bra_OpLa_axioms)
  done

lemma cfgSTD_inst_BF_Bra_DetR_LaOp_axioms: "
  BF_Bra_DetR_LaOp_axioms valid_cfg cfg_configurations
     cfg_initial_configurations cfg_step_labels cfgSTD_step_relation
     cfg_marking_condition cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: BF_Bra_DetR_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: nonblockingness_language_def)
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac M dh n)(*strict*)
  apply(case_tac "dh n")
   apply(rename_tac M dh n)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac M dh n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac M dh n a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n option b)(*strict*)
  apply(case_tac b)
  apply(rename_tac M dh n option b cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n option cfg_conf)(*strict*)
  apply(rename_tac e w)
  apply(rename_tac M dh n e w)(*strict*)
  apply(subgoal_tac "\<exists>v. (maxTermPrefix w)@v \<in> cfgSTD.marked_language M")
   apply(rename_tac M dh n e w)(*strict*)
   prefer 2
   apply(subgoal_tac "(maxTermPrefix w) \<in> (prefix_closure (cfgSTD.marked_language M))")
    apply(rename_tac M dh n e w)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac M dh n e w c)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w)(*strict*)
   apply(subgoal_tac "(maxTermPrefix w) \<in> cfgSTD.unmarked_language M")
    apply(rename_tac M dh n e w)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w)(*strict*)
   apply(simp add: cfgSTD.unmarked_language_def)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac M dh n e w)(*strict*)
    prefer 2
    apply(simp add: cfgSTD.derivation_initial_def)
   apply(rename_tac M dh n e w)(*strict*)
   apply(simp add: cfg_unmarked_effect_def)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf=w\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac M dh n e w)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w)(*strict*)
   apply(rule maxTermPrefix_prefix)
  apply(rename_tac M dh n e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e w v)(*strict*)
  apply(thin_tac "cfgSTD.unmarked_language M \<subseteq> (prefix_closure (cfgSTD.marked_language M))")
  apply(simp add: cfgSTD.marked_language_def)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea c i)(*strict*)
  apply(subgoal_tac "case dh 0 of None \<Rightarrow> False | Some (pair a b) \<Rightarrow> b \<in> cfg_initial_configurations M \<and> a = None")
   apply(rename_tac M dh n e w v d ea c i)(*strict*)
   prefer 2
   apply(simp add: cfgSTD.derivation_initial_def)
  apply(rename_tac M dh n e w v d ea c i)(*strict*)
  apply(subgoal_tac "case_option False (case_derivation_configuration (\<lambda>a b. b \<in> cfg_initial_configurations M \<and> a = None)) (d 0)")
   apply(rename_tac M dh n e w v d ea c i)(*strict*)
   prefer 2
   apply(simp add: cfgSTD.derivation_initial_def)
  apply(rename_tac M dh n e w v d ea c i)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac M dh n e w v d ea c i)(*strict*)
   apply(clarsimp)
  apply(rename_tac M dh n e w v d ea c i a)(*strict*)
  apply(clarsimp)
  apply(case_tac "dh 0")
   apply(rename_tac M dh n e w v d ea c i a)(*strict*)
   apply(clarsimp)
  apply(rename_tac M dh n e w v d ea c i a aa)(*strict*)
  apply(clarsimp)
  apply(case_tac aa)
  apply(rename_tac M dh n e w v d ea c i a aa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea c i a b)(*strict*)
  apply(case_tac a)
  apply(rename_tac M dh n e w v d ea c i a b option ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea c i b ba)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea c i)(*strict*)
  apply(case_tac c)
  apply(rename_tac M dh n e w v d ea c i cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "n\<le>i")
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   prefer 2
   apply(case_tac "n>i")
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "dh i = d i")
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh i = Some (pair e1 c1) \<and> dh (Suc i) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation M c1 e2 c2")
      apply(rename_tac M dh n e w v d ea i)(*strict*)
      prefer 2
      apply(rule_tac
      m="n"
      in cfgSTD.step_detail_before_some_position)
        apply(rename_tac M dh n e w v d ea i)(*strict*)
        apply(simp add: cfgSTD.derivation_initial_def)
       apply(rename_tac M dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac M dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(clarsimp)
     apply(rename_tac M dh n e w v d ea i e2 c2)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac M dh n e w v d ea i e2 c2 l r)(*strict*)
     apply(simp only: setAConcat concat_asso setBConcat)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(rule sym)
    apply(rule_tac
      n="i"
      and m="n"
      and ?d1.0="d"
      and ?d2.0="dh"
      and x="0"
      and y="0"
      in cfgSTD.is_forward_deterministic_accessible_derivations_coincide)
             apply(rename_tac M dh n e w v d ea i)(*strict*)
             apply(force)
            apply(rename_tac M dh n e w v d ea i)(*strict*)
            apply(force)
           apply(rename_tac M dh n e w v d ea i)(*strict*)
           apply(force)
          apply(rename_tac M dh n e w v d ea i)(*strict*)
          apply(force)
         apply(rename_tac M dh n e w v d ea i)(*strict*)
         apply(force)
        apply(rename_tac M dh n e w v d ea i)(*strict*)
        apply(force)
       apply(rename_tac M dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac M dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(rule_tac
      x="derivation_drop (derivation_take d i) n"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(rule_tac
      m="i-n"
      in cfgSTD.derivation_drop_preserves_derivation_prime)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(rule cfgSTD.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   prefer 2
   apply(rule_tac
      m="i"
      in cfgSTD.pre_some_position_is_some_position)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(blast)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(blast)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(rule_tac cfgSTD.derivation_drop_preserves_belongs)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(rule cfgSTD.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(rule_tac cfgSTD.derivation_take_preserves_belongs)
    apply(rule cfgSTD.derivation_initial_belongs)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(simp add: cfgSTD.derivation_initial_def)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
   apply(simp add: derivation_take_def)
   apply(force)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(rule_tac
      x="i-n"
      in exI)
   apply(simp add: maximum_of_domain_def derivation_drop_def derivation_take_def)
   apply(clarsimp)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "dh n = d n")
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule_tac
      n="n"
      and m="n"
      and ?d1.0="d"
      and ?d2.0="dh"
      and x="0"
      and y="0"
      in cfgSTD.is_forward_deterministic_accessible_derivations_coincide)
            apply(rename_tac M dh n e w v d ea i)(*strict*)
            apply(force)
           apply(rename_tac M dh n e w v d ea i)(*strict*)
           apply(force)
          apply(rename_tac M dh n e w v d ea i)(*strict*)
          apply(force)
         apply(rename_tac M dh n e w v d ea i)(*strict*)
         apply(force)
        apply(rename_tac M dh n e w v d ea i)(*strict*)
        apply(force)
       apply(rename_tac M dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac M dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(simp add: derivation_append_fit_def derivation_drop_def derivation_take_def)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(subgoal_tac "i=ia")
   apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
   prefer 2
   apply(case_tac "i=ia")
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
   apply(case_tac "i<ia")
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation M c1 e2 c2")
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     prefer 2
     apply(rule_tac
      m="ia"
      in cfgSTD.step_detail_before_some_position)
       apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
       apply(simp add: cfgSTD.derivation_initial_def)
      apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
      apply(force)
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    apply(clarsimp)
    apply(rename_tac M dh n e w v d ea i ia eb c e2 c2)(*strict*)
    apply(simp add: cfgSTD_step_relation_def)
    apply(clarsimp)
    apply(rename_tac M dh n e w v d ea i ia eb c e2 c2 l r)(*strict*)
    apply(simp only: setAConcat concat_asso setBConcat)
    apply(force)
   apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d ia = Some (pair e1 c1) \<and> d (Suc ia) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation M c1 e2 c2")
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    prefer 2
    apply(rule_tac
      m="i"
      in cfgSTD.step_detail_before_some_position)
      apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
      apply(simp add: cfgSTD.derivation_initial_def)
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e w v d ea i ia eb c e2 c2)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac M dh n e w v d ea i ia eb c e2 c2 l r)(*strict*)
   apply(simp only: setAConcat concat_asso setBConcat)
   apply(force)
  apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea ia)(*strict*)
  apply(rule_tac
      x="ia"
      in exI)
  apply(simp add: derivation_append_def derivation_drop_def derivation_take_def)
  apply(clarsimp)
  done

interpretation "cfgSTD" : loc_cfg_3
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgSTD_step_relation"
  (* effects *)
  "cfg_effects"
  (* marking_condition *)
  "cfg_marking_condition"
  (* marked_effect *)
  "cfg_marked_effect"
  (* unmarked_effect *)
  "cfg_unmarked_effect"
  (* destinations *)
  "cfg_destination"
  (* get_destinations *)
  "cfg_get_destinations"
  (* decreasing *)
  "False"
  (* string_state *)
  "cfg_get_history"
  apply(simp add: LOCALE_DEFS_ALL LOCALE_DEFS_cfg)
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgSTD_inst_AX_step_relation_preserves_belongs cfgSTD_inst_ATS_String_State_Modification_axioms cfgSTD_inst_ATS_axioms cfgSTD_inst_ATS_Language_by_Finite_Derivations_axioms cfgSTD_inst_BF_Bra_OpLa_axioms cfgSTD_inst_BF_Bra_DetR_LaOp_axioms )
  done

lemma CFG_derivation_initial_pos0: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_initial G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>)"
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(case_tac "d 0")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  done

lemma CFG_Nonblockingness_is_lang_notempty: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD.marked_language G \<noteq> {}"
  apply(simp add: cfgSTD.marked_language_def cfgSTD.Nonblockingness_branching_def)
  apply(erule_tac
      x="der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in allE)
  apply(erule impE)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(rule conjI)
    apply(simp add: cfgSTD.der1_is_derivation)
   apply(simp add: der1_def)
   apply(simp add: cfg_initial_configurations_def)
   apply(simp add: cfg_configurations_def)
   apply(rule cfg_initial_in_nonterms)
   apply(force)
  apply(erule_tac
      x="0"
      in allE)
  apply(erule impE)
   apply(rule der1_maximum_of_domain)
  apply(clarsimp)
  apply(rename_tac dc n')(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac dc n' i e c)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(simp add: cfg_marked_effect_def)
  apply(case_tac c)
  apply(rename_tac dc n' i e c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac dc n' i e cfg_confa)(*strict*)
  apply(rename_tac x)
  apply(rename_tac dc n' i e x)(*strict*)
  apply(rule_tac
      x="filterB x"
      in exI)
  apply(rule_tac
      x="derivation_append (der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>) dc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac dc n' i e x)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac dc n' i e x)(*strict*)
     apply(rule cfgSTD.der1_is_derivation)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(force)
   apply(rename_tac dc n' i e x)(*strict*)
   apply(simp add: der1_def)
   apply(case_tac "dc 0")
    apply(rename_tac dc n' i e x)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgSTD.derivation_def)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
   apply(rename_tac dc n' i e x a)(*strict*)
   apply(case_tac "dc 0")
    apply(rename_tac dc n' i e x a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dc n' i e x a aa)(*strict*)
   apply(simp add: cfgSTD.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(rename_tac dc n' i e x a)(*strict*)
   apply(case_tac a)
   apply(rename_tac dc n' i e x a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dc n' i e x option b)(*strict*)
   apply(case_tac option)
    apply(rename_tac dc n' i e x option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac dc n' i e x b)(*strict*)
    apply(simp add: derivation_append_fit_def)
   apply(rename_tac dc n' i e x option b a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dc n' i e x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dc n' i e x)(*strict*)
   apply(simp add: derivation_append_def)
   apply(case_tac i)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(clarsimp)
    apply(rename_tac dc n' e x)(*strict*)
    apply(rule_tac
      x="e"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="\<lparr>cfg_conf=x\<rparr>"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac dc n' e x)(*strict*)
     apply(rule_tac
      x="0"
      in exI)
     apply(clarsimp)
    apply(rename_tac dc n' e x)(*strict*)
    apply(rule liftBDeConv2)
    apply(force)
   apply(rename_tac dc n' i e x nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac dc n' e x nat)(*strict*)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf=x\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac dc n' e x nat)(*strict*)
    apply(rule_tac
      x="Suc nat"
      in exI)
    apply(clarsimp)
   apply(rename_tac dc n' e x nat)(*strict*)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac dc n' i e x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dc n' i e x)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(rule cfgSTD.derivation_append_preserves_derivation)
      apply(rename_tac dc n' i e x)(*strict*)
      apply(rule cfgSTD.der1_is_derivation)
     apply(rename_tac dc n' i e x)(*strict*)
     apply(force)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(simp add: der1_def)
    apply(case_tac "dc 0")
     apply(rename_tac dc n' i e x)(*strict*)
     apply(clarsimp)
     apply(simp add: cfgSTD.derivation_def)
     apply(erule_tac
      x="0"
      in allE)
     apply(clarsimp)
    apply(rename_tac dc n' i e x a)(*strict*)
    apply(case_tac "dc 0")
     apply(rename_tac dc n' i e x a)(*strict*)
     apply(clarsimp)
    apply(rename_tac dc n' i e x a aa)(*strict*)
    apply(simp add: cfgSTD.derivation_def)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
    apply(rename_tac dc n' i e x a)(*strict*)
    apply(case_tac a)
    apply(rename_tac dc n' i e x a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac dc n' i e x option b)(*strict*)
    apply(case_tac option)
     apply(rename_tac dc n' i e x option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac dc n' i e x b)(*strict*)
     apply(simp add: derivation_append_fit_def)
    apply(rename_tac dc n' i e x option b a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dc n' i e x)(*strict*)
   apply(simp add: derivation_append_def der1_def)
   apply(simp add: cfg_initial_configurations_def)
   apply(simp add: cfg_configurations_def)
   apply(rule cfg_initial_in_nonterms)
   apply(force)
  apply(rename_tac dc n' i e x)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(clarsimp)
  done

lemma cfg_no_step_without_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> setA (cfg_conf c) = {}
  \<Longrightarrow> d (Suc n) = None"
  apply(case_tac "d (Suc n)")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation G c1 e2 c2")
   apply(rename_tac option b)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac option b)(*strict*)
     apply(force)
    apply(rename_tac option b)(*strict*)
    apply(force)
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b e2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac b e2 l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

definition cfgSTD_accessible_productions :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event)cfg_step_label set"
  where
    "cfgSTD_accessible_productions G \<equiv>
  {p \<in> cfg_productions G.
      dest_production p \<in> cfgSTD.get_accessible_destinations G}"

lemma cfgSTD_first_with_takekw: "
  take k w \<in> cfgSTD_first G' k (liftB (take k w))"
  apply(simp add: cfgSTD_first_def)
  apply(rule inMap)
  apply(clarsimp)
  apply(rule_tac
      x="take k w"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB (take k w)\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rule cfgSTD.der1_is_derivation)
  apply(simp add: der1_def maximum_of_domain_def)
  done

lemma CFG_preserves_partial_belongs: "
  valid_cfg G
  \<Longrightarrow> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> cfgSTD.derivation G' d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = w @ liftB z\<rparr>)
  \<Longrightarrow> (\<And>p. p\<in> cfg_productions G' \<Longrightarrow> prod_lhs p \<in> cfg_nonterminals G \<Longrightarrow> p \<in> cfg_productions G)
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>v. set v \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<and> (case e of None \<Rightarrow> True|Some e' \<Rightarrow> e' \<in> cfg_productions G)
  \<and> c=\<lparr>cfg_conf = v @ liftB z\<rparr>"
  apply(induct n arbitrary: e v c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation G' c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 l r)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac n c e1 e2 c1 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 l r v)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n e1 e2 l r v prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A x)
  apply(rename_tac n e1 e2 l r v A x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 l r v A x)(*strict*)
  apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = x\<rparr>"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n e1 l r v A x)(*strict*)
   apply(force)
  apply(rename_tac n e1 l r v A x)(*strict*)
  apply(subgoal_tac "suffix r (liftB z)")
   apply(rename_tac n e1 l r v A x)(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac n e1 l A x c)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac n e1 l A x c)(*strict*)
    apply (metis suffixes_setA_2 suffixes_intro2 two_elements_construct_domain_setA two_elements_construct_domain_append set_concat_subset)
   apply(rename_tac n e1 l A x c)(*strict*)
   apply(rule conjI)
    apply(rename_tac n e1 l A x c)(*strict*)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(rename_tac n e1 l A x c xa)(*strict*)
    apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = x\<rparr>"
      in ballE)
     apply(rename_tac n e1 l A x c xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n e1 l A x c xa)(*strict*)
    apply(clarsimp)
    apply (metis SetxBiElem_check_vs_set_two_elements_construct_domain_check set_rev_mp)
   apply(rename_tac n e1 l A x c)(*strict*)
   apply(force)
  apply(rename_tac n e1 l r v A x)(*strict*)
  apply(subgoal_tac "prefix v (l@[teA A]) \<or> prefix (l@[teA A]) v")
   apply(rename_tac n e1 l r v A x)(*strict*)
   apply(erule disjE)
    apply(rename_tac n e1 l r v A x)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac n e1 l r v A x c)(*strict*)
    apply(simp add: suffix_def)
    apply(case_tac c)
     apply(rename_tac n e1 l r v A x c)(*strict*)
     apply(clarsimp)
    apply(rename_tac n e1 l r v A x c a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac n e1 l r v A x c a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac n e1 l r v A x c a list)(*strict*)
    apply(thin_tac "c=a#list")
    apply(clarsimp)
    apply(rename_tac n e1 r v A x w')(*strict*)
    apply (metis setA_liftB elemInsetA ex_in_conv)
   apply(rename_tac n e1 l r v A x)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n e1 l A x c)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac n e1 l r v A x)(*strict*)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

corollary cfg_dependency_between_Nonblockingnessness_properties1STD: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> nonblockingness_language (cfgSTD.unmarked_language G) (cfgSTD.marked_language G)"
  apply(simp add: nonblockingness_language_def)
  apply (metis nonblockingness_language_def cfgSTD.AX_BF_Bra_OpLa)
  done

corollary cfg_dependency_between_Nonblockingnessness_properties1: "
  valid_cfg G
  \<Longrightarrow> nonblockingness_language (cfgSTD.unmarked_language G) (cfgSTD.marked_language G)
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G"
  (*
counterexample:
  S \<longrightarrow> aA
  S \<longrightarrow> ab
marked={[a,b]}
unmarked={[],[a],[a,b]}
*)
  oops

lemma cfgSTD_no_nonterminal_at_end_in_marking_condition: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> cfg_marking_condition G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> cfg_conf c=w
  \<Longrightarrow> setA w={}"
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(rename_tac i ea ca)(*strict*)
  apply(case_tac "i=n")
   apply(rename_tac i ea ca)(*strict*)
   apply(force)
  apply(rename_tac i ea ca)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and n="i"
      and m="n"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac i ea ca)(*strict*)
     apply(force)
    apply(rename_tac i ea ca)(*strict*)
    apply(force)
   apply(rename_tac i ea ca)(*strict*)
   apply (metis (mono_tags) cfgSTD.allPreMaxDomSome_prime le_antisym not_less_eq_eq option.distinct(1))
  apply(rename_tac i ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea ca e2 c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i ea ca e2 c2 l r)(*strict*)
  apply(case_tac ca)
  apply(rename_tac i ea ca e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea e2 c2 l r)(*strict*)
  apply (metis elemInsetA empty_iff)
  done

definition cfgSTD_accessible_nonterminals_ALT :: "
  ('nonterminal,'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgSTD_accessible_nonterminals_ALT G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n c.
      cfgSTD.derivation_initial G d
      \<and> get_configuration (d n) = Some c
      \<and> (\<exists>w1 w2. cfg_conf c = w1 @ teA A # w2)}"

definition cfgSTD_accessible_nonterminals_ALT_ALT :: "
  ('nonterminal,'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgSTD_accessible_nonterminals_ALT_ALT G \<equiv>
  {A. \<exists>d n e w1 w2.
      cfgSTD.derivation_initial G d
      \<and> d n = Some (pair e \<lparr>cfg_conf = w1 @ teA A # w2 \<rparr>)}"

lemma cfgSTD_accessible_nonterminals_ALT_ALT_vs_cfgSTD_accessible_nonterminals_ALT: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_accessible_nonterminals_ALT_ALT G = cfgSTD_accessible_nonterminals_ALT G"
  apply(simp add: cfgSTD_accessible_nonterminals_ALT_ALT_def cfgSTD_accessible_nonterminals_ALT_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x d n e w1 w2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x d n e w1 w2)(*strict*)
    prefer 2
    apply(rule cfgSTD.belongs_configurations)
     apply(rename_tac x d n e w1 w2)(*strict*)
     apply(rule cfgSTD.derivation_initial_belongs)
      apply(rename_tac x d n e w1 w2)(*strict*)
      apply(force)
     apply(rename_tac x d n e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac x d n e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac x d n e w1 w2)(*strict*)
   apply(simp add: cfg_configurations_def setAConcat)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(force)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(case_tac "d n")
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(force)
  apply(rename_tac x d n c w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d n c w1 w2 a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 option)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n c w1 w2 option cfg_confa)(*strict*)
  apply(force)
  done

definition cfgSTD_Nonblockingness_nonterminals_ALT2 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgSTD_Nonblockingness_nonterminals_ALT2 G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n e w.
      cfgSTD.derivation G d
      \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)
      \<and> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)}"

lemma CFGSTD_no_step_without_nonterms: "
  setA (cfg_conf ca) = {}
  \<Longrightarrow> \<forall>e c'. \<not> cfgSTD_step_relation G' ca e c'"
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e c' l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma CFGSTD_Nonblockingness_to_elimination: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> cfgSTD.belongs G d
  \<Longrightarrow> cfgSTD.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w1@w2@w3\<rparr>)
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> \<exists>d' n' w e. maximum_of_domain d' n' \<and> cfgSTD.derivation G d' \<and> cfgSTD.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w2\<rparr>) \<and> d' n' = Some (pair e \<lparr>cfg_conf=w\<rparr>) \<and> setA w = {}"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule cfgSTD.some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(erule_tac
      x="d"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rename_tac c dc x)(*strict*)
  apply(simp add: derivation_append_fit_def)
  apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
   apply(rename_tac c dc x)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac c dc x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>cfg_conf = w1 @ w2 @ w3\<rparr> \<in> cfg_configurations G")
   apply(rename_tac c dc x)(*strict*)
   prefer 2
   apply(simp add: cfgSTD.belongs_def)
   apply(erule_tac
      x="n"
      and P="\<lambda>i. case d i of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> cfg_step_labels G) \<and> c \<in> cfg_configurations G"
      in allE)
   apply(rename_tac c dc x)(*strict*)
   apply(clarsimp)
  apply(rename_tac c dc x)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac c dc x i ea ca)(*strict*)
  apply(case_tac "i<n")
   apply(rename_tac c dc x i ea ca)(*strict*)
   apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
    apply(rename_tac c dc x i ea ca)(*strict*)
    prefer 2
    apply(rule_tac
      M="G"
      in cfgSTD.some_position_has_details_before_max_dom)
      apply(rename_tac c dc x i ea ca)(*strict*)
      apply(blast)
     apply(rename_tac c dc x i ea ca)(*strict*)
     apply(blast)
    apply(rename_tac c dc x i ea ca)(*strict*)
    apply(arith)
   apply(rename_tac c dc x i ea ca)(*strict*)
   apply(erule exE)+
   apply(rename_tac c dc x i ea ca eaa cb)(*strict*)
   apply(simp add: cfg_marking_configuration_def)
   apply(clarsimp)
   apply(rule_tac
      m="i"
      in cfgSTD.noDeadEndBeforeMaxDom)
       apply(rename_tac c dc x i ea ca eaa cb)(*strict*)
       apply(force)
      apply(rename_tac c dc x i ea ca eaa cb)(*strict*)
      apply(force)
     apply(rename_tac c dc x i ea ca eaa cb)(*strict*)
     apply(force)
    apply(rename_tac c dc x i ea ca eaa cb)(*strict*)
    apply(force)
   apply(rename_tac c dc x i ea ca eaa cb)(*strict*)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
   apply(rename_tac c dc x i ea ca e2 c2)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac c dc x i ea ca e2 c2 l r)(*strict*)
   apply(subgoal_tac "prod_lhs e2 \<in> setA (l @ teA (prod_lhs e2) # r)")
    apply(rename_tac c dc x i ea ca e2 c2 l r)(*strict*)
    apply(force)
   apply(rename_tac c dc x i ea ca e2 c2 l r)(*strict*)
   apply(rule elemInsetA)
  apply(rename_tac c dc x i ea ca)(*strict*)
  apply(case_tac "i=n")
   apply(rename_tac c dc x i ea ca)(*strict*)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = w2\<rparr>"
      in exI)
   apply(rule_tac
      x = "0"
      in exI)
   apply(rule conjI)
    apply(rename_tac c dc x i ea ca)(*strict*)
    apply(simp add: der1_maximum_of_domain)
   apply(rename_tac c dc x i ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac c dc x i ea ca)(*strict*)
    apply(rule cfgSTD.der1_is_derivation)
   apply(rename_tac c dc x i ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac c dc x i ea ca)(*strict*)
    apply(rule cfgSTD.der1_belongs)
    apply(simp add: cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac c dc x ea ca)(*strict*)
    apply(simp only: setAConcat setBConcat concat_asso)
    apply(force)
   apply(rename_tac c dc x i ea ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac c dc x ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac c dc x ea ca)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac c dc x ea ca)(*strict*)
   apply(simp add: der1_def)
   apply(simp add: cfg_marking_configuration_def derivation_append_def)
   apply(clarsimp)
   apply(rename_tac c dc x)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(force)
  apply(rename_tac c dc x i ea ca)(*strict*)
  apply(subgoal_tac "i>n")
   apply(rename_tac c dc x i ea ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c dc x i ea ca)(*strict*)
  apply(thin_tac "i\<noteq>n")
  apply(thin_tac "\<not>i<n")
  apply(case_tac ca)
  apply(rename_tac c dc x i ea ca cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac c dc x i ea cfg_conf)(*strict*)
  apply(rename_tac w')
  apply(rename_tac c dc x i ea w')(*strict*)
  apply(subgoal_tac "maximum_of_domain dc (i-n)")
   apply(rename_tac c dc x i ea w')(*strict*)
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(simp add: derivation_append_def)
   apply(simp add: cfg_marking_configuration_def)
   apply(clarsimp)
   apply(rename_tac c dc x i ea w' y)(*strict*)
   apply(case_tac "dc (Suc (i-n))")
    apply(rename_tac c dc x i ea w' y)(*strict*)
    apply(force)
   apply(rename_tac c dc x i ea w' y a)(*strict*)
   apply(subgoal_tac "\<forall>e c'. \<not> cfgSTD_step_relation G \<lparr>cfg_conf = w'\<rparr> e c'")
    apply(rename_tac c dc x i ea w' y a)(*strict*)
    prefer 2
    apply(rule CFGSTD_no_step_without_nonterms)
    apply(force)
   apply(rename_tac c dc x i ea w' y a)(*strict*)
   apply(subgoal_tac "\<exists>e c. dc (Suc (i - n)) = Some (pair (Some e) c)")
    apply(rename_tac c dc x i ea w' y a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(i-n)"
      in cfgSTD.pre_some_position_is_some_position_prime)
       apply(rename_tac c dc x i ea w' y a)(*strict*)
       apply(force)
      apply(rename_tac c dc x i ea w' y a)(*strict*)
      apply(force)
     apply(rename_tac c dc x i ea w' y a)(*strict*)
     apply(force)
    apply(rename_tac c dc x i ea w' y a)(*strict*)
    apply(force)
   apply(rename_tac c dc x i ea w' y a)(*strict*)
   apply(clarsimp)
   apply(rename_tac c dc x i ea w' y eaa ca)(*strict*)
   apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w'\<rparr> eaa ca")
    apply(rename_tac c dc x i ea w' y eaa ca)(*strict*)
    prefer 2
    apply(rule_tac
      d="dc"
      and n="(i-n)"
      in cfgSTD.position_change_due_to_step_relation)
      apply(rename_tac c dc x i ea w' y eaa ca)(*strict*)
      apply(blast)
     apply(rename_tac c dc x i ea w' y eaa ca)(*strict*)
     apply(blast)
    apply(rename_tac c dc x i ea w' y eaa ca)(*strict*)
    apply(blast)
   apply(rename_tac c dc x i ea w' y eaa ca)(*strict*)
   apply(erule_tac
      x="eaa"
      in allE)
   apply(erule_tac
      x="ca"
      in allE)
   apply(force)
  apply(rename_tac c dc x i ea w')(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2@w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=(i-n)")
   apply(rename_tac c dc x i ea w')(*strict*)
   prefer 2
   apply(rule_tac
      d="dc"
      in derivationCanBeDecomposed2)
    apply(rename_tac c dc x i ea w')(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(rule_tac
      x="i-n"
      in exI)
    apply(rule conjI)
     apply(rename_tac c dc x i ea w')(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac c dc x i ea w')(*strict*)
    apply(rule_tac
      x="pair ea \<lparr>cfg_conf=w'\<rparr>"
      in exI)
    apply(clarsimp)
    apply(simp add: derivation_append_def)
   apply(rename_tac c dc x i ea w')(*strict*)
   apply(clarsimp)
  apply(rename_tac c dc x i ea w')(*strict*)
  apply(clarsimp)
  apply(rename_tac c dc x i ea d1 d2 w1' w2' n1 n2)(*strict*)
  apply(thin_tac "cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rename_tac w' n1 n')
  apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n'")
   apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in derivationCanBeDecomposed2)
    apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
   apply(force)
  apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
  apply(clarsimp)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(thin_tac "cfgSTD.derivation_from_to G d2a {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(thin_tac "cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2 @ w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'nonterminal @ w2'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(rule_tac
      x="d1a"
      in exI)
  apply(rule_tac
      x="n1a"
      in exI)
  apply(clarsimp)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
  apply(case_tac "d1a 0")
   apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
  apply(rule conjI)
   apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
      apply(force)
     apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
     apply(force)
    apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(simp only: setAConcat setBConcat concat_asso)
    apply(force)
   apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
   apply(force)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
  apply(rule_tac
      x="w1'nonterminal"
      in exI)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(simp only: setAConcat setBConcat concat_asso)
  apply(clarsimp)
  apply(subgoal_tac "na=n1a")
   apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
   apply(force)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
  apply(rule_tac
      d="d1a"
      in cfgSTD.maximum_of_domainUnique)
    apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
    apply(force)
   apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
   apply(force)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  done

lemma cfgSTD_Nonblockingness_nonterminals_ALT2_vs_cfgSTD_Nonblockingness_nonterminals_ALT: "
  cfgSTD_Nonblockingness_nonterminals_ALT2 G = cfgSTD_Nonblockingness_nonterminals_ALT G"
  apply(rule antisym)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_ALT2_def cfgSTD_Nonblockingness_nonterminals_ALT_def)
   apply(clarsimp)
   apply(rename_tac x d n e w)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(rule setA_liftB)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_ALT2_def cfgSTD_Nonblockingness_nonterminals_ALT_def)
  apply(clarsimp)
  apply(rename_tac x d n e w')(*strict*)
  apply(rule_tac
      x="d"
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

lemma cfgSTD_Nonblockingness_branching_implies_cfgSTD_accessible_nonterminals_ALT_contained_in_cfgSTD_Nonblockingness_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD_accessible_nonterminals_ALT G \<subseteq> cfgSTD_Nonblockingness_nonterminals G"
  apply(simp add: cfgSTD_accessible_nonterminals_ALT_def)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d n c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2)(*strict*)
  apply(thin_tac "x \<in> cfg_nonterminals G")
  apply(case_tac "d n")
   apply(rename_tac x d n w1 w2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac x d n w1 w2 a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac x d n w1 w2 a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n w1 w2 option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgSTD.derivation_initial G d \<and> maximum_of_domain d n \<and> d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # w2\<rparr>)")
   apply(rename_tac x d n w1 w2 e)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d n"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply (metis cfgSTD.derivation_take_preserves_derivation_initial)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply (metis maximum_of_domain_derivation_take not_None_eq)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(thin_tac "cfgSTD.derivation_initial G d")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac x n w1 w2 e d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x n w1 w2 e d)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and ?w1.0="w1"
      and ?w2.0="[teA x]"
      and ?w3.0="w2"
      in CFGSTD_Nonblockingness_to_elimination)
         apply(rename_tac x n w1 w2 e d)(*strict*)
         apply(force)
        apply(rename_tac x n w1 w2 e d)(*strict*)
        apply(simp add: cfgSTD.derivation_initial_def)
       apply(rename_tac x n w1 w2 e d)(*strict*)
       apply(rule cfgSTD.derivation_initial_belongs)
        apply(rename_tac x n w1 w2 e d)(*strict*)
        apply(force)
       apply(rename_tac x n w1 w2 e d)(*strict*)
       apply(force)
      apply(rename_tac x n w1 w2 e d)(*strict*)
      apply(force)
     apply(rename_tac x n w1 w2 e d)(*strict*)
     apply(force)
    apply(rename_tac x n w1 w2 e d)(*strict*)
    apply(force)
   apply(rename_tac x n w1 w2 e d)(*strict*)
   apply(force)
  apply(rename_tac x n w1 w2 e d)(*strict*)
  apply(thin_tac "cfgSTD.Nonblockingness_branching G")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "cfgSTD.derivation_initial G d")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac x d' n' w e)(*strict*)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(rule conjI)
   apply(rename_tac x d' n' w e)(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf = [teA x]\<rparr> \<in> cfg_configurations G")
    apply(rename_tac x d' n' w e)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac x d' n' w e)(*strict*)
   apply (metis cfgSTD.belongs_configurations)
  apply(rename_tac x d' n' w e)(*strict*)
  apply(rule_tac
      x="derivation_take d' n'"
      in exI)
  apply(subgoal_tac "\<exists>wx. liftB wx = w")
   apply(rename_tac x d' n' w e)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB w"
      in exI)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac x d' n' w e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d' n' e wx)(*strict*)
  apply(rule_tac
      x="liftB wx"
      in exI)
  apply(clarsimp)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(rule conjI)
   apply(rename_tac x d' n' e wx)(*strict*)
   apply(rule cfgSTD.derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac x d' n' e wx)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d' n' e wx)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac x d' n' e wx)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d' n' e wx)(*strict*)
   apply(rule cfgSTD.derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac x d' n' e wx)(*strict*)
  apply(rule_tac
      x="n'"
      in exI)
  apply(simp add: derivation_take_def)
  done

definition cfgSTD_accessible_nonterminals :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgSTD_accessible_nonterminals G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n c.
      cfgSTD.derivation_initial G d
      \<and> get_configuration (d n) = Some c
      \<and> A \<in> setA (cfg_conf c)}"

lemma CFG_CFGAC_has_cfgSTD_accessible_productions: "
  valid_cfg G
  \<Longrightarrow> N = cfgSTD_accessible_nonterminals G
  \<Longrightarrow> P = {p \<in> cfg_productions G. prod_lhs p \<in> N}
  \<Longrightarrow> P = cfgSTD_accessible_productions G"
  apply(simp add: cfgSTD_accessible_productions_def cfgSTD_accessible_nonterminals_def cfgSTD.get_accessible_destinations_def)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x d n c)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d n c)(*strict*)
    apply(simp add: cfg_destination_def)
   apply(rename_tac x d n c)(*strict*)
   apply(case_tac "d n")
    apply(rename_tac x d n c)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac x d n c a)(*strict*)
   apply(case_tac a)
   apply(rename_tac x d n c a option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac x d n c option)(*strict*)
   apply(rename_tac e)
   apply(rename_tac x d n c e)(*strict*)
   apply(case_tac c)
   apply(rename_tac x d n c e cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n e cfg_conf)(*strict*)
   apply(rename_tac w)
   apply(rename_tac x d n e w)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1@[teA (prod_lhs x)]@w2=w")
    apply(rename_tac x d n e w)(*strict*)
    prefer 2
    apply(rule setA_decomp)
    apply(force)
   apply(rename_tac x d n e w)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n e w1 w2)(*strict*)
   apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = w1 @ teA (prod_lhs x) # w2\<rparr> x \<lparr>cfg_conf = w1 @ (prod_rhs x) @ w2\<rparr>) n"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d n e w1 w2)(*strict*)
    apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
      apply(rename_tac x d n e w1 w2)(*strict*)
      apply(force)
     apply(rename_tac x d n e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac x d n e w1 w2)(*strict*)
    apply(rule cfgSTD.derivation_append_preserves_derivation)
      apply(rename_tac x d n e w1 w2)(*strict*)
      apply(simp add: cfgSTD.derivation_initial_def)
     apply(rename_tac x d n e w1 w2)(*strict*)
     apply(rule cfgSTD.der2_is_derivation)
     apply(simp add: cfgSTD_step_relation_def)
     apply(force)
    apply(rename_tac x d n e w1 w2)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac x d n e w1 w2)(*strict*)
   apply(rule_tac
      x="Suc n"
      in exI)
   apply(simp add: der2_def derivation_append_def)
   apply(simp add: setAConcat cfg_get_destinations_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d i e c)(*strict*)
   apply(simp add: valid_cfg_def)
  apply(rename_tac x d i e c)(*strict*)
  apply(simp add: cfg_destination_def cfg_get_destinations_def)
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
      x="d"
      in exI)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac i)
   apply(rename_tac d i c a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c a)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac d c a)(*strict*)
    apply(force)
   apply(rename_tac d c a)(*strict*)
   apply (metis cfgSTD.derivation_initial_is_derivation cfgSTD.initialNotEdgeSome_prime)
  apply(rename_tac d i c a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c a nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation G c1 e2 c2")
   apply(rename_tac d c a nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac d c a nat)(*strict*)
     apply(rule cfgSTD.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d c a nat)(*strict*)
    apply(force)
   apply(rename_tac d c a nat)(*strict*)
   apply(force)
  apply(rename_tac d c a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c a nat e1 c1)(*strict*)
  apply(rule_tac
      x="nat"
      in exI)
  apply(clarsimp)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d c a nat e1 c1 l r)(*strict*)
  apply (metis elemInsetA)
  done

lemma derivationCanBeDecomposed2_with_labels: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> \<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1 + n2 = n \<and> set (get_labels d n) = set (get_labels d1 n1) \<union>set (get_labels d2 n2)"
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2 w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>} \<and> maximum_of_domain d n \<longrightarrow> (\<exists>d1 d2 w1' w2' n1 n2. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n \<and> set(get_labels d n)=set(get_labels d1 n1)\<union>set(get_labels d2 n2))")
   apply(blast)
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}")
  apply(thin_tac "maximum_of_domain d n")
  apply(rule allI)
  apply(rename_tac n)(*strict*)
  apply(induct_tac n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2 w')(*strict*)
   apply(case_tac "w1@w2\<noteq>w'")
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(subgoal_tac "0\<noteq>(0::nat)")
     apply(rename_tac d w1 w2 w')(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(rule cfgSTD.modifying_derivation_is_not_empty)
      apply(rename_tac d w1 w2 w')(*strict*)
      apply(blast)
     apply(rename_tac d w1 w2 w')(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 w')(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2 w')(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = w1\<rparr>"
      in exI)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = w2\<rparr>"
      in exI)
   apply(rule_tac
      x="w1"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(rule cfgSTD.der1_is_derivation)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(rule cfgSTD.der1_is_derivation)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="w2"
      in exI)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule cfgSTD.der1_is_derivation)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule cfgSTD.der1_is_derivation)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="nat_seq (Suc 0) 0"
      and s="[]"
      in ssubst)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac n na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1@w2\<rparr>}. d 0 = Some x")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac na d w1 w2 w')(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2 w')(*strict*)
   apply(arith)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e. d (Suc na) = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac na d w1 w2 w')(*strict*)
   apply(clarsimp)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 w' e ea c)(*strict*)
  apply(case_tac c)
  apply(rename_tac na d w1 w2 w' e ea c cfg_conf)(*strict*)
  apply(rename_tac cv)
  apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
  apply(erule_tac
      x="derivation_drop d (Suc 0)"
      in allE)
  apply(case_tac "\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv")
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = cv")
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    prefer 2
    apply(rule alt_case)
     apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_def)
     apply(clarsimp)
     apply(rename_tac na d w1 w2 w' e ea cv)(*strict*)
     apply(erule_tac
      x="Suc 0"
      in allE)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   apply(thin_tac "\<not> (\<exists>c'. cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv)")
   apply(clarsimp)
   apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
   apply(erule_tac
      x="w1"
      in allE)
   apply(erule_tac
      x="c'"
      in allE)
   apply(erule_tac
      x="w'"
      in allE)
   apply(erule impE)
    apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
    apply(rule conjI)
     apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
     apply(rule_tac
      m = "na"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
        apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
        apply(blast)
       apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
       apply(rule_tac
      s = "Suc na"
      in ssubst)
        apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
        apply(arith)
       apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
       apply(blast)
      apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
      apply(blast)
     apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
    apply(rule derivation_drop_preserves_generates_maximum_of_domain)
    apply(blast)
   apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="d1"
      in exI)
   apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr>) d2 (Suc 0)"
      in exI)
   apply(rule_tac
      x="w1'"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(force)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      x="w2'"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
     apply(rule cfgSTD.derivation_append_preserves_derivation)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(force)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
     apply(simp add: der2_def)
     apply(case_tac "d2 0")
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(clarsimp)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
     apply(rule cfgSTD.derivation_append_preserves_derivation)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(force)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
     apply(simp add: der2_def)
     apply(case_tac "d2 0")
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(clarsimp)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(rule_tac
      x="Suc nb"
      in exI)
    apply(simp add: derivation_append_def der2_def)
    apply(clarsimp)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="n1"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="Suc n2"
      and s="Suc 0+n2"
      in ssubst)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(rule_tac concat_has_max_dom)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     apply(rule der2_maximum_of_domain)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(force)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="get_labels d (Suc (n1 + n2))"
      and s="Some e#get_labels (derivation_drop d (Suc 0)) ((n1 + n2))"
      in ssubst)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr>) d2 (Suc 0)) (Suc n2)"
      and s=" Some e# get_labels d2 n2 "
      in ssubst)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     apply(rule get_labels_der2_decompose)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(rule get_labels_derivation_drop_decompose)
    apply(force)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(force)
  apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
  apply(erule_tac
      x="c'"
      in allE)
  apply(erule_tac
      x="w2"
      in allE)
  apply(erule_tac
      x="w'"
      in allE)
  apply(erule impE)
   apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
    apply(rule_tac
      m = "na"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
       apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
       apply(blast)
      apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
      apply(rule_tac
      s = "Suc na"
      in ssubst)
       apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
       apply(arith)
      apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
      apply(blast)
     apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
     apply(blast)
    apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
    apply(clarsimp)
   apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
   apply(rule derivation_drop_preserves_generates_maximum_of_domain)
   apply(blast)
  apply(rename_tac na d w1 w2 w' e ea c')(*strict*)
  apply(clarsimp)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> ) d1 (Suc 0)"
      in exI)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(rule_tac
      x="w1'"
      in exI)
  apply(rule conjI)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      dJ = "\<lparr>cfg_conf=c'\<rparr>"
      in cfgSTD.concatIsFromTo)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
      apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
      apply(clarsimp)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgSTD.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule_tac
      x="Suc 0"
      in exI)
      apply(simp add: der2_def)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(force)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule_tac
      x="w2'"
      in exI)
  apply(rule conjI)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(force)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="Suc n1"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="Suc n1"
      and s="Suc 0+n1"
      in ssubst)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule conjI)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(force)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule_tac
      t="get_labels d (Suc (n1 + n2))"
      and s="Some e#get_labels (derivation_drop d (Suc 0)) ((n1 + n2))"
      in ssubst)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule get_labels_derivation_drop_decompose)
   apply(force)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr>) d1 (Suc 0)) (Suc 0+n1)"
      and s=" Some e# get_labels d1 n1 "
      in ssubst)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule_tac
      t="Suc 0+n1"
      and s="Suc n1"
      in ssubst)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(force)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule get_labels_der2_decompose)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(force)
  done

lemma cfg_sub_preserves_cfg_derivation_contra: "
  valid_cfg G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> (\<forall>i e c. d i = Some (pair e c) \<longrightarrow> set (option_to_list e) \<subseteq> cfg_productions G' \<and> c \<in> cfg_configurations G')
  \<Longrightarrow> cfgSTD.derivation G' d"
  apply(simp (no_asm) add: cfgSTD.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(simp add: cfgSTD.derivation_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
    apply(erule_tac
      x="0"
      and P="\<lambda>x. case x of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (d 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G i'2 i1v i2)) (d i'))) (d x)"
      in allE)
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b)(*strict*)
   apply(erule_tac
      x="0"
      and P="\<lambda>x. case x of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (d 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G i'2 i1v i2)) (d i'))) (d x)"
      in allE)
   apply(rename_tac option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat option b)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and n="nat"
      and m="Suc nat"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac nat option b)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
    apply(rename_tac nat option b)(*strict*)
    apply(force)
   apply(rename_tac nat option b)(*strict*)
   apply(force)
  apply(rename_tac nat option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat b e1 e2 c1)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat b e1 e2 c1 l r)(*strict*)
  apply(erule_tac
      x="Suc nat"
      in allE)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  done

lemma cfg_sub_preserves_cfg_derivation_contra2: "
  valid_cfg G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgSTD.derivation G d
  \<Longrightarrow> d 0 = Some (pair None c0)
  \<Longrightarrow> c0 \<in> cfg_configurations G'
  \<Longrightarrow> \<forall>e c c'. e \<in> cfg_productions G \<and> c \<in> cfg_configurations G' \<and> cfgSTD_step_relation G c e c' \<longrightarrow> c' \<in> cfg_configurations G' \<and> e \<in> cfg_productions G'
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> set (option_to_list e) \<subseteq> cfg_productions G' \<and> c \<in> cfg_configurations G'"
  apply(induct i arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: option_to_list_def)
  apply(rename_tac i e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and n="i"
      and m="Suc i"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac i e c)(*strict*)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(simp (no_asm_simp))
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(erule exE)+
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(simp add: option_to_list_def)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule impE)
   apply(rename_tac i c e1 e2 c1)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(force)
  done

lemma cfg_sub_preserves_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgSTD.derivation G d"
  apply(simp (no_asm) add: cfgSTD.derivation_def cfgSTD.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgSTD.derivation_def cfgSTD.derivation_initial_def)
   apply(case_tac "d 0")
    apply(clarsimp)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule cfgSTD.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(simp add: cfg_sub_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
  apply(force)
  done

lemma cfg_sub_preserves_derivation_initial: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.derivation_initial G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgSTD.derivation_initial G d"
  apply(rule cfgSTD.derivation_initialI)
   apply(simp (no_asm) add: cfgSTD.derivation_def cfgSTD.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgSTD.derivation_def cfgSTD.derivation_initial_def)
    apply(clarsimp)
    apply(case_tac "d 0")
     apply(clarsimp)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(case_tac "d (Suc nat)")
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation SSG c1 e2 c2" for SSd SSn SSG)
    apply(rename_tac nat a)(*strict*)
    prefer 2
    apply(rule cfgSTD.step_detail_before_some_position)
      apply(rename_tac nat a)(*strict*)
      apply(simp add: cfgSTD.derivation_initial_def)
      apply(force)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(simp add: cfg_sub_def)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
   apply(force)
  apply(simp add: cfgSTD.derivation_def cfgSTD.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfg_initial_configurations_def get_configuration_def cfg_configurations_def cfg_sub_def)
  apply(force)
  done

lemma cfgSTD_accessible_nonterminals_vs_cfgSTD_accessible_nonterminals_ALT_1: "
  valid_cfg G \<Longrightarrow>
  cfgSTD_accessible_nonterminals G \<subseteq> cfgSTD_accessible_nonterminals_ALT G"
  apply(simp add: cfgSTD_accessible_nonterminals_def cfgSTD_accessible_nonterminals_ALT_def)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(clarsimp)
  apply(rule_tac x="n" in exI)
  apply(clarsimp)
  apply(case_tac c)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule earliest_occurence_in_list)
   apply(force)
  apply(clarsimp)
  apply(force)
  done

lemma cfgSTD_accessible_nonterminals_vs_cfgSTD_accessible_nonterminals_ALT_2: "
  valid_cfg G \<Longrightarrow>
 cfgSTD_accessible_nonterminals_ALT G \<subseteq> cfgSTD_accessible_nonterminals G"
  apply(simp add: cfgSTD_accessible_nonterminals_def cfgSTD_accessible_nonterminals_ALT_def)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(clarsimp)
  apply(rule_tac x="n" in exI)
  apply(clarsimp)
  apply(case_tac c)
  apply(clarsimp)
  apply(simp add: setAConcat)
  done

lemma cfgSTD_accessible_nonterminals_vs_cfgSTD_accessible_nonterminals_ALT: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_accessible_nonterminals_ALT G = cfgSTD_accessible_nonterminals G"
  apply(rule antisym)
   apply(metis cfgSTD_accessible_nonterminals_vs_cfgSTD_accessible_nonterminals_ALT_1 cfgSTD_accessible_nonterminals_vs_cfgSTD_accessible_nonterminals_ALT_2)
  apply(metis cfgSTD_accessible_nonterminals_vs_cfgSTD_accessible_nonterminals_ALT_1 cfgSTD_accessible_nonterminals_vs_cfgSTD_accessible_nonterminals_ALT_2)
  done

definition Sentential :: "('a,'b) cfg \<Rightarrow> ('a,'b)DT_two_elements list \<Rightarrow> bool" where
  "Sentential G w = (\<exists>d e n v. cfgSTD.derivation G d \<and> cfgSTD.belongs G d \<and> cfgSTD.derivation_initial G d \<and> d n = Some (pair e \<lparr>cfg_conf=w@v\<rparr>))"

lemma Nonterminal_free_Sentential_in_unmarked_language: "
  valid_cfg G
  \<Longrightarrow> Sentential G (liftB w)
  \<Longrightarrow> w \<in> cfgSTD.unmarked_language G"
  apply(simp add: cfgSTD.unmarked_language_def Sentential_def)
  apply(clarsimp)
  apply(rename_tac d e n v)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(simp add: cfg_unmarked_effect_def)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="\<lparr>cfg_conf = liftB w @ v\<rparr>"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  done

lemma LR1_productions_reachable: "
  valid_cfg G
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G'
  \<Longrightarrow> prod_lhs p \<in> cfgSTD_accessible_nonterminals G'
  \<Longrightarrow> p \<in> cfg_productions G'
  \<Longrightarrow> p \<in> cfgSTD_accessible_productions G"
  apply(simp add: cfgSTD_accessible_productions_def)
  apply(rule context_conjI)
   apply(simp add: cfg_sub_def)
   apply(force)
  apply(simp add: cfgSTD.get_accessible_destinations_def cfg_destination_def)
  apply(simp add: cfg_get_destinations_def)
  apply(simp add: cfgSTD_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac d n c)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1 @ [teA SSx] @ w2 = SSw" for SSx SSw)
   apply(rename_tac d n c)(*strict*)
   prefer 2
   apply(rule setA_decomp)
   apply(force)
  apply(rename_tac d n c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c w1 w2)(*strict*)
  apply(case_tac c)
  apply(rename_tac d n c w1 w2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n w1 w2)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = w1 @ teA (prod_lhs p) # w2\<rparr> p \<lparr>cfg_conf = w1 @ (prod_rhs p) @ w2\<rparr>) n"
      in exI)
  apply(rule conjI)
   apply(rename_tac d n w1 w2)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
     apply(rename_tac d n w1 w2)(*strict*)
     apply(force)
    apply(rename_tac d n w1 w2)(*strict*)
    apply(rule cfg_sub_preserves_derivation_initial)
      apply(rename_tac d n w1 w2)(*strict*)
      apply(force)
     apply(rename_tac d n w1 w2)(*strict*)
     apply(force)
    apply(rename_tac d n w1 w2)(*strict*)
    apply(force)
   apply(rename_tac d n w1 w2)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac d n w1 w2)(*strict*)
     apply(rule cfgSTD.derivation_initial_is_derivation)
     apply(rule cfg_sub_preserves_derivation_initial)
       apply(rename_tac d n w1 w2)(*strict*)
       apply(force)
      apply(rename_tac d n w1 w2)(*strict*)
      apply(force)
     apply(rename_tac d n w1 w2)(*strict*)
     apply(force)
    apply(rename_tac d n w1 w2)(*strict*)
    apply(rule cfgSTD.der2_is_derivation)
    apply(simp add: cfgSTD_step_relation_def)
    apply(force)
   apply(rename_tac d n w1 w2)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d n")
    apply(rename_tac d n w1 w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac d n w1 w2 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d n w1 w2 a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac d n w1 w2)(*strict*)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(rule_tac
      x="Some p"
      in exI)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  done

end

(*

lemma : "
  valid_cfg M
  \<Longrightarrow> nonblockingness_language (CFGLangListConv ` cfgSTD.unmarked_language M) (CFGLangListConv ` cfgSTD.marked_language M)
  \<Longrightarrow> cfgSTD.Nonblockingness M"
oops
DOES NOT HOLD:
 let S\<rightarrow>aA, S\<rightarrow>ab then nonblockingness_language (unmarked_language={\<lambda>, a, ab}) (lang={ab}) but not Nonblockingness since S\<Rightarrow>aA can not be saved

only holds for reduced grammars... can be verified seperatedly...

then the problem dissapears; is this locale change sufficient?
(A, w1), (A, w2) in cfg_productions
then \<forall>a. \<not>\<exists>v1 v2. w1=a#v1, w2=a#v2

    *)

