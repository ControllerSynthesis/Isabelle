section {*I\_cfgLM*}
theory
  I_cfgLM

imports
  I_cfg_base

begin

definition cfgLM_step_relation :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "cfgLM_step_relation M c1 p c2 \<equiv>
  p \<in> cfg_productions M
  \<and> (\<exists>l r.
      cfg_conf c1 = l @ teA (prod_lhs p) # r
      \<and> cfg_conf c2 = l @ prod_rhs p @ r
      \<and> setA l = {})"

lemma cfgLM_inst_AX_step_relation_preserves_belongs: "
  (\<forall>M. valid_cfg M \<longrightarrow> (\<forall>c1 e c2. cfgLM_step_relation M c1 e c2 \<longrightarrow> c1 \<in> cfg_configurations M \<longrightarrow> e \<in> cfg_step_labels M \<and> c2 \<in> cfg_configurations M))"
  apply(rule allI)
  apply(rename_tac M)(*strict*)
  apply(rule impI)+
  apply(rule allI)+
  apply(rename_tac M c1 e c2)(*strict*)
  apply(rule impI)+
  apply(simp add: cfg_configurations_def cfgLM_step_relation_def cfg_step_labels_def)
  apply(case_tac c2)
  apply(rename_tac M c1 e c2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e l r)(*strict*)
  apply(simp only: setAConcat concat_asso setBConcat)
  apply(clarsimp)
  apply(simp add: valid_cfg_def)
  done

lemma cfgLM_step_relation_both_sides_context: "
  setA left = {}
  \<Longrightarrow> \<forall>a e b. cfgLM_step_relation G a e b \<longrightarrow> cfgLM_step_relation G \<lparr>cfg_conf = left @ cfg_conf a @ right\<rparr> e \<lparr>cfg_conf = left @ cfg_conf b @ right\<rparr>"
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac a e b l r)(*strict*)
  apply(rule_tac
      x="left@l"
      in exI)
  apply(rule_tac
      x="r@right"
      in exI)
  apply(clarsimp)
  apply(simp (no_asm) only: setAConcat concat_asso)
  apply(force)
  done

lemma CFGLM_alt_case: "
  cfgLM_step_relation G \<lparr>cfg_conf = w1 @ w2\<rparr> e \<lparr>cfg_conf = c\<rparr>
  \<Longrightarrow> \<not> (\<exists>c'. cfgLM_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = c)
  \<Longrightarrow> \<exists>c'. cfgLM_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = c"
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def)
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
   apply(clarsimp)
   apply(rename_tac A w c)(*strict*)
   apply(simp only: setAConcat concat_asso)
   apply(force)
  apply(rename_tac l r A w c)(*strict*)
  apply(case_tac c)
   apply(rename_tac l r A w c)(*strict*)
   apply(force)
  apply(rename_tac l r A w c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac l A w list)(*strict*)
  apply(erule_tac
      x="l @ w @ list"
      in allE)
  apply(clarsimp)
  done

lemma CFGLM_no_step_without_nonterms: "
  setA (cfg_conf ca) = {}
  \<Longrightarrow> \<forall>e c'. \<not> cfgLM_step_relation G' ca e c'"
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e c' l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma supCFGLMhasAllStepsOfsub: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgLM_step_relation G1 c1 e c2
  \<Longrightarrow> cfgLM_step_relation G2 c1 e c2"
  apply(simp add: cfgLM_step_relation_def)
  apply(auto)
  apply(rename_tac l r)(*strict*)
  apply(simp add: cfg_sub_def)
  apply(auto)
  done

lemma cfgLM_step_relation_contextOK1: "
  valid_cfg G
  \<Longrightarrow> \<forall>a e b. cfgLM_step_relation G a e b \<longrightarrow> cfgLM_step_relation G \<lparr>cfg_conf = cfg_conf a@w1\<rparr> e \<lparr>cfg_conf = cfg_conf b@w1\<rparr>"
  apply(simp add: cfgLM_step_relation_def)
  apply(auto)
  apply(rename_tac a e b l r)(*strict*)
  apply(rule_tac
      x="l"
      in exI)
  apply(rule_tac
      x="r@w1"
      in exI)
  apply(auto)
  done

interpretation "cfgLM" : loc_cfg_0
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgLM_step_relation"
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
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgLM_inst_AX_step_relation_preserves_belongs )
  done

lemma CFGLM_derivation_initial_pos0: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>)"
  apply(simp add: cfgLM.derivation_initial_def)
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

lemma CFGLM_derivationCanBeDecomposed2: "
  cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1@w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> \<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n"
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2 w'. cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>} \<and> maximum_of_domain d n \<longrightarrow> (\<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n)")
   apply(blast)
  apply(thin_tac "cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}")
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
    apply(rule cfgLM.modifying_derivation_is_not_empty)
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
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="w2"
      in exI)
   apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
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
   apply(rule der1_maximum_of_domain)
  apply(rename_tac n na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1@w2\<rparr>}. d 0 = Some x")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgLM.derivation_from_starts_from)
   apply(rule cfgLM.from_to_is_from)
   apply(blast)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgLM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac na d w1 w2 w')(*strict*)
     apply(rule cfgLM.from_to_is_der)
     apply(blast)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2 w')(*strict*)
   apply(arith)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e. d (Suc na) = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgLM.reachesToAtMaxDom)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(rule cfgLM.from_to_is_to)
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
  apply(case_tac "\<exists>c'. cfgLM_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv")
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>c'. cfgLM_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = cv")
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    prefer 2
    apply(rule CFGLM_alt_case)
     apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
     apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_def)
     apply(clarsimp)
     apply(rename_tac na d w1 w2 w' e ea cv)(*strict*)
     apply(erule_tac
      x="Suc 0"
      in allE)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   apply(thin_tac "\<not> (\<exists>c'. cfgLM_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv)")
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
      in cfgLM.derivation_drop_preserves_derivation_from_to2)
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
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
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
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
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
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
    apply(rule der2_maximum_of_domain)
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
      in cfgLM.derivation_drop_preserves_derivation_from_to2)
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
      in cfgLM.concatIsFromTo)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
      apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
      apply(clarsimp)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule_tac
      x="Suc 0"
      in exI)
      apply(simp add: der2_def)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
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
  apply(rule_tac concat_has_max_dom)
   apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
  apply(force)
  done

lemma CFGLM_Nonblockingness_to_elimination: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w1@w2@w3\<rparr>)
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> cfgLM.Nonblockingness_branching G
  \<Longrightarrow> \<exists>d' n' w e. maximum_of_domain d' n' \<and> cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w2\<rparr>) \<and> d' n' = Some (pair e \<lparr>cfg_conf=w\<rparr>) \<and> setA w = {}"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule cfgLM.some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfgLM.Nonblockingness_branching_def)
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
   apply(rule cfgLM.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac c dc x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>cfg_conf = w1 @ w2 @ w3\<rparr> \<in> cfg_configurations G")
   apply(rename_tac c dc x)(*strict*)
   prefer 2
   apply(simp add: cfgLM.belongs_def)
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
      in cfgLM.some_position_has_details_before_max_dom)
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
      in cfgLM.noDeadEndBeforeMaxDom)
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
   apply(simp add: cfgLM_step_relation_def)
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
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac c dc x i ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac c dc x i ea ca)(*strict*)
    apply(rule cfgLM.der1_belongs)
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
   apply(subgoal_tac "\<forall>e c'. \<not> cfgLM_step_relation G \<lparr>cfg_conf = w'\<rparr> e c'")
    apply(rename_tac c dc x i ea w' y a)(*strict*)
    prefer 2
    apply(rule CFGLM_no_step_without_nonterms)
    apply(force)
   apply(rename_tac c dc x i ea w' y a)(*strict*)
   apply(subgoal_tac "\<exists>e c. dc (Suc (i - n)) = Some (pair (Some e) c)")
    apply(rename_tac c dc x i ea w' y a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(i-n)"
      in cfgLM.pre_some_position_is_some_position_prime)
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
   apply(subgoal_tac "cfgLM_step_relation G \<lparr>cfg_conf = w'\<rparr> eaa ca")
    apply(rename_tac c dc x i ea w' y eaa ca)(*strict*)
    prefer 2
    apply(rule_tac
      d="dc"
      and n="(i-n)"
      in cfgLM.position_change_due_to_step_relation)
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
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2@w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=(i-n)")
   apply(rename_tac c dc x i ea w')(*strict*)
   prefer 2
   apply(rule_tac
      d="dc"
      in CFGLM_derivationCanBeDecomposed2)
    apply(rename_tac c dc x i ea w')(*strict*)
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
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
  apply(thin_tac "cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rename_tac w' n1 n')
  apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n'")
   apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in CFGLM_derivationCanBeDecomposed2)
    apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
   apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
   apply(force)
  apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
  apply(clarsimp)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(thin_tac "cfgLM.derivation_from_to G d2a {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(thin_tac "cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2 @ w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'nonterminal @ w2'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(rule_tac
      x="d1a"
      in exI)
  apply(rule_tac
      x="n1a"
      in exI)
  apply(clarsimp)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
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
   apply(rule cfgLM.derivation_belongs)
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
      in cfgLM.maximum_of_domainUnique)
    apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
    apply(force)
   apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
   apply(force)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  done

lemma cfgLM_step_relation_contextOK2: "
  valid_cfg G
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> \<forall>a e b. cfgLM_step_relation G a e b \<longrightarrow> cfgLM_step_relation G \<lparr>cfg_conf = w2@cfg_conf a\<rparr> e \<lparr>cfg_conf = w2@cfg_conf b\<rparr>"
  apply(simp add: cfgLM_step_relation_def)
  apply(auto)
  apply(rename_tac a e b l r)(*strict*)
  apply(rule_tac
      x="w2@l"
      in exI)
  apply(rule_tac
      x="r"
      in exI)
  apply(auto)
  apply(rename_tac a e b l r x)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  done

lemma cfgLM_concatExtendIsFromToBoth: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>}
  \<Longrightarrow> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>}
  \<Longrightarrow> setA w1' = {}
  \<Longrightarrow> maximum_of_domain d1 m1
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> cfgLM.derivation_from_to G (derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w2\<rparr>)) (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = w1' @ (cfg_conf v)\<rparr>)) m1) {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1' @ w2'\<rparr>}"
  apply(subgoal_tac "\<exists>e1 e2. d1 0 =Some (pair None \<lparr>cfg_conf=w1\<rparr>) \<and> d1 m1 =Some (pair e1 \<lparr>cfg_conf=w1'\<rparr>) \<and> d2 0 =Some (pair None \<lparr>cfg_conf=w2\<rparr>) \<and> d2 m2 =Some (pair e2 \<lparr>cfg_conf=w2'\<rparr>)")
   prefer 2
   apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_to_def cfgLM.derivation_from_def)
   apply(clarsimp)
   apply(rename_tac n na xa xaa)(*strict*)
   apply(case_tac "d1 0")
    apply(rename_tac n na xa xaa)(*strict*)
    apply(clarsimp)
   apply(rename_tac n na xa xaa a)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac n na xa xaa a)(*strict*)
    apply(clarsimp)
   apply(rename_tac n na xa xaa a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n na xa xaa)(*strict*)
   apply(subgoal_tac "n=m1")
    apply(rename_tac n na xa xaa)(*strict*)
    apply(subgoal_tac "na=m2")
     apply(rename_tac n na xa xaa)(*strict*)
     apply(clarsimp)
    apply(rename_tac n na xa xaa)(*strict*)
    apply(rule_tac
      d="d2"
      in cfgLM.maximum_of_domainUnique)
      apply(rename_tac n na xa xaa)(*strict*)
      apply(force)
     apply(rename_tac n na xa xaa)(*strict*)
     apply(force)
    apply(rename_tac n na xa xaa)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac n na xa xaa)(*strict*)
   apply(rule_tac
      d="d1"
      in cfgLM.maximum_of_domainUnique)
     apply(rename_tac n na xa xaa)(*strict*)
     apply(force)
    apply(rename_tac n na xa xaa)(*strict*)
    apply(force)
   apply(rename_tac n na xa xaa)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(subgoal_tac "cfgLM.derivation G (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ w2\<rparr>))")
   prefer 2
   apply(rule cfgLM.derivation_map_preserves_derivation2)
    apply(rule cfgLM.from_to_is_der)
    apply(force)
   apply(rule cfgLM_step_relation_contextOK1)
   apply(clarsimp)
  apply(subgoal_tac "cfgLM.derivation G (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = w1' @ cfg_conf v\<rparr>))")
   prefer 2
   apply(rule cfgLM.derivation_map_preserves_derivation2)
    apply(rule cfgLM.from_to_is_der)
    apply(force)
   apply(rule cfgLM_step_relation_contextOK2)
    apply(clarsimp)
   apply(force)
  apply(rule_tac
      dJ="\<lparr>cfg_conf=w1'@w2\<rparr>"
      in cfgLM.concatIsFromTo)
     apply(simp add: cfgLM.derivation_from_to_def)
     apply(simp add: cfgLM.derivation_from_def)
     apply(simp add: cfgLM.derivation_to_def)
     apply(simp add: derivation_map_def)
     apply(rule_tac
      x="m1"
      in exI)
     apply(clarsimp)
     apply(rename_tac n na e1 xa xaa e2)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(simp add: cfgLM.derivation_from_to_def)
    apply(simp add: cfgLM.derivation_from_def)
    apply(simp add: cfgLM.derivation_to_def)
    apply(simp add: derivation_map_def)
    apply(rule_tac
      x="m2"
      in exI)
    apply(clarsimp)
    apply(rename_tac n na e1 xa xaa e2)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(blast)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  done

lemma StepPreciseLM: "
  valid_cfg G
  \<Longrightarrow> setA w1={}
  \<Longrightarrow> cfgLM_step_relation G \<lparr>cfg_conf = w1 @ [teA A] @ w2 \<rparr> e \<lparr>cfg_conf = w1 @ w @ w2\<rparr>
  \<Longrightarrow> e=\<lparr>prod_lhs=A, prod_rhs=w\<rparr>"
  apply(simp add: cfgLM_step_relation_def)
  apply(auto)
  apply(rename_tac l r)(*strict*)
  apply(case_tac e)
  apply(rename_tac l r prod_lhsa prod_rhsa)(*strict*)
  apply(subgoal_tac "w1=l")
   apply(rename_tac l r prod_lhsa prod_rhsa)(*strict*)
   apply(auto)
  apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
  apply(rule terminalHeadEquals1)
    apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
    apply(blast)
   apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
   apply(blast)
  apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
  apply(clarsimp)
  apply(blast)
  done

lemma cfgLM_inst_AX_marking_condition_implies_existence_of_effect: "
  \<forall>M. valid_cfg M \<longrightarrow> (\<forall>f. cfgLM.derivation_initial M f \<longrightarrow> cfg_marking_condition M f \<longrightarrow> cfg_marked_effect M f \<noteq> {})"
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

lemma cfgLM_inst_AX_string_state_increases: "
   \<forall>G. valid_cfg G \<longrightarrow>
        (\<forall>c1. c1 \<in> cfg_configurations G \<longrightarrow>
              (\<forall>e c2. cfgLM_step_relation G c1 e c2 \<longrightarrow>
                      (\<exists>w. cfg_get_history c1 @ w = cfg_get_history c2)))"
  apply(simp add: cfg_get_history_def maxTermPrefix_def cfgLM_step_relation_def)
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
   prefer 2
   apply(rule maxSplit)
  apply(rename_tac M e l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e r w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = (prod_rhs e@r) \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   apply(rename_tac M e r w1 w2)(*strict*)
   prefer 2
   apply(rule maxSplit)
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
  done

lemma cfgLM_staysInSigma: "
  valid_cfg G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgLM_step_relation G \<lparr>cfg_conf=w\<rparr> e \<lparr>cfg_conf=w'\<rparr>
  \<Longrightarrow> e \<in> cfg_productions G
  \<Longrightarrow> setB w' \<subseteq> cfg_events G"
  apply(simp add: cfgLM_step_relation_def)
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

lemma cfgLM_CFGStepNonTermBehaviour: "
  cfgLM_step_relation G \<lparr>cfg_conf = w1\<rparr> \<lparr>prod_lhs=A, prod_rhs=w\<rparr> \<lparr>cfg_conf = w2\<rparr>
  \<Longrightarrow> setA w2 \<subseteq> setA w1 \<union> setA w"
  apply(simp add: cfgLM_step_relation_def)
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

lemma cfgLM_staysInAlpha2: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>)
  \<Longrightarrow> setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G"
  apply(subgoal_tac " \<forall>e2 w'. d (i+j)=Some (pair e2 \<lparr>cfg_conf=w'\<rparr>) \<longrightarrow> (setA w' \<subseteq> cfg_nonterminals G \<and> setB w' \<subseteq> cfg_events G) ")
   apply(clarsimp)
  apply(rule_tac
      m="i"
      and n="j"
      in cfgLM.property_preseved_under_steps_is_invariant2)
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
      in cfgLM.pre_some_position_is_some_position)
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
   apply(subgoal_tac "cfgLM_step_relation G \<lparr>cfg_conf = cw\<rparr> e \<lparr>cfg_conf = w'nonterminal\<rparr>")
    apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
    apply(rule conjI)
     apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
     prefer 2
     apply(rule_tac
      w="cw"
      and e="e"
      in cfgLM_staysInSigma)
        apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
        apply(blast)
       apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
       apply(blast)
      apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
      apply(blast)
     apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
    apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
    prefer 2
    apply(rule cfgLM.position_change_due_to_step_relation)
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
    apply(rule cfgLM_CFGStepNonTermBehaviour)
    apply(blast)
   apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
   apply(clarsimp del: subsetI)
   apply(rule_tac
      a="Ax"
      in prod_rhs_in_nonterms)
    apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
    apply(blast)+
   apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac ia e2a w'nonterminal)(*strict*)
  apply(case_tac e2a)
   apply(rename_tac ia e2a w'nonterminal)(*strict*)
   apply(clarsimp)
   apply(rename_tac ia w'nonterminal)(*strict*)
   apply(rule cfgLM.derivation_Always_PreEdge_prime)
    apply(rename_tac ia w'nonterminal)(*strict*)
    apply(blast)+
  done

lemma cfgLM_staysInSigma2: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>)
  \<Longrightarrow> setB w' \<subseteq> cfg_events G"
  apply(subgoal_tac "setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G")
   apply(force)
  apply(rule cfgLM_staysInAlpha2)
       apply(force)+
  done

lemma cfgLM_inst_lang_sound: "
  (\<forall>M. valid_cfg M \<longrightarrow> cfgLM.unmarked_language M \<subseteq> cfg_effects M)"
  apply(simp add: cfg_effects_def cfgLM.unmarked_language_def cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac M x xa d e c i z)(*strict*)
  apply(simp add: cfgLM.derivation_initial_def)
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
      in cfgLM_staysInSigma2)
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

lemma cfgLM_inst_ATS_axioms: "
  ATS_Language_axioms valid_cfg cfg_initial_configurations
     cfgLM_step_relation cfg_effects cfg_marking_condition cfg_marked_effect
     cfg_unmarked_effect"
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: cfgBASE_inst_AX_effect_inclusion1 cfgLM_inst_AX_unmarked_effect_persists cfgLM_inst_lang_sound cfgLM_inst_AX_marking_condition_implies_existence_of_effect )
  done

lemma cfgLM_inst_ATS_String_State_Modification_axioms: "
  ATS_String_State_Modification_axioms valid_cfg cfg_configurations cfgLM_step_relation False cfg_get_history"
  apply(simp add: ATS_String_State_Modification_axioms_def)
  apply(rule cfgLM_inst_AX_string_state_increases)
  done

interpretation "cfgLM" : loc_cfg_1
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgLM_step_relation"
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
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgLM_inst_AX_step_relation_preserves_belongs )
  apply(simp add: cfgLM_inst_ATS_String_State_Modification_axioms cfgLM_inst_ATS_axioms )
  done

lemma cfglm_earliest_word_generated_position: "
  cfgLM.derivation G d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w@v\<rparr>)
  \<Longrightarrow> P = (\<lambda>c. \<exists>z. w@z=cfg_conf c)
  \<Longrightarrow> \<exists>k\<le>n. (\<forall>i<k. \<not> (case d i of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)) \<and>
                  (case d k of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)"
  apply(rule cfgLM.existence_of_earliest_satisfaction_point)
    apply(force)
   apply(force)
  apply(force)
  done

lemma CFGLM_Nonblockingness2: "
  valid_cfg G
  \<Longrightarrow> Nonblockingness2 (cfgLM.unmarked_language G) (cfgLM.marked_language G)"
  apply(simp add: Nonblockingness2_def)
  apply(simp add: cfgLM.marked_language_def cfgLM.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(simp add: cfg_marked_effect_def cfg_marking_condition_def cfg_initial_configurations_def cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea cb ia)(*strict*)
  apply(case_tac cb)
  apply(rename_tac x d c e i ca ea cb ia cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea ia cfg_confa)(*strict*)
  apply(simp add: cfgLM.derivation_initial_def)
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
      in cfglm_earliest_word_generated_position)
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

lemma cfgLM_inst_Nonblockingness2: "
  \<forall>M. valid_cfg M \<longrightarrow> Nonblockingness2 (cfgLM.unmarked_language M) (cfgLM.marked_language M)"
  apply(rule allI)
  apply(rename_tac M)(*strict*)
  apply(clarsimp)
  apply(rule CFGLM_Nonblockingness2)
  apply(force)
  done

lemma cfglm_terminals_at_beginning_are_never_modified: "
  cfgLM.derivation G d
  \<Longrightarrow> maximum_of_domain d (m + n)
  \<Longrightarrow> d m = Some (pair e1 \<lparr>cfg_conf = (liftB b) @ w\<rparr>)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<exists>e w. d x = Some (pair e \<lparr>cfg_conf = (liftB b) @ w\<rparr>)"
  apply(rule cfgLM.property_preseved_under_steps_is_invariant2)
      apply(blast)+
  apply(auto)
  apply(rename_tac i e wa)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i e wa)(*strict*)
   apply(clarsimp, case_tac c)
   apply(rename_tac i e wa ea c cfg_conf)(*strict*)
   apply(subgoal_tac "cfgLM_step_relation G \<lparr>cfg_conf = (liftB b) @ wa\<rparr> ea c")
    apply(rename_tac i e wa ea c cfg_conf)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
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
    apply(rule cfgLM.position_change_due_to_step_relation)
      apply(rename_tac i e wa ea cfg_conf)(*strict*)
      apply(blast)+
   apply(rename_tac i e wa)(*strict*)
   apply(rule cfgLM.some_position_has_details_before_max_dom_after_0)
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

lemma cfgLM_inst_Nonblockingness_branching_correspond1: "
  (\<forall>M. valid_cfg M \<longrightarrow> cfgLM.Nonblockingness_branching M \<longrightarrow> nonblockingness_language (cfgLM.unmarked_language M) (cfgLM.marked_language M))"
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: cfgLM.Nonblockingness_branching_def)
  apply(simp add: nonblockingness_language_def cfgLM.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac M xa d)(*strict*)
  apply(subgoal_tac "cfgLM.belongs M d")
   apply(rename_tac M xa d)(*strict*)
   prefer 2
   apply(rule cfgLM.derivation_initial_belongs)
    apply(rename_tac M xa d)(*strict*)
    apply(force)
   apply(rename_tac M xa d)(*strict*)
   apply(force)
  apply(rename_tac M xa d)(*strict*)
  apply(subgoal_tac "\<exists>v. v \<in> cfgLM.marked_language M \<and> (\<exists>c. xa @ c = v)")
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
   apply(rename_tac M xa d e c i z)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac M xa d e c i z)(*strict*)
    apply(rule cfgLM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac M xa d e c i z)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M xa d e c i z)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac M xa d e c i z)(*strict*)
   apply(rename_tac M xa d e c i z)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac M xa d e c i z)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x)(*strict*)
  apply(subgoal_tac "\<exists>c. dc 0 = Some (pair None c)")
   apply(rename_tac M xa d e c i z dc x)(*strict*)
   prefer 2
   apply(rule cfgLM.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac M xa d e c i z dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac M xa d e c i z dc x ca)(*strict*)
   prefer 2
   apply(rule cfgLM.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac M xa d e c i z dc x ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
  apply(subgoal_tac "cfgLM.derivation M (derivation_append (derivation_take d i) dc i)")
   apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
   prefer 2
   apply(simp add: cfgLM.derivation_initial_def)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
     apply(rule cfgLM.derivation_take_preserves_derivation)
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
      in cfgLM.some_position_has_details_before_max_dom)
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
   apply(simp add: cfgLM.marked_language_def)
   apply(rule_tac
      x="derivation_append (derivation_take d i) dc i"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
      apply(force)
     apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
     apply(rule cfgLM.derivation_take_preserves_derivation_initial)
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
      in cfgLM.maximum_of_domainUnique)
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
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_append (derivation_take d i) dc i) ia = Some (pair e1 c1) \<and> (derivation_append (derivation_take d i) dc i) (Suc ia) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation M c1 e2 c2")
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc ia"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
       apply(simp add: cfgLM.derivation_initial_def)
      apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
      apply(force)
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc ya e2 c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
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
   apply(rule cfglm_terminals_at_beginning_are_never_modified)
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

lemma cfgLM_inst_lang_finite: "
  (\<forall>G. valid_cfg G \<longrightarrow> cfgLM.finite_marked_language G = cfgLM.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x)(*strict*)
   apply(simp add: cfgLM.marked_language_def cfgLM.finite_marked_language_def)
   apply(clarsimp)
   apply(rename_tac G x d xa)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: cfgLM.marked_language_def cfgLM.finite_marked_language_def)
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
   apply(simp add: cfgLM.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G x d e c i)(*strict*)
    apply(rule cfgLM.derivation_take_preserves_derivation)
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
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
    apply(rule cfgLM.derivation_initial_belongs)
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

lemma cfgLM_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_cfg G \<longrightarrow> cfgLM.finite_unmarked_language G = cfgLM.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x)(*strict*)
   apply(simp add: cfgLM.unmarked_language_def cfgLM.finite_unmarked_language_def)
   apply(clarsimp)
   apply(rename_tac G x d xa)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: cfgLM.unmarked_language_def cfgLM.finite_unmarked_language_def)
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
   apply(simp add: cfgLM.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G x d e c i z)(*strict*)
    apply(rule cfgLM.derivation_take_preserves_derivation)
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

lemma cfgLM_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_cfg
     cfg_initial_configurations cfgLM_step_relation cfg_marking_condition
     cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(rule conjI)
   apply (metis cfgLM_inst_lang_finite)
  apply (metis cfgLM_inst_AX_unmarked_language_finite)
  done

lemma cfgLM_inst_BF_Bra_OpLa_axioms: "
  BF_Bra_OpLa_axioms valid_cfg cfg_configurations
     cfg_initial_configurations cfg_step_labels cfgLM_step_relation
     cfg_marking_condition cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: BF_Bra_OpLa_axioms_def)
  apply (metis cfgLM_inst_Nonblockingness_branching_correspond1)
  done

lemma cfgLM_inst_AX_marked_configuration_effect_coincides_with_marked_effect: "
(\<forall>G. valid_cfg G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial cfg_initial_configurations
               cfgLM_step_relation G d \<longrightarrow>
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
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac G d x e c i)(*strict*)
    apply(rule cfgLM.derivation_initial_belongs)
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

lemma cfgLM_inst_AX_unmarked_configuration_effect_coincides_with_unmarked_effect: "
 (\<forall>G. valid_cfg G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial cfg_initial_configurations
               cfgLM_step_relation G d \<longrightarrow>
              cfg_unmarked_effect G d =
              \<Union>{cfg_unmarked_configuration_effect G c |c.
                 \<exists>i e. d i = Some (pair e c)}))"
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

interpretation "cfgLM" : loc_cfg_2
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgLM_step_relation"
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
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgLM_inst_AX_step_relation_preserves_belongs )
  apply(simp add: cfgLM_inst_ATS_String_State_Modification_axioms cfgLM_inst_ATS_axioms cfgLM_inst_ATS_Language_by_Finite_Derivations_axioms cfgLM_inst_BF_Bra_OpLa_axioms )
  done

lemma cfgLM_inst_Nonblockingness_branching_correspond2d: "
  valid_cfg M
  \<Longrightarrow> cfgLM.is_forward_deterministic M
  \<Longrightarrow> nonblockingness_language (cfgLM.unmarked_language M) (cfgLM.marked_language M)
  \<Longrightarrow> cfgLM.Nonblockingness_branching M"
  apply(simp add: nonblockingness_language_def)
  apply(simp add: cfgLM.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(case_tac "dh n")
   apply(rename_tac dh n)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac dh n a)(*strict*)
  apply(case_tac a)
  apply(rename_tac dh n a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n option b)(*strict*)
  apply(case_tac b)
  apply(rename_tac dh n option b cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n option cfg_conf)(*strict*)
  apply(rename_tac e w)
  apply(rename_tac dh n e w)(*strict*)
  apply(subgoal_tac "\<exists>v. (maxTermPrefix w)@v \<in> cfgLM.marked_language M")
   apply(rename_tac dh n e w)(*strict*)
   prefer 2
   apply(subgoal_tac "(maxTermPrefix w) \<in> (prefix_closure (cfgLM.marked_language M))")
    apply(rename_tac dh n e w)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(subgoal_tac "(maxTermPrefix w) \<in> cfgLM.unmarked_language M")
    apply(rename_tac dh n e w)(*strict*)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(simp add: cfgLM.unmarked_language_def)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac dh n e w)(*strict*)
    prefer 2
    apply(simp add: cfgLM.derivation_initial_def)
   apply(rename_tac dh n e w)(*strict*)
   apply(simp add: cfg_unmarked_effect_def)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf=w\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac dh n e w)(*strict*)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(rule maxTermPrefix_prefix)
  apply(rename_tac dh n e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w v)(*strict*)
  apply(thin_tac " cfgLM.unmarked_language M \<subseteq> (prefix_closure (cfgLM.marked_language M))")
  apply(simp add: cfgLM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac dh n e w v d)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac dh n e w v d ea c i)(*strict*)
  apply(simp add: cfgLM.derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(rename_tac dh n e w v d ea c i)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e w v d ea c i a)(*strict*)
  apply(clarsimp)
  apply(case_tac "dh 0")
   apply(rename_tac dh n e w v d ea c i a)(*strict*)
   apply(clarsimp)
  apply(rename_tac dh n e w v d ea c i a aa)(*strict*)
  apply(clarsimp)
  apply(case_tac aa)
  apply(rename_tac dh n e w v d ea c i a aa option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w v d ea c i a b)(*strict*)
  apply(case_tac a)
  apply(rename_tac dh n e w v d ea c i a b option ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w v d ea c i b ba)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac dh n e w v d ea c i)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e w v d ea c i cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "n\<le>i")
   apply(rename_tac dh n e w v d ea i)(*strict*)
   prefer 2
   apply(case_tac "n>i")
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "dh i = d i")
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh i = Some (pair e1 c1) \<and> dh (Suc i) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation M c1 e2 c2")
      apply(rename_tac dh n e w v d ea i)(*strict*)
      prefer 2
      apply(rule_tac
      m="n"
      in cfgLM.step_detail_before_some_position)
        apply(rename_tac dh n e w v d ea i)(*strict*)
        apply(simp add: cfgLM.derivation_initial_def)
       apply(rename_tac dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(clarsimp)
     apply(rename_tac dh n e w v d ea i e2 c2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac dh n e w v d ea i e2 c2 l r)(*strict*)
     apply(simp only: setAConcat concat_asso setBConcat)
     apply(force)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(rule sym)
    apply(rule_tac
      n="i"
      and m="n"
      and ?d1.0="d"
      and ?d2.0="dh"
      and x="0"
      and y="0"
      in cfgLM.is_forward_deterministic_derivations_coincide)
             apply(rename_tac dh n e w v d ea i)(*strict*)
             apply(force)
            apply(rename_tac dh n e w v d ea i)(*strict*)
            apply(force)
           apply(rename_tac dh n e w v d ea i)(*strict*)
           apply(force)
          apply(rename_tac dh n e w v d ea i)(*strict*)
          apply(force)
         apply(rename_tac dh n e w v d ea i)(*strict*)
         apply(force)
        apply(rename_tac dh n e w v d ea i)(*strict*)
        apply(force)
       apply(rename_tac dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(force)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(rule_tac
      x="derivation_drop (derivation_take d i) n"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(rule_tac
      m="i-n"
      in cfgLM.derivation_drop_preserves_derivation_prime)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(rule cfgLM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac dh n e w v d ea i)(*strict*)
   prefer 2
   apply(rule_tac
      m="i"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(blast)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(blast)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(rule_tac cfgLM.derivation_drop_preserves_belongs)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(rule cfgLM.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(rule_tac cfgLM.derivation_take_preserves_belongs)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(simp add: cfgLM.derivation_initial_def)
    apply(simp add: cfg_initial_configurations_def)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(simp add: derivation_take_def)
   apply(force)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(rule_tac
      x="i-n"
      in exI)
   apply(simp add: maximum_of_domain_def derivation_drop_def derivation_take_def)
   apply(clarsimp)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "dh n = d n")
   apply(rename_tac dh n e w v d ea i)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule_tac
      n="n"
      and m="n"
      and ?d1.0="d"
      and ?d2.0="dh"
      and x="0"
      and y="0"
      in cfgLM.is_forward_deterministic_derivations_coincide)
            apply(rename_tac dh n e w v d ea i)(*strict*)
            apply(force)
           apply(rename_tac dh n e w v d ea i)(*strict*)
           apply(force)
          apply(rename_tac dh n e w v d ea i)(*strict*)
          apply(force)
         apply(rename_tac dh n e w v d ea i)(*strict*)
         apply(force)
        apply(rename_tac dh n e w v d ea i)(*strict*)
        apply(force)
       apply(rename_tac dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(force)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(simp add: derivation_append_fit_def derivation_drop_def derivation_take_def)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(subgoal_tac "i=ia")
   apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
   prefer 2
   apply(case_tac "i=ia")
    apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
    apply(force)
   apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
   apply(case_tac "i<ia")
    apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation M c1 e2 c2")
     apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
     prefer 2
     apply(rule_tac
      m="ia"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
       apply(simp add: cfgLM.derivation_initial_def)
      apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
      apply(force)
     apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n e w v d ea i ia eb c e2 c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac dh n e w v d ea i ia eb c e2 c2 l r)(*strict*)
    apply(simp only: setAConcat concat_asso setBConcat)
    apply(force)
   apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d ia = Some (pair e1 c1) \<and> d (Suc ia) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation M c1 e2 c2")
    apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
    prefer 2
    apply(rule_tac
      m="i"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
    apply(force)
   apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e w v d ea i ia eb c e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac dh n e w v d ea i ia eb c e2 c2 l r)(*strict*)
   apply(simp only: setAConcat concat_asso setBConcat)
   apply(force)
  apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w v d ea ia)(*strict*)
  apply(rule_tac
      x="ia"
      in exI)
  apply(simp add: derivation_append_def derivation_drop_def derivation_take_def)
  apply(clarsimp)
  done

lemma cfgLM_inst_BF_Bra_DetR_LaOp_axioms: "
  BF_Bra_DetR_LaOp_axioms valid_cfg cfg_configurations
     cfg_initial_configurations cfg_step_labels cfgLM_step_relation
     cfg_marking_condition cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: BF_Bra_DetR_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: nonblockingness_language_def)
  apply(simp add: cfgLM.Nonblockingness_branching_def)
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
  apply(subgoal_tac "\<exists>v. (maxTermPrefix w)@v \<in> cfgLM.marked_language M")
   apply(rename_tac M dh n e w)(*strict*)
   prefer 2
   apply(subgoal_tac "(maxTermPrefix w) \<in> (prefix_closure (cfgLM.marked_language M))")
    apply(rename_tac M dh n e w)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(force)
   apply(rename_tac M dh n e w)(*strict*)
   apply(subgoal_tac "(maxTermPrefix w) \<in> cfgLM.unmarked_language M")
    apply(rename_tac M dh n e w)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w)(*strict*)
   apply(simp add: cfgLM.unmarked_language_def)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac M dh n e w)(*strict*)
    prefer 2
    apply(simp add: cfgLM.derivation_initial_def)
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
  apply(thin_tac " cfgLM.unmarked_language M \<subseteq> (prefix_closure (cfgLM.marked_language M))")
  apply(simp add: cfgLM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea c i)(*strict*)
  apply(subgoal_tac "case dh 0 of None \<Rightarrow> False | Some (pair a b) \<Rightarrow> b \<in> cfg_initial_configurations M \<and> a = None")
   apply(rename_tac M dh n e w v d ea c i)(*strict*)
   prefer 2
   apply(simp add: cfgLM.derivation_initial_def)
  apply(rename_tac M dh n e w v d ea c i)(*strict*)
  apply(subgoal_tac "case_option False (case_derivation_configuration (\<lambda>a b. b \<in> cfg_initial_configurations M \<and> a = None)) (d 0)")
   apply(rename_tac M dh n e w v d ea c i)(*strict*)
   prefer 2
   apply(simp add: cfgLM.derivation_initial_def)
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
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh i = Some (pair e1 c1) \<and> dh (Suc i) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation M c1 e2 c2")
      apply(rename_tac M dh n e w v d ea i)(*strict*)
      prefer 2
      apply(rule_tac
      m="n"
      in cfgLM.step_detail_before_some_position)
        apply(rename_tac M dh n e w v d ea i)(*strict*)
        apply(simp add: cfgLM.derivation_initial_def)
       apply(rename_tac M dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac M dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(clarsimp)
     apply(rename_tac M dh n e w v d ea i e2 c2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
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
      in cfgLM.is_forward_deterministic_accessible_derivations_coincide)
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
      in cfgLM.derivation_drop_preserves_derivation_prime)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(rule cfgLM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   prefer 2
   apply(rule_tac
      m="i"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(blast)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(blast)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(rule_tac cfgLM.derivation_drop_preserves_belongs)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(rule cfgLM.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(rule_tac cfgLM.derivation_take_preserves_belongs)
    apply(rule cfgLM.derivation_initial_belongs)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(simp add: cfgLM.derivation_initial_def)
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
      in cfgLM.is_forward_deterministic_accessible_derivations_coincide)
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
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation M c1 e2 c2")
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     prefer 2
     apply(rule_tac
      m="ia"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
       apply(simp add: cfgLM.derivation_initial_def)
      apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
      apply(force)
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    apply(clarsimp)
    apply(rename_tac M dh n e w v d ea i ia eb c e2 c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac M dh n e w v d ea i ia eb c e2 c2 l r)(*strict*)
    apply(simp only: setAConcat concat_asso setBConcat)
    apply(force)
   apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d ia = Some (pair e1 c1) \<and> d (Suc ia) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation M c1 e2 c2")
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    prefer 2
    apply(rule_tac
      m="i"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e w v d ea i ia eb c e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
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

interpretation "cfgLM" : loc_cfg_3
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgLM_step_relation"
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
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgLM_inst_AX_step_relation_preserves_belongs cfgLM_inst_ATS_String_State_Modification_axioms cfgLM_inst_ATS_axioms cfgLM_inst_ATS_Language_by_Finite_Derivations_axioms cfgLM_inst_BF_Bra_OpLa_axioms cfgLM_inst_BF_Bra_DetR_LaOp_axioms )
  done

lemma CFGLM0_is_forward_target_deterministic: "
  valid_cfg M
  \<Longrightarrow> cfgLM.is_forward_target_deterministic M"
  apply(simp add: cfgLM.is_forward_target_deterministic_def)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e l r la ra)(*strict*)
  apply(case_tac c)
  apply(rename_tac c c1 c2 e l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c1 c2 e l r la ra)(*strict*)
  apply(case_tac c1)
  apply(rename_tac c1 c2 e l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c2 e l r la ra)(*strict*)
  apply(case_tac c2)
  apply(rename_tac c2 e l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e l r la ra)(*strict*)
  apply(subgoal_tac "l=la")
   apply(rename_tac e l r la ra)(*strict*)
   apply(force)
  apply(rename_tac e l r la ra)(*strict*)
  apply(case_tac e)
  apply(rename_tac e l r la ra prod_lhsa prod_rhs)(*strict*)
  apply(clarsimp)
  apply(rename_tac l r la ra prod_lhs prod_rhs)(*strict*)
  apply(rename_tac w v)
  apply(rename_tac l r la ra w v)(*strict*)
  apply(thin_tac "valid_cfg M")
  apply(thin_tac "\<lparr>prod_lhs = w, prod_rhs = v\<rparr> \<in> cfg_productions M")
  apply(rule sym)
  apply(rule terminalHeadEquals1)
    apply(rename_tac l r la ra w v)(*strict*)
    apply(force)
   apply(rename_tac l r la ra w v)(*strict*)
   apply(force)
  apply(rename_tac l r la ra w v)(*strict*)
  apply(force)
  done

lemma CFGLM_Nonblockingness_is_lang_notempty: "
  valid_cfg G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G
  \<Longrightarrow> cfgLM.marked_language G \<noteq> {}"
  apply(simp add: cfgLM.marked_language_def cfgLM.Nonblockingness_branching_def)
  apply(erule_tac
      x="der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in allE)
  apply(erule impE)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(rule conjI)
    apply(simp add: cfgLM.der1_is_derivation)
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
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac dc n' i e x)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(force)
   apply(rename_tac dc n' i e x)(*strict*)
   apply(simp add: der1_def)
   apply(case_tac "dc 0")
    apply(rename_tac dc n' i e x)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgLM.derivation_def)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
   apply(rename_tac dc n' i e x a)(*strict*)
   apply(case_tac "dc 0")
    apply(rename_tac dc n' i e x a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dc n' i e x a aa)(*strict*)
   apply(simp add: cfgLM.derivation_def)
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
   apply(simp add: cfgLM.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac dc n' i e x)(*strict*)
      apply(rule cfgLM.der1_is_derivation)
     apply(rename_tac dc n' i e x)(*strict*)
     apply(force)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(simp add: der1_def)
    apply(case_tac "dc 0")
     apply(rename_tac dc n' i e x)(*strict*)
     apply(clarsimp)
     apply(simp add: cfgLM.derivation_def)
     apply(erule_tac
      x="0"
      in allE)
     apply(clarsimp)
    apply(rename_tac dc n' i e x a)(*strict*)
    apply(case_tac "dc 0")
     apply(rename_tac dc n' i e x a)(*strict*)
     apply(clarsimp)
    apply(rename_tac dc n' i e x a aa)(*strict*)
    apply(simp add: cfgLM.derivation_def)
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

lemma cfgLM_no_step_without_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac option b)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac option b)(*strict*)
     apply(force)
    apply(rename_tac option b)(*strict*)
    apply(force)
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b e2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac b e2 l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

interpretation "cfgLM_cfgLM_ATS_Bisimulation_Configuration_Weak" : ATS_Bisimulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_cfg"
  (* configurations1 *)
  "cfg_configurations"
  (* initial_configurations1 *)
  "cfg_initial_configurations"
  (* step_labels1 *)
  "cfg_step_labels"
  (* step_relation1 *)
  "cfgLM_step_relation"
  (* effects1 *)
  "cfg_effects"
  (* marking_condition1 *)
  "cfg_marking_condition"
  (* marked_effect1 *)
  "cfg_marked_effect"
  (* unmarked_effect1 *)
  "cfg_unmarked_effect"
  (* TSstructure2 *)
  "valid_cfg"
  (* configurations2 *)
  "cfg_configurations"
  (* initial_configurations2 *)
  "cfg_initial_configurations"
  (* step_labels2 *)
  "cfg_step_labels"
  (* step_relation2 *)
  "cfgLM_step_relation"
  (* effects2 *)
  "cfg_effects"
  (* marking_condition2 *)
  "cfg_marking_condition"
  (* marked_effect2 *)
  "cfg_marked_effect"
  (* unmarked_effect2 *)
  "cfg_unmarked_effect"
  apply(simp add: LOCALE_DEFS_ALL LOCALE_DEFS_cfg ATS_Bisimulation_Configuration_Weak_def)
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgLM_inst_AX_step_relation_preserves_belongs cfgLM_inst_ATS_String_State_Modification_axioms cfgLM_inst_ATS_axioms )
  done

lemma cfgLM_inst_accept: "
  (\<forall>G d. cfgLM.derivation_initial G d \<longrightarrow> cfg_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> cfg_marking_configuration G))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  done

definition cfgLM_accessible_productions :: "
  ('nonterminal, 'event)cfg
  \<Rightarrow> ('nonterminal, 'event)cfg_step_label set"
  where
    "cfgLM_accessible_productions G \<equiv>
  {p \<in> cfg_productions G.
    dest_production p \<in> cfgLM.get_accessible_destinations G}"

definition cfgLM_required_productions :: "
  ('nonterminal, 'event)cfg
  \<Rightarrow> ('nonterminal, 'event)cfg_step_label set"
  where
    "cfgLM_required_productions G \<equiv>
  {p \<in> cfg_productions G.
    \<exists>d n c.
      cfgLM.derivation_initial G d
      \<and> d n = Some (pair (Some p) c)
      \<and> cfg_marking_condition G d}"

lemma only_extension_by_one: "
  valid_cfg G
  \<Longrightarrow> (\<forall>p\<in> cfg_productions G. \<exists>w v. prod_rhs p=liftB w@liftA v \<and> length w\<le>Suc 0)
  \<Longrightarrow> c1 \<in> cfg_configurations G
  \<Longrightarrow> cfg_conf c1=liftB w@liftA v
  \<Longrightarrow> cfgLM_step_relation G c1 p c2
  \<Longrightarrow> length(maxTermPrefix (cfg_conf c2))\<le>Suc(length(maxTermPrefix (cfg_conf c1)))"
  apply(simp add: cfgLM_step_relation_def)
  apply(erule_tac
      x="p"
      in ballE)
   prefer 2
   apply(force)
  apply(case_tac c1)
  apply(rename_tac cfg_confa)(*strict*)
  apply(case_tac p)
  apply(rename_tac cfg_confa prod_lhsa prod_rhsa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac cfg_confa prod_lhsa prod_rhsa cfg_confaa)(*strict*)
  apply(rename_tac w1 A r w2)
  apply(rename_tac w1 A r w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac A wa l ra va)(*strict*)
  apply(subgoal_tac "\<exists>w. liftB w = l")
   apply(rename_tac A wa l ra va)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac A wa l ra va)(*strict*)
  apply(clarsimp)
  apply(rename_tac A wa ra va waa)(*strict*)
  apply(subgoal_tac "w=waa")
   apply(rename_tac A wa ra va waa)(*strict*)
   prefer 2
   apply(rule equal_left_liftB)
   apply(force)
  apply(rename_tac A wa ra va waa)(*strict*)
  apply(clarsimp)
  apply(rename_tac A wa ra va)(*strict*)
  apply(case_tac v)
   apply(rename_tac A wa ra va)(*strict*)
   apply(clarsimp)
  apply(rename_tac A wa ra va a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac A wa v list)(*strict*)
  apply(subgoal_tac "maxTermPrefix (liftB w @ teA A # liftA list) = w")
   apply(rename_tac A wa v list)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_mixed_string)
  apply(rename_tac A wa v list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "maxTermPrefix (liftB w @ liftB wa @ liftA v @ liftA list) = w@wa")
   apply(rename_tac A wa v list)(*strict*)
   prefer 2
   apply (metis (erased, hide_lams) liftA.simps(1) liftA.simps(2) append_Cons append_Nil maxTermPrefix_mixed_string maxTermPrefix_shift maxTermPrefix_term_string neq_Nil_conv)
  apply(rename_tac A wa v list)(*strict*)
  apply(case_tac wa)
   apply(rename_tac A wa v list)(*strict*)
   apply(clarsimp)
  apply(rename_tac A wa v list a lista)(*strict*)
  apply(force)
  done

definition cfgLM_accessible_nonterminals :: "
  ('nonterminal,'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgLM_accessible_nonterminals G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n c.
      cfgLM.derivation_initial G d
      \<and> get_configuration (d n) = Some c
      \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2)}"

definition cfgLM_Nonblockingness_nonterminals :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgLM_Nonblockingness_nonterminals G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n e w'.
      cfgLM.derivation G d
      \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)
      \<and> d n = Some (pair e \<lparr>cfg_conf = w'\<rparr>)
      \<and> setA w' = {}}"

lemma cfgLM_Nonblockingness_branching_implies_cfgLM_accessible_nonterminals_contained_in_cfgLM_Nonblockingness_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G
  \<Longrightarrow> cfgLM_accessible_nonterminals G \<subseteq> cfgLM_Nonblockingness_nonterminals G"
  apply(simp add: cfgLM_accessible_nonterminals_def)
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
  apply(subgoal_tac "\<exists>d. cfgLM.derivation_initial G d \<and> maximum_of_domain d n \<and> d n = Some (pair e \<lparr>cfg_conf = liftB w1 @ teA x # w2\<rparr>)")
   apply(rename_tac x d n w1 w2 e)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d n"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply (metis cfgLM.derivation_take_preserves_derivation_initial)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply (metis maximum_of_domain_derivation_take not_None_eq)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(thin_tac "cfgLM.derivation_initial G d")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = liftB w1 @ teA x # w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac x n w1 w2 e d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x n w1 w2 e d)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and ?w1.0="liftB w1"
      and ?w2.0="[teA x]"
      and ?w3.0="w2"
      in CFGLM_Nonblockingness_to_elimination)
         apply(rename_tac x n w1 w2 e d)(*strict*)
         apply(force)
        apply(rename_tac x n w1 w2 e d)(*strict*)
        apply(simp add: cfgLM.derivation_initial_def)
       apply(rename_tac x n w1 w2 e d)(*strict*)
       apply(rule cfgLM.derivation_initial_belongs)
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
  apply(thin_tac "cfgLM.Nonblockingness_branching G")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "cfgLM.derivation_initial G d")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = liftB w1 @ teA x # w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac x d' n' w e)(*strict*)
  apply(simp add: cfgLM_Nonblockingness_nonterminals_def)
  apply(rule conjI)
   apply(rename_tac x d' n' w e)(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf = [teA x]\<rparr> \<in> cfg_configurations G")
    apply(rename_tac x d' n' w e)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac x d' n' w e)(*strict*)
   apply (metis cfgLM.belongs_configurations)
  apply(rename_tac x d' n' w e)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n'"
      in exI)
  apply(clarsimp)
  done

lemma cfgLM_Nonblockingness_branching_implies_FB_iterated_elimination: "
  valid_cfg G
  \<Longrightarrow> cfgLM.Nonblockingness_branching G
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> cfg_conf c = w1 @ teA x # w2
  \<Longrightarrow> \<exists>d. cfgLM.derivation_initial G d \<and>
  (\<exists>n c. get_configuration (d n) = Some c \<and>
  (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA x # w2))"
  apply(induct "length (filterA w1)" arbitrary: w1 d n e c)
   apply(rename_tac w1 d n e c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule conjI)
    apply(rename_tac w1 d n e c)(*strict*)
    apply(force)
   apply(rename_tac w1 d n e c)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "\<exists>w. liftB w = w1")
    apply(rename_tac w1 d n e c)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB w1"
      in exI)
    apply(rule liftBDeConv2)
    apply(rule filterA_setA)
    apply(force)
   apply(rename_tac w1 d n e c)(*strict*)
   apply(force)
  apply(rename_tac xa w1 d n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa w1 d n e c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa w1 d n e)(*strict*)
  apply(subgoal_tac "\<exists>wx1 A wx2. w1 = liftB wx1 @[teA A]@ wx2")
   apply(rename_tac xa w1 d n e)(*strict*)
   prefer 2
   apply(rule filterA_gt_0_then_lm_nontelminal)
   apply(force)
  apply(rename_tac xa w1 d n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa d n e wx1 A wx2)(*strict*)
  apply(subgoal_tac "A \<in> cfgLM_Nonblockingness_nonterminals G")
   apply(rename_tac xa d n e wx1 A wx2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfgLM_accessible_nonterminals G"
      in set_mp)
    apply(rename_tac xa d n e wx1 A wx2)(*strict*)
    apply(rule cfgLM_Nonblockingness_branching_implies_cfgLM_accessible_nonterminals_contained_in_cfgLM_Nonblockingness_nonterminals)
     apply(rename_tac xa d n e wx1 A wx2)(*strict*)
     apply(force)
    apply(rename_tac xa d n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac xa d n e wx1 A wx2)(*strict*)
   apply(simp add: cfgLM_accessible_nonterminals_def)
   apply(subgoal_tac "\<lparr>cfg_conf = liftB wx1 @ teA A # wx2 @ teA x # w2\<rparr> \<in> cfg_configurations G")
    apply(rename_tac xa d n e wx1 A wx2)(*strict*)
    prefer 2
    apply (rule cfgLM.belongs_configurations)
     apply(rename_tac xa d n e wx1 A wx2)(*strict*)
     apply(rule cfgLM.derivation_initial_belongs)
      apply(rename_tac xa d n e wx1 A wx2)(*strict*)
      apply(force)
     apply(rename_tac xa d n e wx1 A wx2)(*strict*)
     apply(force)
    apply(rename_tac xa d n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac xa d n e wx1 A wx2)(*strict*)
   apply(rule conjI)
    apply(rename_tac xa d n e wx1 A wx2)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(simp add: setAConcat)
   apply(rename_tac xa d n e wx1 A wx2)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      x="wx1"
      in exI)
   apply(force)
  apply(rename_tac xa d n e wx1 A wx2)(*strict*)
  apply(simp add: cfgLM_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac xa d n e wx1 A wx2 da na ea w')(*strict*)
  apply(subgoal_tac "\<exists>w. liftB w = w'")
   apply(rename_tac xa d n e wx1 A wx2 da na ea w')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB w'"
      in exI)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac xa d n e wx1 A wx2 da na ea w')(*strict*)
  apply(clarsimp)
  apply(rename_tac xa d n e wx1 A wx2 da na ea w)(*strict*)
  apply(thin_tac "setA (liftB w) = {}")
  apply(case_tac na)
   apply(rename_tac xa d n e wx1 A wx2 da na ea w)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa d n e wx1 A wx2 da w)(*strict*)
   apply(case_tac w)
    apply(rename_tac xa d n e wx1 A wx2 da w)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa d n e wx1 A wx2 da w a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa d n e wx1 A wx2 da na ea w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa d n e wx1 A wx2 da ea w nat)(*strict*)
  apply(rename_tac na)
  apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
  apply(subgoal_tac "\<exists>d n e c. cfgLM.derivation_initial G d \<and> d n = Some (pair e c) \<and> cfg_conf c = liftB wx1 @ liftB w @ wx2 @ teA x # w2")
   apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_append d (derivation_map da (\<lambda>c. \<lparr>cfg_conf=liftB wx1@(cfg_conf c)@wx2 @ teA x # w2\<rparr>)) n"
      in exI)
   apply(rule_tac
      x="n+Suc na"
      in exI)
   apply(rule_tac
      x="ea"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf=liftB wx1@(liftB w)@wx2 @ teA x # w2\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
      apply(force)
     apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
     apply(force)
    apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
     apply(rule cfgLM.derivation_map_preserves_derivation)
       apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
       apply(force)
      apply(rename_tac xa d n e wx1 A wx2 da ea w na i eb c)(*strict*)
      apply(force)
     apply(rename_tac xa d n e wx1 A wx2 da ea w na c1 eb c2)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac xa d n e wx1 A wx2 da ea w na c1 eb c2 l r)(*strict*)
     apply(rule_tac
      x="liftB wx1 @ l"
      in exI)
     apply(clarsimp)
     apply(simp add: setAConcat)
     apply(rule setA_liftB)
    apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_map_def)
   apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
   apply(simp add: derivation_append_def derivation_map_def)
  apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
  apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
  apply(thin_tac "A \<in> cfg_nonterminals G")
  apply(thin_tac "cfgLM.derivation_initial G d")
  apply(thin_tac "cfgLM.Nonblockingness_branching G")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = liftB wx1 @ teA A # wx2 @ teA x # w2\<rparr>)")
  apply(thin_tac "cfgLM.derivation G da")
  apply(thin_tac "da (Suc na) = Some (pair ea \<lparr>cfg_conf = liftB w\<rparr>)")
  apply(clarsimp)
  apply(rename_tac xa wx1 A wx2 w d n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa wx1 A wx2 w d n e c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa wx1 A wx2 w d n e)(*strict*)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  apply(rename_tac xa wx1 wx2 w d n e)(*strict*)
  apply(erule_tac
      x="liftB wx1 @ liftB w @ wx2"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac wx1 wx2 w d n e)(*strict*)
  apply(erule_tac
      x="d"
      in meta_allE)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="e"
      in meta_allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = liftB wx1 @ liftB w @ wx2 @ teA x # w2\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  done

lemma cfgLM_no_nonterminal_at_end_in_marking_condition: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
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
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i ea ca)(*strict*)
     apply(force)
    apply(rename_tac i ea ca)(*strict*)
    apply(force)
   apply(rename_tac i ea ca)(*strict*)
   apply (metis (mono_tags) cfgLM.allPreMaxDomSome_prime le_antisym not_less_eq_eq option.distinct(1))
  apply(rename_tac i ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea ca e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i ea ca e2 c2 l r)(*strict*)
  apply(case_tac ca)
  apply(rename_tac i ea ca e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea e2 c2 l r)(*strict*)
  apply (metis elemInsetA empty_iff)
  done

definition cfgLM_accessible_nonterminals_ALT :: "
  ('nonterminal,'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgLM_accessible_nonterminals_ALT G \<equiv>
  {A. \<exists>d n e w1 w2.
      cfgLM.derivation_initial G d
      \<and> d n = Some (pair e \<lparr>cfg_conf = liftB w1 @ teA A # w2 \<rparr>)}"

lemma cfgLM_accessible_nonterminals_ALT_vs_cfgLM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgLM_accessible_nonterminals_ALT G = cfgLM_accessible_nonterminals G"
  apply(simp add: cfgLM_accessible_nonterminals_ALT_def cfgLM_accessible_nonterminals_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x d n e w1 w2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x d n e w1 w2)(*strict*)
    prefer 2
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac x d n e w1 w2)(*strict*)
     apply(rule cfgLM.derivation_initial_belongs)
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

definition cfgLM_Nonblockingness_nonterminals_ALT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgLM_Nonblockingness_nonterminals_ALT G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n e w.
      cfgLM.derivation G d
      \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)
      \<and> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)}"

lemma cfgLM_Nonblockingness_nonterminals_ALT_vs_cfgLM_Nonblockingness_nonterminals: "
  cfgLM_Nonblockingness_nonterminals_ALT G = cfgLM_Nonblockingness_nonterminals G"
  apply(rule antisym)
   apply(simp add: cfgLM_Nonblockingness_nonterminals_ALT_def cfgLM_Nonblockingness_nonterminals_def)
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
  apply(simp add: cfgLM_Nonblockingness_nonterminals_ALT_def cfgLM_Nonblockingness_nonterminals_def)
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

lemma CFGLM_derivationCanBeDecomposed2_with_labels: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> \<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1 + n2 = n \<and> set (get_labels d n) = set (get_labels d1 n1) \<union>set (get_labels d2 n2)"
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2 w'. cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>} \<and> maximum_of_domain d n \<longrightarrow> (\<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n \<and> set(get_labels d n)=set(get_labels d1 n1)\<union>set(get_labels d2 n2))")
   apply(blast)
  apply(thin_tac "cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}")
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
    apply(rule cfgLM.modifying_derivation_is_not_empty)
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
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="w2"
      in exI)
   apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
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
   apply(rule cfgLM.derivation_from_starts_from)
   apply(rule cfgLM.from_to_is_from)
   apply(blast)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgLM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac na d w1 w2 w')(*strict*)
     apply(rule cfgLM.from_to_is_der)
     apply(blast)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2 w')(*strict*)
   apply(arith)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e. d (Suc na) = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgLM.reachesToAtMaxDom)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(rule cfgLM.from_to_is_to)
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
  apply(case_tac "\<exists>c'. cfgLM_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv")
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>c'. cfgLM_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = cv")
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    prefer 2
    apply(rule CFGLM_alt_case)
     apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
     apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_def)
     apply(clarsimp)
     apply(rename_tac na d w1 w2 w' e ea cv)(*strict*)
     apply(erule_tac
      x="Suc 0"
      in allE)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   apply(thin_tac "\<not> (\<exists>c'. cfgLM_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv)")
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
      in cfgLM.derivation_drop_preserves_derivation_from_to2)
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
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
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
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
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
      in cfgLM.derivation_drop_preserves_derivation_from_to2)
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
      in cfgLM.concatIsFromTo)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
      apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
      apply(clarsimp)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule_tac
      x="Suc 0"
      in exI)
      apply(simp add: der2_def)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
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

lemma cfgLM_accessible_productions_vs_cfgLM_required_productions2: "
  valid_cfg G
  \<Longrightarrow> cfgLM_accessible_productions G \<supseteq> cfgLM_required_productions G"
  apply(simp add: cfgLM_accessible_productions_def cfgLM_required_productions_def)
  apply(clarsimp)
  apply(rename_tac x d n c)(*strict*)
  apply(simp add: cfgLM.get_accessible_destinations_def)
  apply(simp add: cfg_get_destinations_def)
  apply(simp add: cfg_destination_def)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="n"
      in exI)
  apply(clarsimp)
  done

lemma earlist_occurence_of_nonterminal: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> cfg_conf (the (get_configuration (d n))) = w1 @ [teA x] @ w2
  \<Longrightarrow> \<exists>m\<le>n. \<exists>w1. cfg_conf (the (get_configuration (d m))) = w1 @ [teA x] @ w2 \<and> (\<forall>k<m. \<not>(\<exists>w1. cfg_conf (the (get_configuration (d k))) = w1 @ [teA x] @ w2))"
  apply(subgoal_tac "\<exists>k\<le>n. (\<forall>i<k. \<not>(\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> SSP c)) i) & ((\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> SSP c)))k" for SSP)
   prefer 2
   apply(rule_tac
      P="\<lambda>c. \<exists>w1. cfg_conf c = w1 @ [teA x] @ w2"
      in cfgLM.existence_of_earliest_satisfaction_point)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(rule_tac
      x="w1"
      in exI)
   apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(rule_tac
      x="k"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac k)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d k")
    apply(rename_tac k)(*strict*)
    apply(clarsimp)
   apply(rename_tac k a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac k a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ka w1a)(*strict*)
  apply(case_tac "k=ka")
   apply(rename_tac k ka w1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac k ka w1a)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="ka"
      in allE)
  apply(clarsimp)
  apply(case_tac "d k")
   apply(rename_tac k ka w1a)(*strict*)
   apply(clarsimp)
  apply(rename_tac k ka w1a a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac k ka w1a a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ka w1a option b w1aa)(*strict*)
  apply(case_tac "d ka")
   apply(rename_tac k ka w1a option b w1aa)(*strict*)
   apply(clarsimp)
   apply (metis cfgLM.derivationNoFromNone2 cfgLM.derivation_initial_is_derivation not_None_eq)
  apply(rename_tac k ka w1a option b w1aa a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac k ka w1a option b w1aa a optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac k ka w1a option b w1aa optiona ba)(*strict*)
  apply(simp add: get_configuration_def)
  done

lemma CFGLM_CFGAC_has_cfgSTD_accessible_productions: "
  valid_cfg G
  \<Longrightarrow> N = cfgLM_accessible_nonterminals G
  \<Longrightarrow> P = {p \<in> cfg_productions G. prod_lhs p \<in> N}
  \<Longrightarrow> P = cfgLM_accessible_productions G"
  apply(simp add: cfgLM_accessible_productions_def cfgLM_accessible_nonterminals_def cfgLM.get_accessible_destinations_def)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d n c w1 w2)(*strict*)
    apply(simp add: cfg_destination_def)
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(case_tac "d n")
    apply(rename_tac x d n c w1 w2)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac x d n c w1 w2 a)(*strict*)
   apply(case_tac a)
   apply(rename_tac x d n c w1 w2 a option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac x d n c w1 w2 option)(*strict*)
   apply(rename_tac e)
   apply(rename_tac x d n c w1 w2 e)(*strict*)
   apply(case_tac c)
   apply(rename_tac x d n c w1 w2 e cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = liftB w1 @ teA (prod_lhs x) # w2\<rparr> x \<lparr>cfg_conf = liftB w1 @ (prod_rhs x) @ w2\<rparr>) n"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(rename_tac x d n w1 w2 e)(*strict*)
      apply(force)
     apply(rename_tac x d n w1 w2 e)(*strict*)
     apply(force)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac x d n w1 w2 e)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac x d n w1 w2 e)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="liftB w1"
      in exI)
     apply(clarsimp)
     apply (metis setA_liftB)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac x d n w1 w2 e)(*strict*)
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
   apply (metis cfgLM.derivation_initial_is_derivation cfgLM.initialNotEdgeSome_prime)
  apply(rename_tac d i c a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c a nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac d c a nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d c a nat)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
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
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d c a nat e1 c1 l r)(*strict*)
  apply(rule_tac
      x="filterB l"
      in exI)
  apply(rule_tac
      x="r"
      in exI)
  apply(clarsimp)
  apply (metis liftBDeConv2)
  done

lemma cfg_sub_preserves_cfgLM_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgLM.derivation G d"
  apply(simp (no_asm) add: cfgLM.derivation_def cfgLM.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_def cfgLM.derivation_initial_def)
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule cfgLM.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(simp add: cfg_sub_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
  apply(force)
  done

lemma cfg_sub_preserves_cfgLM_derivation_initial: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgLM.derivation_initial G d"
  apply(rule cfgLM.derivation_initialI)
   apply(simp (no_asm) add: cfgLM.derivation_def cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgLM.derivation_def cfgLM.derivation_initial_def)
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
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation SSG c1 e2 c2" for SSd SSn SSG)
    apply(rename_tac nat a)(*strict*)
    prefer 2
    apply(rule cfgLM.step_detail_before_some_position)
      apply(rename_tac nat a)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(simp add: cfg_sub_def)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
   apply(force)
  apply(simp add: cfgLM.derivation_def cfgLM.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfg_initial_configurations_def get_configuration_def cfg_configurations_def cfg_sub_def)
  apply(force)
  done

lemma cfg_sub_preserves_derivation_initial_contra: "
  valid_cfg G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> (\<forall>i e c. d i = Some (pair e c) \<longrightarrow> set (option_to_list e) \<subseteq> cfg_productions G' \<and> c \<in> cfg_configurations G')
  \<Longrightarrow> cfgLM.derivation_initial G' d"
  apply(rule cfgLM.derivation_initialI)
   apply(simp add: cfgLM.derivation_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(case_tac "d 0")
     apply(clarsimp)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac option b)(*strict*)
    apply(simp add: cfgLM.derivation_initial_def)
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
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac nat option b)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
     apply(rename_tac nat option b)(*strict*)
     apply(force)
    apply(rename_tac nat option b)(*strict*)
    apply(force)
   apply(rename_tac nat option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat b e1 e2 c1)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac nat b e1 e2 c1 l r)(*strict*)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(simp add: option_to_list_def)
  apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def valid_cfg_def cfg_sub_def cfg_configurations_def get_configuration_def cfg_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def valid_cfg_def cfg_sub_def cfg_configurations_def get_configuration_def cfg_initial_configurations_def)
  done

lemma cfg_sub_preserves_derivation_initial_contra2: "
  valid_cfg G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> \<forall>e c c'. e \<in> cfg_productions G \<and> c \<in> cfg_configurations G' \<and> cfgLM_step_relation G c e c' \<longrightarrow> c' \<in> cfg_configurations G' \<and> e \<in> cfg_productions G'
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> set (option_to_list e) \<subseteq> cfg_productions G' \<and> c \<in> cfg_configurations G'"
  apply(induct i arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: option_to_list_def)
   apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def cfg_sub_def)
  apply(rename_tac i e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e c)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and n="i"
      and m="Suc i"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i e c)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac i e c)(*strict*)
    apply(force)
   apply(rename_tac i e c)(*strict*)
   apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(erule exE)+
  apply(rename_tac i e c e1 e2 c1 c2)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarify)
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
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="c"
      in allE)
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def option_to_list_def)
  done

lemma cfgLM_initial_marking_derivations_equal_implies_marked_language_equal: "
  valid_cfg Gi
  \<Longrightarrow> valid_cfg Go
  \<Longrightarrow> cfgLM.initial_marking_derivations Go = cfgLM.initial_marking_derivations Gi
  \<Longrightarrow> cfgLM.marked_language Go = cfgLM.marked_language Gi"
  apply(simp add: cfgLM.marked_language_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rule_tac x="d" in exI)
   apply(subgoal_tac "d \<in> ATS_Language0.initial_marking_derivations cfg_initial_configurations
            cfgLM_step_relation cfg_marking_condition Gi")
    prefer 2
    apply(rule_tac A="ATS_Language0.initial_marking_derivations cfg_initial_configurations
            cfgLM_step_relation cfg_marking_condition Go" in set_mp)
     apply(force)
    apply(simp add: cfgLM.initial_marking_derivations_def)
    apply(force)
   apply(simp add: cfgLM.initial_marking_derivations_def)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(subgoal_tac "d \<in> ATS_Language0.initial_marking_derivations cfg_initial_configurations
            cfgLM_step_relation cfg_marking_condition Go")
   prefer 2
   apply(rule_tac A="ATS_Language0.initial_marking_derivations cfg_initial_configurations
            cfgLM_step_relation cfg_marking_condition Gi" in set_mp)
    apply(force)
   apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(thin_tac "ATS_Language0.initial_marking_derivations cfg_initial_configurations
            cfgLM_step_relation cfg_marking_condition Go =
           ATS_Language0.initial_marking_derivations cfg_initial_configurations
            cfgLM_step_relation cfg_marking_condition Gi")
  apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(simp add: cfgLM.derivation_initial_def)
  apply(simp add: cfg_marked_effect_def)
  done

lemma cfg_sub_preserves_derivationLM: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgLM.derivation G d"
  apply(simp (no_asm) add: cfgLM.derivation_def cfgLM.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_def cfgLM.derivation_initial_def)
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule cfgLM.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(simp add: cfg_sub_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
  apply(force)
  done

lemma cfg_sub_preserves_derivation_initialLM: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgLM.derivation_initial G d"
  apply(rule cfgLM.derivation_initialI)
   apply(simp (no_asm) add: cfgLM.derivation_def cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgLM.derivation_def cfgLM.derivation_initial_def)
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
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation SSG c1 e2 c2" for SSd SSn SSG)
    apply(rename_tac nat a)(*strict*)
    prefer 2
    apply(rule cfgLM.step_detail_before_some_position)
      apply(rename_tac nat a)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(simp add: cfg_sub_def)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
   apply(force)
  apply(simp add: cfgLM.derivation_def cfgLM.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfg_initial_configurations_def get_configuration_def cfg_configurations_def cfg_sub_def)
  apply(force)
  done

lemma cfg_sub_preserves_cfgLM_accessible_nonterminals: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgLM_accessible_nonterminals G1 \<subseteq> cfgLM_accessible_nonterminals G2"
  apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: cfg_sub_def)
   apply(force)
  apply(rule_tac x="d" in exI)
  apply(rule conjI)
   apply(rule cfg_sub_preserves_derivation_initialLM)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

definition cfgLM_language_relevant_nonterminals :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgLM_language_relevant_nonterminals G \<equiv>
  {A | A d n e c.
  cfgLM.derivation_initial G d
  \<and> cfg_marking_condition G d
  \<and> d n = Some (pair e c)
  \<and> A \<in> setA (cfg_conf c)}"

lemma cfg_sub_cfgLM_language_relevant_nonterminals_hlp1: "
valid_cfg G \<Longrightarrow>
          valid_cfg G' \<Longrightarrow>
          cfg_sub G' G \<Longrightarrow>
          cfgLM_language_relevant_nonterminals G' \<subseteq>
          cfgLM_language_relevant_nonterminals G"
  apply(clarsimp)
  apply(simp add: cfgLM_language_relevant_nonterminals_def)
  apply(clarsimp)
  apply(rule_tac x="d" in exI)
  apply(rule context_conjI)
   apply (metis cfg_sub_preserves_derivation_initialLM)
  apply(rule context_conjI)
   apply (metis Int_iff cfgLM.derivation_initial_configurations cfg_marking_condition_def cfg_marking_configuration_def)
  apply(rule_tac x="n" in exI)
  apply(clarsimp)
  done

lemma cfgLM_maximum_of_domain_by_nonterminal_free: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB v\<rparr>)
  \<Longrightarrow> maximum_of_domain d n"
  apply(simp add: maximum_of_domain_def)
  apply(case_tac "d (Suc n)")
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac n="n" and m="Suc n" in cfgLM.step_detail_before_some_position)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply (metis liftB_with_nonterminal_inside)
  done

lemma cfg_sub_preserves_marked_language_cfgLM: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgLM.marked_language G1 \<subseteq> cfgLM.marked_language G2"
  apply(simp add: cfgLM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac x="d" in exI)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(rule cfg_sub_preserves_derivation_initialLM)
     apply(rename_tac x d)(*strict*)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply(force)
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: cfg_marked_effect_def)
  apply(rename_tac x d)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(rule cfg_sub_preserves_derivationLM)
     apply(rename_tac x d)(*strict*)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply(force)
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(rule_tac x="i" in exI)
  apply(clarsimp)
  apply(simp add: cfg_marking_configuration_def cfg_sub_def cfg_configurations_def)
  apply(force)
  done

lemma cfg_sub_preserves_derivation_reverse: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgLM.derivation G2 d
  \<Longrightarrow> (\<forall>i e c. d i = Some (pair e c) \<longrightarrow> setA (cfg_conf c) \<subseteq> cfg_nonterminals G1)
  \<Longrightarrow> (cfg_productions G1 = {p\<in> cfg_productions G2. prod_lhs p \<in> cfg_nonterminals G1 \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G1})
  \<Longrightarrow> cfgLM.derivation G1 d"
  apply(simp (no_asm) add: cfgLM.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_def)
   apply(erule_tac x="0" in allE)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="nat" and
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac nat e1 e2 c1 c2 l r cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac nat e1 e2 c1 c2 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 l r)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(erule_tac x="nat" in allE')
  apply(erule_tac x="Suc nat" in allE)
  apply(clarsimp)
  apply(simp add: setAConcat)
  done

lemma cfg_sub_preserves_derivation_initial_reverse: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgLM.derivation_initial G2 d
  \<Longrightarrow> (\<forall>i e c. d i = Some (pair e c) \<longrightarrow> setA (cfg_conf c) \<subseteq> cfg_nonterminals G1)
  \<Longrightarrow> (cfg_productions G1 = {p\<in> cfg_productions G2. prod_lhs p \<in> cfg_nonterminals G1 \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G1})
  \<Longrightarrow> cfgLM.derivation_initial G1 d"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac ?G1.0="G1" and ?G2.0="G2" in cfg_sub_preserves_derivation_reverse)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: cfgLM.derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: cfgLM.derivation_initial_def)
  apply(case_tac "d 0")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac conf)(*strict*)
  apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def cfg_sub_def)
  done

lemma cfg_sub_preserves_marked_language_reverse: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfg_events G1 = cfg_events G2
  \<Longrightarrow> (\<forall>d. cfgLM.derivation_initial G2 d \<longrightarrow> cfg_marking_condition G2 d \<longrightarrow> cfgLM.derivation_initial G1 d)
  \<Longrightarrow> cfgLM.marked_language G2 \<subseteq> cfgLM.marked_language G1"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: cfgLM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac x="d" in exI)
  apply(erule_tac x="d" in allE)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: cfg_marked_effect_def)
  apply(rename_tac x d)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def)
  apply(rename_tac x d)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(rule_tac x="i" in exI)
  apply(clarsimp)
  apply(simp add: cfg_marked_effect_def cfg_marking_configuration_def valid_cfg_def cfg_sub_def cfg_configurations_def)
  apply(clarsimp)
  done

lemma cfg_sub_equal_marked_language: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfg_events G1 = cfg_events G2
  \<Longrightarrow> (\<forall>d. cfgLM.derivation_initial G2 d \<longrightarrow> cfg_marking_condition G2 d \<longrightarrow> cfgLM.derivation_initial G1 d)
  \<Longrightarrow> cfgLM.marked_language G1 = cfgLM.marked_language G2"
  apply(rule antisym)
   prefer 2
   apply(rule cfg_sub_preserves_marked_language_reverse)
       prefer 3
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule cfg_sub_preserves_marked_language_cfgLM)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfgLM_no_step_without_nonterms_maximum_of_domain: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> setA (cfg_conf c) = {}
  \<Longrightarrow> maximum_of_domain d n"
  apply(simp add: maximum_of_domain_def)
  apply(rule cfgLM_no_step_without_nonterms)
     apply(force)+
  done

lemma last_head_occurence_of_nonterminal: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e \<lparr>cfg_conf=l@[teA A]@r\<rparr>)
  \<Longrightarrow> d j = Some (pair ej \<lparr>cfg_conf=liftB w\<rparr>)
  \<Longrightarrow> \<exists>k ek ck s \<alpha>.
          i \<le> k \<and>
          k < j \<and>
          d k = Some (pair ek ck) \<and> cfg_conf ck = liftB \<alpha> @ teA A # s"
  apply(subgoal_tac "maximum_of_domain d j")
   prefer 2
   apply(rule cfgLM_no_step_without_nonterms_maximum_of_domain)
      apply(force)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(force)
   apply(clarsimp)
   apply(rule setA_liftB)
  apply(subgoal_tac "i<j")
   prefer 2
   apply(case_tac "i<j")
    apply(force)
   apply(case_tac "i=j")
    apply(clarsimp)
    apply (metis liftBSplit list.distinct(1) maxTermPrefix_drop_tail maxTermPrefix_term_string self_append_conv)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      n="j"
      and m="i"
      in cfgLM.step_detail_before_some_position)
      apply(rule_tac d="d" in cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rename_tac e2 c2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e2 c2)(*strict*)
    prefer 2
    apply(rule_tac n="j" in cfgLM_no_step_without_nonterms)
       apply(rename_tac e2 c2)(*strict*)
       apply(force)
      apply(rename_tac e2 c2)(*strict*)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(rename_tac e2 c2)(*strict*)
     apply(force)
    apply(rename_tac e2 c2)(*strict*)
    apply(clarsimp)
    apply(rule setA_liftB)
   apply(rename_tac e2 c2)(*strict*)
   apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac P="%n. \<exists>e c w1 w2. d (j-n) = Some (pair e c) \<and> A \<in> setA (cfg_conf c)" and n="j-i" in ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(clarsimp)
  apply(rename_tac k ea c)(*strict*)
  apply(case_tac k)
   apply(rename_tac k ea c)(*strict*)
   apply(clarsimp)
   apply (metis setA_liftB_empty empty_iff)
  apply(rename_tac k ea c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea c nat)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ea c nat)(*strict*)
   prefer 2
   apply(rule_tac
      n="j-Suc nat"
      and m="j"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac ea c nat)(*strict*)
     apply(rule_tac d="d" in cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac ea c nat)(*strict*)
    apply(force)
   apply(rename_tac ea c nat)(*strict*)
   apply(force)
  apply(rename_tac ea c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea c nat e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(erule_tac x="nat" in allE)
  apply(clarsimp)
  apply(rename_tac ea c nat e2 c2 la ra)(*strict*)
  apply(rule_tac x="j-Suc nat" in exI)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac ea c nat e2 c2 la ra cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac ea c nat e2 c2 la ra cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea nat e2 la ra)(*strict*)
  apply(rule conjI)
   apply(rename_tac ea nat e2 la ra)(*strict*)
   apply(force)
  apply(rename_tac ea nat e2 la ra)(*strict*)
  apply(subgoal_tac "\<exists>w. liftB w= la")
   apply(rename_tac ea nat e2 la ra)(*strict*)
   prefer 2
   apply(rule_tac x="filterB la" in exI)
   apply(rule liftBDeConv2)
   apply(force)
  apply(rename_tac ea nat e2 la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea nat e2 ra wa)(*strict*)
  apply(simp add: setAConcat)
  apply(rule_tac x="ra" in exI)
  apply(rule_tac x="wa" in exI)
  apply(clarsimp)
  apply(subgoal_tac "Suc (j - Suc nat) = j-nat")
   apply(rename_tac ea nat e2 ra wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ea nat e2 ra wa)(*strict*)
  apply(clarsimp)
  apply(simp add: setAConcat)
  done

lemma cfg_cfgLM_initial_marking_derivations_subset_implies_cfgLM_language_relevant_nonterminals_subset: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfgLM.initial_marking_derivations G2 \<subseteq> cfgLM.initial_marking_derivations G1
  \<Longrightarrow> cfgLM_language_relevant_nonterminals G2 \<subseteq> cfgLM_language_relevant_nonterminals G1"
  apply(simp add: cfgLM_language_relevant_nonterminals_def)
  apply(clarsimp)
  apply(subgoal_tac "d \<in> ATS_Language0.initial_marking_derivations cfg_initial_configurations
           cfgLM_step_relation cfg_marking_condition G1")
   prefer 2
   apply(rule_tac A="ATS_Language0.initial_marking_derivations cfg_initial_configurations
           cfgLM_step_relation cfg_marking_condition G2" in set_mp)
    apply(force)
   apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(thin_tac "ATS_Language0.initial_marking_derivations cfg_initial_configurations
        cfgLM_step_relation cfg_marking_condition G2
       \<subseteq> ATS_Language0.initial_marking_derivations cfg_initial_configurations
           cfgLM_step_relation cfg_marking_condition G1")
  apply(rule_tac x="d" in exI)
  apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(rule_tac x="n" in exI)
  apply(clarsimp)
  done

lemma cfg_cfgLM_initial_marking_derivations_equal_implies_cfgLM_language_relevant_nonterminals_equal: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfgLM.initial_marking_derivations G2 = cfgLM.initial_marking_derivations G1
  \<Longrightarrow> cfgLM_language_relevant_nonterminals G2 = cfgLM_language_relevant_nonterminals G1"
  apply(rule antisym)
   apply(rule cfg_cfgLM_initial_marking_derivations_subset_implies_cfgLM_language_relevant_nonterminals_subset)
     apply(force)
    apply(force)
   apply(force)
  apply(rule cfg_cfgLM_initial_marking_derivations_subset_implies_cfgLM_language_relevant_nonterminals_subset)
    apply(force)
   apply(force)
  apply(force)
  done

definition cfgLM_language_relevant_productions :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label set"
  where
    "cfgLM_language_relevant_productions G \<equiv>
  {e | d n e c.
  cfgLM.derivation_initial G d
  \<and> cfg_marking_condition G d
  \<and> d n = Some (pair (Some e) c)}"

lemma cfg_cfgLM_initial_marking_derivations_subset_implies_cfgLM_language_relevant_productions_subset: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfgLM.initial_marking_derivations G2 \<subseteq> cfgLM.initial_marking_derivations G1
  \<Longrightarrow> cfgLM_language_relevant_productions G2 \<subseteq> cfgLM_language_relevant_productions G1"
  apply(simp add: cfgLM_language_relevant_productions_def)
  apply(clarsimp)
  apply(subgoal_tac "d \<in> ATS_Language0.initial_marking_derivations cfg_initial_configurations
           cfgLM_step_relation cfg_marking_condition G1")
   prefer 2
   apply(rule_tac A="ATS_Language0.initial_marking_derivations cfg_initial_configurations
           cfgLM_step_relation cfg_marking_condition G2" in set_mp)
    apply(force)
   apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(thin_tac "ATS_Language0.initial_marking_derivations cfg_initial_configurations
        cfgLM_step_relation cfg_marking_condition G2
       \<subseteq> ATS_Language0.initial_marking_derivations cfg_initial_configurations
           cfgLM_step_relation cfg_marking_condition G1")
  apply(rule_tac x="d" in exI)
  apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(rule_tac x="n" in exI)
  apply(clarsimp)
  done

lemma cfg_cfgLM_initial_marking_derivations_equal_implies_cfgLM_language_relevant_productions_equal: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfgLM.initial_marking_derivations G2 = cfgLM.initial_marking_derivations G1
  \<Longrightarrow> cfgLM_language_relevant_productions G2 = cfgLM_language_relevant_productions G1"
  apply(rule antisym)
   apply(rule cfg_cfgLM_initial_marking_derivations_subset_implies_cfgLM_language_relevant_productions_subset)
     apply(force)
    apply(force)
   apply(force)
  apply(rule cfg_cfgLM_initial_marking_derivations_subset_implies_cfgLM_language_relevant_productions_subset)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfgLM_accessible_nonterminals_lhs_makes_prod_cfgLM_accessible_productions: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_lhs p \<in> cfgLM_accessible_nonterminals G
  \<Longrightarrow> p \<in> cfgLM_accessible_productions G"
  apply(simp add: cfgLM_accessible_productions_def cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac d n c w1 w2)(*strict*)
  apply(simp add: cfgLM.get_accessible_destinations_def cfg_destination_def cfg_get_destinations_def)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(rename_tac d n c w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac d n c w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d n c w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n c w1 w2 option)(*strict*)
  apply(case_tac c)
  apply(rename_tac d n c w1 w2 option cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n w1 w2 option)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = liftB w1 @ teA (prod_lhs p) # w2\<rparr> p \<lparr>cfg_conf = liftB w1 @ (prod_rhs p) @ w2\<rparr>) n"
      in exI)
  apply(rule conjI)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac d n w1 w2 option)(*strict*)
     apply(force)
    apply(rename_tac d n w1 w2 option)(*strict*)
    apply(force)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac d n w1 w2 option)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac d n w1 w2 option)(*strict*)
    apply(rule cfgLM.der2_is_derivation)
    apply(simp add: cfgLM_step_relation_def)
    apply(rule_tac
      x="liftB w1"
      in exI)
    apply(rule_tac
      x="w2"
      in exI)
    apply(clarsimp)
    apply (metis setA_liftB)
   apply(rename_tac d n w1 w2 option)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac d n w1 w2 option)(*strict*)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(rule_tac
      x="Some p"
      in exI)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  done

lemma CFGLM_composition_of_two_derivation_with_context: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d1
  \<Longrightarrow> d1 0 = Some (pair None c1)
  \<Longrightarrow> d1 n1 = Some (pair e1 c1')
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> d2 0 = Some (pair None c2)
  \<Longrightarrow> d2 n2 = Some (pair e2 c2')
  \<Longrightarrow> setA (cfg_conf c1') = {}
  \<Longrightarrow> \<exists>d e.
  cfgLM.derivation G d
  \<and> d 0 = Some (pair None \<lparr>cfg_conf=(liftB x1)@(cfg_conf c1)@(liftB x2)@(cfg_conf c2)@y\<rparr>)
  \<and> d (n1+n2) = Some (pair e \<lparr>cfg_conf=(liftB x1)@(cfg_conf c1')@(liftB x2)@(cfg_conf c2')@y\<rparr>)"
  apply(rule_tac
      x="\<lambda>n. if (n\<le>n1) then Some (pair ((get_label(d1 n))) \<lparr>cfg_conf=(liftB x1)@(cfg_conf(the(get_configuration(d1 n))))@(liftB x2)@(cfg_conf c2)@y\<rparr>) else (if (n\<le>n1+n2) then Some (pair ((get_label(d2 ((n-n1))))) \<lparr>cfg_conf=(liftB x1)@(cfg_conf c1')@(liftB x2)@(cfg_conf(the(get_configuration(d2((n-n1))))))@y\<rparr>) else None)"
      in exI)
  apply(simp (no_asm) add: cfgLM.derivation_def)
  apply(case_tac n2)
   apply(clarsimp)
   apply(rule conjI)
    prefer 2
    apply(simp add: get_label_def get_configuration_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(rule conjI)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(case_tac i)
     apply(rename_tac i)(*strict*)
     apply(clarsimp)
     apply(simp add: get_label_def get_configuration_def)
    apply(rename_tac i nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat)(*strict*)
    apply(simp add: get_label_def get_configuration_def)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 nat = Some (pair e1 c1) \<and> d1 (Suc nat) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
     apply(rename_tac nat)(*strict*)
     prefer 2
     apply(rule_tac
      m="n1"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1a e2 c1a c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac nat e1a e2 c1a c2 l r)(*strict*)
    apply(case_tac c2)
    apply(rename_tac nat e1a e2 c1a c2 l r cfg_confa)(*strict*)
    apply(case_tac c1a)
    apply(rename_tac nat e1a e2 c1a c2 l r cfg_confa cfg_confaa)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1a e2 l r)(*strict*)
    apply(simp add: get_label_def get_configuration_def)
    apply(rule_tac
      x="liftB x1 @ l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat)
    apply (metis setA_liftB)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(simp add: get_label_def get_configuration_def)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat i)(*strict*)
  apply(rule conjI)
   apply(rename_tac nat i)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac nat i)(*strict*)
    apply(clarsimp)
    apply(case_tac i)
     apply(rename_tac nat i)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat)(*strict*)
     apply(simp add: get_label_def get_configuration_def)
    apply(rename_tac nat i nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat nata)(*strict*)
    apply(simp add: get_label_def get_configuration_def)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 nata = Some (pair e1 c1) \<and> d1 (Suc nata) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
     apply(rename_tac nat nata)(*strict*)
     prefer 2
     apply(rule_tac
      m="n1"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac nat nata)(*strict*)
       apply(force)
      apply(rename_tac nat nata)(*strict*)
      apply(force)
     apply(rename_tac nat nata)(*strict*)
     apply(force)
    apply(rename_tac nat nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat nata e1a e2a c1a c2a)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac nat nata e1a e2a c1a c2a l r)(*strict*)
    apply(case_tac c1a)
    apply(rename_tac nat nata e1a e2a c1a c2a l r cfg_confa)(*strict*)
    apply(case_tac c2a)
    apply(rename_tac nat nata e1a e2a c1a c2a l r cfg_confa cfg_confaa)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat nata e1a e2a l r)(*strict*)
    apply(simp add: get_label_def get_configuration_def)
    apply(rule_tac
      x="liftB x1 @ l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat)
    apply (metis setA_liftB)
   apply(rename_tac nat i)(*strict*)
   apply(clarsimp)
   apply(case_tac i)
    apply(rename_tac nat i)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat i nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat nata)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat nata)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "nata=n1")
     apply(rename_tac nat nata)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac nat nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 0 = Some (pair e1 c1) \<and> d2 (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
     apply(rename_tac nat)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e2a c2a)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(simp add: get_label_def get_configuration_def)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac nat e2a c2a l r)(*strict*)
    apply(rule_tac
      x="liftB x1 @ cfg_conf c1' @ liftB x2 @ l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat)
    apply(rule conjI)
     apply(rename_tac nat e2a c2a l r)(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac nat e2a c2a l r)(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac nat nata)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (nata-n1) = Some (pair e1 c1) \<and> d2 (Suc (nata-n1)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
    apply(rename_tac nat nata)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac nat nata)(*strict*)
      apply(force)
     apply(rename_tac nat nata)(*strict*)
     apply(force)
    apply(rename_tac nat nata)(*strict*)
    apply(force)
   apply(rename_tac nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat nata e1a e2a c1a c2a)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(simp add: get_label_def get_configuration_def)
   apply(clarsimp)
   apply(rename_tac nat nata e1a e2a c1a c2a l r)(*strict*)
   apply(case_tac c1a)
   apply(rename_tac nat nata e1a e2a c1a c2a l r cfg_confa)(*strict*)
   apply(case_tac c2a)
   apply(rename_tac nat nata e1a e2a c1a c2a l r cfg_confa cfg_confaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat nata e1a e2a l r)(*strict*)
   apply(subgoal_tac "Suc (nata - n1)=Suc nata-n1")
    apply(rename_tac nat nata e1a e2a l r)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgLM_step_relation_def)
    apply(simp add: get_label_def get_configuration_def)
    apply(rule_tac
      x="liftB x1 @ cfg_conf c1' @ liftB x2 @ l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat)
    apply(rule conjI)
     apply(rename_tac nat nata e1a e2a l r)(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac nat nata e1a e2a l r)(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac nat nata e1a e2a l r)(*strict*)
   apply(force)
  apply(rename_tac nat i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac nat i)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat i nata)(*strict*)
  apply(clarsimp)
  done

lemma CFGLM_terminals_stay_at_front: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> d (n+m) = Some (pair e2 c2)
  \<Longrightarrow> cfg_conf c1=liftB w@v
  \<Longrightarrow> \<exists>v. cfg_conf c2=liftB w@v"
  apply(induct m arbitrary: e2 c2)
   apply(rename_tac e2 c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac m e2 c2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (n+m) = Some (pair e1 c1) \<and> d (Suc (n+m)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac m e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (n+m)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac m e2 c2)(*strict*)
     apply(force)
    apply(rename_tac m e2 c2)(*strict*)
    apply(force)
   apply(rename_tac m e2 c2)(*strict*)
   apply(force)
  apply(rename_tac m e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a c1a)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a c1a va)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a c1a va l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac m c2 e1a e2a c1a va l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a c1 va l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac m c2 e1a e2a c1 va l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a va l r)(*strict*)
  apply(subgoal_tac "\<exists>v0. liftB v0=l")
   apply(rename_tac m c2 e1a e2a va l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac m c2 e1a e2a va l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a va r v0)(*strict*)
  apply(thin_tac "setA (liftB v0) = {}")
  apply(subgoal_tac "prefix w v0")
   apply(rename_tac m c2 e1a e2a va r v0)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_drop_tail maxTermPrefix_shift maxTermPrefix_term_string prefix_append)
  apply(rename_tac m c2 e1a e2a va r v0)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a va r c)(*strict*)
  apply(case_tac c2)
  apply(rename_tac m c2 e1a e2a va r c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1a e2a va r c)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma empty_start_then_cfgLM_derivation_is_empty: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> n=0"
  apply(case_tac n)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  done

lemma cfgLM_no_step_without_nontermsX: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> setA (cfg_conf c)={}
  \<Longrightarrow> d (n+m) \<noteq> None
  \<Longrightarrow> m=0"
  apply(case_tac m)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+m"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat y e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat y e2 c2 l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac nat y e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat y e2 c2 l r)(*strict*)
  apply (metis elemInsetA emptyE)
  done

lemma cfgLM_terminal_preserved: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> setB (cfg_conf c1)\<noteq>{}
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> d (n+m) = Some (pair e2 c2)
  \<Longrightarrow> setB (cfg_conf c2)\<noteq>{}"
  apply(induct m arbitrary: e2 c2)
   apply(rename_tac e2 c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac m e2 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (n+m) = Some (pair e1 c1) \<and> d (Suc (n+m)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac m e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (n+m)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac m e2 c2)(*strict*)
     apply(force)
    apply(rename_tac m e2 c2)(*strict*)
    apply(force)
   apply(rename_tac m e2 c2)(*strict*)
   apply(force)
  apply(rename_tac m e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a c1a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac m c2 e1a e2a c1a l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac m c2 e1a e2a c1a l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1a e2a c1a l r)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac m e1a e2a c1a l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1a e2a l r)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = l @ teA (prod_lhs e2a) # r\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: setBConcat)
  done

lemma cfgLM_terminal_preserved2: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e1 c)
  \<Longrightarrow> d (n+m) = Some (pair e2 \<lparr>cfg_conf=[]\<rparr>)
  \<Longrightarrow> setB (cfg_conf c)={}"
  apply(case_tac "setB (cfg_conf c)={}")
   apply(force)
  apply(subgoal_tac "False")
   apply(force)
  apply(subgoal_tac "setB (cfg_conf \<lparr>cfg_conf=[]\<rparr>)\<noteq>{}")
   apply(force)
  apply(rule cfgLM_terminal_preserved)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfgLM_terminals_preserved: "
  valid_cfg G'
  \<Longrightarrow> cfgLM.derivation G' dc
  \<Longrightarrow> dc 0 = Some (pair None c1)
  \<Longrightarrow> dc nc = Some (pair ec c2)
  \<Longrightarrow> setB (cfg_conf c1) \<subseteq> setB (cfg_conf c2)"
  apply(induct nc arbitrary: ec c2)
   apply(rename_tac ec c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac nc ec c2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dc nc = Some (pair e1 c1) \<and> dc (Suc nc) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G' c1 e2 c2")
   apply(rename_tac nc ec c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nc"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac nc ec c2)(*strict*)
     apply(force)
    apply(rename_tac nc ec c2)(*strict*)
    apply(force)
   apply(rename_tac nc ec c2)(*strict*)
   apply(force)
  apply(rename_tac nc ec c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac nc c2 x e1 e2 c1a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nc c2 x e1 e2 c1a l r)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac nc c2 x e1 e2 c1a l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nc c2 x e1 e2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac nc c2 x e1 e2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(case_tac c2)
  apply(rename_tac nc c2 x e1 e2 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nc x e1 e2 l r cfg_confa)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="\<lparr>cfg_conf = l @ teA (prod_lhs e2) # r\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac nc x e1 e2 l r cfg_conf)(*strict*)
  apply(rule_tac
      A="setB cfg_conf"
      in set_mp)
   apply(rename_tac nc x e1 e2 l r cfg_conf)(*strict*)
   apply(simp add: setBConcat)
   apply(force)
  apply(rename_tac nc x e1 e2 l r cfg_conf)(*strict*)
  apply(simp add: setBConcat)
  done

lemma cfgLM_no_terminals_at_beginning: "
  valid_cfg G'
  \<Longrightarrow> cfgLM.derivation G' dc
  \<Longrightarrow> dc 0 = Some (pair None \<lparr>cfg_conf = c\<rparr>)
  \<Longrightarrow> dc nc = Some (pair ec \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> setB c = {}"
  apply(subgoal_tac "setB (cfg_conf \<lparr>cfg_conf=c\<rparr>) \<subseteq> setB (cfg_conf \<lparr>cfg_conf = []\<rparr>)")
   apply(force)
  apply(rule cfgLM_terminals_preserved)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

definition CFGlmEliminators :: "('a,'b) cfg \<Rightarrow> ('a,'b)DT_two_elements option \<Rightarrow> ('a,'b)cfg_step_label list set" where
  "CFGlmEliminators G \<alpha> \<equiv> {\<pi>. \<exists>d n e w.
  cfgLM.derivation G d
  \<and> cfgLM.belongs G d
  \<and> d 0 = Some (pair None \<lparr>cfg_conf=(option_to_list \<alpha>)\<rparr>)
  \<and> d n = Some (pair e \<lparr>cfg_conf=liftB w\<rparr>)
  \<and> \<pi>=map the (get_labels d n)}"

function (domintros) CFGlm2rm :: "('a,'b) cfg \<Rightarrow> ('a,'b)cfg_step_label list \<Rightarrow> ('a,'b)cfg_step_label list" where
  "CFGlm2rm G [] = []"
| "CFGlm2rm G (r#\<pi>') = (
  let \<pi>s=SOME \<pi>s.
  (foldl ((@)) [] \<pi>s) = \<pi>'
  \<and> (length \<pi>s) = (length (prod_rhs r))
  \<and> (\<forall>i<length \<pi>s. (\<pi>s!i) \<in> CFGlmEliminators G (Some((prod_rhs r)!i)))
  in
  r#(foldl ((@)) [] (map (\<lambda>x. CFGlm2rm G x) (rev \<pi>s)))
  )"
  by pat_completeness auto

lemma lemma_4_6_existence: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> \<exists>\<pi>s ws.
  foldl (@) [] \<pi>s = \<pi>
  \<and> length \<pi>s = length \<alpha>
  \<and> foldl (@) [] ws = w
  \<and> length ws = length \<alpha>
  \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'.
  cfgLM.derivation G d'
  \<and> cfgLM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=\<alpha>!i\<rparr>)
  \<and> d' n' = Some (pair e' \<lparr>cfg_conf=liftB (ws!i)\<rparr>)
  \<and> \<pi>s!i = map the (get_labels d' n'))"
  apply(induct n arbitrary: d \<pi> \<alpha> w e)
   apply(rename_tac d \<pi> \<alpha> w e)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<alpha> w)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "nat_seq (Suc 0) 0=[]")
    apply(rename_tac d \<alpha> w)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="map (\<lambda>x. []) \<alpha>"
      in exI)
    apply(rule context_conjI)
     apply(rename_tac d \<alpha> w)(*strict*)
     apply(rule foldl_empty)
     apply(rename_tac d \<alpha> w a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d \<alpha> w)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac d \<alpha> w)(*strict*)
     apply(simp add: get_label_def)
    apply(rename_tac d \<alpha> w)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="map filterB \<alpha>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d \<alpha> w)(*strict*)
     apply(rule liftB_inj)
     apply(rule sym)
     apply(rule_tac
      t="liftB w"
      and s="foldl (@) [] \<alpha>"
      in ssubst)
      apply(rename_tac d \<alpha> w)(*strict*)
      apply(force)
     apply(rename_tac d \<alpha> w)(*strict*)
     apply(rule_tac
      t="liftB (foldl (@) [] (map filterB \<alpha>))"
      and s="(foldl (@) [] (map liftB (map filterB \<alpha>)))"
      in ssubst)
      apply(rename_tac d \<alpha> w)(*strict*)
      apply(rule distrib_liftB_foldl)
     apply(rename_tac d \<alpha> w)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="(map (liftB \<circ> filterB) \<alpha>)"
      and s="\<alpha>"
      in ssubst)
      apply(rename_tac d \<alpha> w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d \<alpha> w)(*strict*)
     apply(rule listEqI)
      apply(rename_tac d \<alpha> w)(*strict*)
      apply (metis length_map)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "setA (\<alpha>!i)={}")
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply (metis liftBDeConv2)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule order_antisym)
      apply(rename_tac d \<alpha> w i)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule_tac
      B="setA (liftB w)"
      in subset_trans)
      apply(rename_tac d \<alpha> w i)(*strict*)
      prefer 2
      apply(simp (no_asm))
      apply(rule setA_liftB)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(subgoal_tac "set(\<alpha>!i)\<subseteq> set(liftB w)")
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply(rule set_subset_to_setA_subset)
      apply(force)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule_tac
      t="liftB w"
      and s="foldl (@) [] \<alpha>"
      in ssubst)
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply(force)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule set_nth_foldl)
     apply(force)
    apply(rename_tac d \<alpha> w)(*strict*)
    apply(rule conjI)
     apply(rename_tac d \<alpha> w)(*strict*)
     apply (metis length_map)
    apply(rename_tac d \<alpha> w)(*strict*)
    apply(clarsimp)
    apply(rename_tac d \<alpha> w i)(*strict*)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf=\<alpha>!i\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d \<alpha> w i)(*strict*)
    apply(rule conjI)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule cfgLM.der1_belongs)
     apply(subgoal_tac "\<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr> \<in> cfg_configurations G")
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply(simp add: cfg_configurations_def)
      apply(rule conjI)
       apply(rename_tac d \<alpha> w i)(*strict*)
       apply(rule_tac
      B="setA (foldl (@) [] \<alpha>)"
      in subset_trans)
        apply(rename_tac d \<alpha> w i)(*strict*)
        apply(rule set_subset_to_setA_subset)
        apply(rule set_nth_foldl)
        apply(force)
       apply(rename_tac d \<alpha> w i)(*strict*)
       apply(force)
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply(rule_tac
      B="setB (foldl (@) [] \<alpha>)"
      in subset_trans)
       apply(rename_tac d \<alpha> w i)(*strict*)
       apply(rule set_subset_to_setB_subset)
       apply(rule set_nth_foldl)
       apply(force)
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply(force)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule cfgLM.belongs_configurations)
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply(force)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(force)
    apply(rename_tac d \<alpha> w i)(*strict*)
    apply(rule conjI)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d \<alpha> w i)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(rule conjI)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule_tac
      x="None"
      in exI)
     apply(simp add: der1_def)
     apply(subgoal_tac "setA (\<alpha>!i) = {}")
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply (metis liftBDeConv2)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule order_antisym)
      apply(rename_tac d \<alpha> w i)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule_tac
      B="setA (foldl (@) [] \<alpha>)"
      in subset_trans)
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply(rule set_subset_to_setA_subset)
      apply(rule set_nth_foldl)
      apply(force)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule_tac
      t="foldl (@) [] \<alpha>"
      and s="liftB w"
      in ssubst)
      apply(rename_tac d \<alpha> w i)(*strict*)
      apply(force)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply (metis setA_liftB empty_subsetI)
    apply(rename_tac d \<alpha> w i)(*strict*)
    apply (metis)
   apply(rename_tac d \<alpha> w)(*strict*)
   apply (metis nat_seqEmpty zero_less_Suc)
  apply(rename_tac n d \<pi> \<alpha> w e)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> w e)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac n d \<alpha> w e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac n d \<alpha> w e)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> w e)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> w e)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> w e e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> w e e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac n d \<alpha> w e e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> w e e2 l r)(*strict*)
  apply(subgoal_tac "\<exists>n l1 l2 r1 r2. n<length \<alpha> \<and>l1=foldl (@) [] (take n \<alpha>) \<and> l1@l2=l \<and> r1=foldl (@) [] (drop (Suc n) \<alpha>) \<and> r=r2@r1 \<and> \<alpha>!n=l2@[teA(prod_lhs e2)]@r2")
   apply(rename_tac n d \<alpha> w e e2 l r)(*strict*)
   prefer 2
   apply(rule single_element_in_some_slice)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
  apply(erule_tac
      x="derivation_drop d (Suc 0)"
      in meta_allE)
  apply(erule_tac
      x="map the (get_labels (derivation_drop d (Suc 0)) n)"
      in meta_allE)
  apply(erule_tac
      x="(take na \<alpha>)@[l2 @ prod_rhs e2 @ r2]@(drop (Suc na) \<alpha>)"
      in meta_allE)
  apply(erule_tac
      x="w"
      in meta_allE)
  apply(erule_tac
      x="(case n of 0 \<Rightarrow> None | Suc n \<Rightarrow> e)"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(rule cfgLM.derivation_drop_preserves_derivation_prime)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(rule cfgLM.derivation_drop_preserves_belongs)
     apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
  apply(subgoal_tac "foldl (@) [] (take na \<alpha> @ [l2 @ prod_rhs e2 @ r2] @ drop (Suc na) \<alpha>)=foldl (@) [] (take na \<alpha>) @ l2 @ prod_rhs e2 @ r2 @ foldl (@) [] (drop (Suc na) \<alpha>)")
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   prefer 2
   apply(rule_tac
      t="foldl (@) [] (take na \<alpha> @ [l2 @ prod_rhs e2 @ r2] @ drop (Suc na) \<alpha>)"
      and s=" (foldl (@) [] (take na \<alpha>))@(foldl (@) [] ([l2 @ prod_rhs e2@ r2] @ drop (Suc na) \<alpha>))"
      in ssubst)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
    apply(rule foldl_distrib_append)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(rule_tac
      t="foldl (@) [] ([l2 @ prod_rhs e2 @ r2] @ drop (Suc na) \<alpha>)"
      and s="(foldl (@) [] ([l2 @ prod_rhs e2 @ r2]))@(foldl (@) [] (drop (Suc na) \<alpha>))"
      in ssubst)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
    apply(rule foldl_distrib_append)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(simp add: derivation_drop_def)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(simp add: derivation_drop_def)
   apply(case_tac n)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2 nat)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
  apply(erule exE)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
  apply(rule_tac
      x="(take na \<pi>s @ [e2#(\<pi>s!na)] @ drop (Suc na) \<pi>s)"
      in exI)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
   apply(rule_tac
      t="foldl (@) [] (take na \<pi>s @ [e2 # \<pi>s ! na] @ drop (Suc na) \<pi>s)"
      and s="e2#(foldl (@) [] \<pi>s)"
      in ssubst)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
    prefer 2
    apply(rule_tac
      t="foldl (@) [] \<pi>s"
      and s="map the (get_labels (derivation_drop d (Suc 0)) n)"
      in ssubst)
     apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
    apply(simp (no_asm) add: get_labels_def)
    apply(rule listEqI)
     apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
     apply (metis gr0I list.size(3) nat_seqEmpty nat_seq_length_Suc0 zero_less_Suc)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s i)(*strict*)
    apply(simp (no_asm))
    apply(rule impI)
    apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc n)) ! i"
      and s="(the \<circ> (\<lambda>i. get_label (d i))) ((nat_seq (Suc 0) (Suc n)) ! i)"
      in ssubst)
     apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s i)(*strict*)
     apply(rule nth_map)
     apply (metis gr0I length_0_conv nat_seqEmpty nat_seq_length_Suc0 zero_less_Suc)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s i)(*strict*)
    apply(case_tac i)
     apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s i)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
     apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = Suc 0 # (nat_seq (Suc (Suc 0)) (Suc n))")
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
      apply(clarsimp)
      apply(simp add: get_label_def)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
     apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s i nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
    apply(subgoal_tac "nat_seq (Suc 0) (Suc n) ! Suc nat = (Suc 0)+(Suc nat)")
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
      apply(force)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
     apply (metis Suc_leI diff_Suc_Suc less_zeroE list.size(3) minus_nat.diff_0 nat_seqEmpty nat_seq_length_Suc0 not_less_eq)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
    apply(subgoal_tac "nat_seq (Suc 0) n ! nat = (Suc 0)+nat")
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
      apply (metis Suc_leI gr0I lessI list.size(3) nat_seqEmpty not_less0)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
     apply (metis Nat.add_0_right Suc_leI add_Suc_right add_leD2 gr0I le_diff_conv2 length_0_conv nat_seqEmpty nat_seq_length_Suc0 zero_less_Suc)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s nat ws)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_drop_def)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
   apply(rule empty_foldl_ignore)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
   apply(rule foldl_empty)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s a)(*strict*)
   apply(case_tac a)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s a)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s a aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s aa list ws)(*strict*)
   apply(subgoal_tac "\<exists>na'<(length(take na \<pi>s)). aa#list=(take na \<pi>s)!na'")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s aa list ws)(*strict*)
    prefer 2
    apply (metis in_set_conv_nth)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s aa list ws)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s aa list ws na')(*strict*)
   apply(erule_tac
      x="na'"
      in allE)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' n' e' z zs)(*strict*)
   apply(case_tac n')
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' n' e' z zs)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' z zs)(*strict*)
    apply(simp add: get_labels_def)
    apply(clarsimp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' za zsa)(*strict*)
    apply (metis lessI list.simps(2) nat_seqEmpty)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' n' e' z zs nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d' 0 = Some (pair e1 c1) \<and> d' (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat)(*strict*)
      apply(force)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
   apply(subgoal_tac "prod_lhs e2a \<in> setA (foldl (@) [] (take na \<alpha>) @ l2)")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
    apply(subgoal_tac "prod_lhs e2a \<notin>setA (foldl (@) [] (take na \<alpha>) @ l2)")
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
    apply(rule_tac
      t="setA (foldl (@) [] (take na \<alpha>) @ l2)"
      and s="{}"
      in ssubst)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
   apply(rule_tac
      A="setA (foldl (@) [] (take na \<alpha>))"
      in set_mp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
    apply (metis setA_Concat2 subset_iff_psubset_eq)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
   apply(subgoal_tac "teA (prod_lhs e2a) \<in> set (foldl (@) [] (take na \<alpha>))")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
    apply (metis setA_set_not)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
   apply(rule_tac
      A="set ((take na \<alpha>)!na')"
      in set_mp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
    apply(rule set_nth_foldl)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
   apply(rule_tac
      t="take na \<alpha> ! na'"
      and s="(take na \<alpha> @ (l2 @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>) ! na'"
      in ssubst)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
    apply(rule nth_appendX)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws na' d' e' z zs nat e2a c2 l r)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
  apply(clarify)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(rule_tac
      x="ws"
      in exI)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s ws)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(subgoal_tac "min (length \<alpha>) na = na")
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s ws)(*strict*)
   prefer 2
   apply(rule Orderings.min_absorb2)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(subgoal_tac "(Suc (length \<alpha> - Suc 0)) = length \<alpha>")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
  apply(thin_tac "min (length \<alpha>) na = na")
  apply(thin_tac "Suc (length \<alpha> - Suc 0) = length \<alpha>")
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
  apply(case_tac "i=na")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   prefer 2
   apply(rule_tac
      x="d'"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply (metis nth_list_update_neq upd_conv_take_nth_drop)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(rule_tac
      x="n'"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="(take na \<pi>s @ (e2 # \<pi>s ! na) # drop (Suc na) \<pi>s) ! i"
      and s="\<pi>s!i"
      in ssubst)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply (metis nth_list_update_neq upd_conv_take_nth_drop)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = l2 @ teA (prod_lhs e2) # r2\<rparr> e2 \<lparr>cfg_conf = l2 @ prod_rhs e2 @ r2\<rparr>) d' (Suc 0)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="l2"
      in exI)
     apply(rule_tac
      x="r2"
      in exI)
     apply(clarsimp)
     apply(simp add: setAConcat)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(simp add: der2_def)
   apply(rule hlp1)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
      apply(force)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
    apply(rule_tac
      s="\<alpha> ! na"
      in ssubst)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr> \<in> cfg_configurations G")
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
     apply(subgoal_tac "set (\<alpha>!na) \<subseteq> set (foldl (@) [] \<alpha>)")
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
      apply(subgoal_tac "setA (\<alpha>!na) \<subseteq> setA (foldl (@) [] \<alpha>)")
       apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
       apply(subgoal_tac "setB (\<alpha>!na) \<subseteq> setB (foldl (@) [] \<alpha>)")
        apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
        apply(simp add: cfg_configurations_def)
        apply(force)
       apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
       apply(rule set_subset_to_setB_subset)
       apply(force)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
      apply(rule set_subset_to_setA_subset)
      apply(force)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
     apply(rule set_nth_foldl)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule_tac
      x="Suc n'"
      in exI)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(rule_tac
      x="if n'=0 then Some e2 else e'"
      in exI)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d')(*strict*)
   apply(rule hlp1)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule_tac
      t="(take na \<pi>s @ (e2 # map the (get_labels d' n')) # drop (Suc na) \<pi>s) ! na"
      and s="e2 # map the (get_labels d' n')"
      in ssubst)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(rule sym)
   apply(rule hlp1)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule listEqI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(clarsimp)
   apply(simp add: get_labels_def)
   apply (metis list.size(3) nat_seqEmpty nat_seq_length_Suc0 neq0_conv zero_less_Suc)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' i)(*strict*)
  apply(clarsimp)
  apply(case_tac i)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' i)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc n')=Suc 0#(nat_seq (Suc (Suc 0)) (Suc n'))")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
    apply(clarsimp)
    apply(simp add: get_label_def derivation_append_def der2_def)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
  apply(simp add: get_labels_def)
  apply(rule_tac
      t="nat_seq (Suc 0) n' ! nat"
      and s="Suc 0+nat"
      in ssubst)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
    apply(case_tac n')
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' nat)(*strict*)
     apply (metis less_zeroE list.size(3) nat_seqEmpty zero_less_Suc)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
   apply (metis Suc_le_mono Suc_pred gr_implies_not0 length_0_conv less_eq_Suc_le_raw nat_seqEmpty nat_seq_length_Suc0 not_less_eq)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc n') ! (Suc nat) = (Suc 0)+(Suc nat)")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
   apply(clarsimp)
   apply (metis gr_implies_not0 length_0_conv less_eq_Suc_le_raw nat_seqEmpty nat_seq_length_Suc0 not_less_eq)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="map (\<lambda>a. the (get_label (derivation_append (der2 \<lparr>cfg_conf = l2 @ teA (prod_lhs e2) # r2\<rparr> e2 \<lparr>cfg_conf = l2 @ prod_rhs e2 @ r2\<rparr>) d' (Suc 0) a))) (nat_seq (Suc 0) (Suc n')) ! Suc nat"
      and s=" (\<lambda>a. the (get_label (derivation_append (der2 \<lparr>cfg_conf = l2 @ teA (prod_lhs e2) # r2\<rparr> e2 \<lparr>cfg_conf = l2 @ prod_rhs e2 @ r2\<rparr>) d' (Suc 0) a))) ((nat_seq (Suc 0) (Suc n')) ! Suc nat)"
      in ssubst)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
   apply(rule nth_map)
   apply (metis Suc_less_eq length_0_conv nat_seqEmpty nat_seq_length_Suc0 neq0_conv zero_less_Suc)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e' nat)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def derivation_append_def der2_def)
  done

lemma equal_labels_implies_equal_cfgLMderivation: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d'
  \<Longrightarrow> cfgLM.derivation G d'a
  \<Longrightarrow> d' 0 = d'a 0
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> d' (n+m1) \<noteq> None
  \<Longrightarrow> d'a (n+m2) \<noteq> None
  \<Longrightarrow> map the (get_labels d' (n+m1)) @ c = map the (get_labels d'a (n + m2))
  \<Longrightarrow> d' i = d'a i"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d' i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+m1"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya)(*strict*)
     apply(force)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d'a i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+m2"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r la ra)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a l r la ra)(*strict*)
  apply(case_tac c1)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c2 e2a l r la ra)(*strict*)
  apply(case_tac c2)
  apply(rename_tac i y ya e1 e2 c2 e2a l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(subgoal_tac "e2=e2a")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
   apply(subgoal_tac "l=la")
    apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
    apply(clarsimp)
   apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (metis liftBDeConv2)
   apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac i y ya e1 e2a r la ra l')(*strict*)
   apply(thin_tac "setA (liftB l') = {}")
   apply(subgoal_tac "\<exists>la'. liftB la' = la")
    apply(rename_tac i y ya e1 e2a r la ra l')(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB la"
      in exI)
    apply (metis liftBDeConv2)
   apply(rename_tac i y ya e1 e2a r la ra l')(*strict*)
   apply(clarsimp)
   apply(rename_tac i y ya e1 e2a r ra l' la')(*strict*)
   apply(thin_tac "setA (liftB la') = {}")
   apply(rule terminalHeadEquals1)
     apply(rename_tac i y ya e1 e2a r ra l' la')(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac i y ya e1 e2a r ra l' la')(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac i y ya e1 e2a r ra l' la')(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(subgoal_tac "(map the (get_labels d' (n + m1)) @ c)!i = (map the (get_labels d'a (n + m2)))!i")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(thin_tac "map the (get_labels d' (n + m1)) @ c = map the (get_labels d'a (n + m2))")
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n + m1)) = (n+m1) + 1 - (Suc 0)")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n + m2)) = (n+m2) + 1 - (Suc 0)")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) (n + m1)) @ c) ! i = (map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) (n + m1))) ! i")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule nth_appendX)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) (n + m1) ! i = (Suc 0)+i")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (n + m2) ! i = (Suc 0)+i")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  done

lemma lemma_4_6_uniqueness_hlp2: "
  (\<And>y. y < x \<Longrightarrow> x1 ! y = x2 ! y \<and> y1 ! y = y2 ! y)
  \<Longrightarrow> valid_cfg G\<Longrightarrow> cfgLM.derivation G d\<Longrightarrow>
         cfgLM.belongs G d\<Longrightarrow>
         d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)\<Longrightarrow>
         d n = Some (pair e \<lparr>cfg_conf = liftB (foldl (@) [] y1)\<rparr>)\<Longrightarrow> x < length \<alpha>\<Longrightarrow>
         foldl (@) [] x1 = map the (get_labels d n)\<Longrightarrow>
         foldl (@) [] x2 = map the (get_labels d n)\<Longrightarrow> length x1 = length \<alpha>\<Longrightarrow>
         length x2 = length \<alpha>\<Longrightarrow> foldl (@) [] y2 = foldl (@) [] y1\<Longrightarrow>
         length y1 = length \<alpha>\<Longrightarrow>
         \<forall>i<length \<alpha>.
            \<exists>d'. cfgLM.derivation G d' \<and>
                 cfgLM.belongs G d' \<and>
                 d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
                 (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y1 ! i)\<rparr>)) \<and>
                       x1 ! i = map the (get_labels d' n'))\<Longrightarrow>
         length y2 = length \<alpha>\<Longrightarrow>
         \<forall>i<length \<alpha>.
            \<exists>d'. cfgLM.derivation G d' \<and>
                 cfgLM.belongs G d' \<and>
                 d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
                 (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y2 ! i)\<rparr>)) \<and>
                       x2 ! i = map the (get_labels d' n'))\<Longrightarrow>
         (x1 ! x) \<sqsubseteq> (x2 ! x)
        \<Longrightarrow> x1 ! x = x2 ! x \<and> y1 ! x = y2 ! x"
  apply(rule context_conjI)
   apply(erule_tac
      x="x"
      in allE)+
   apply(clarsimp)
   apply(rename_tac d' d'a n' n'a e' e'a)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac d' d'a n' n'a e' e'a c)(*strict*)
   apply(subgoal_tac "c=[]")
    apply(rename_tac d' d'a n' n'a e' e'a c)(*strict*)
    apply(force)
   apply(rename_tac d' d'a n' n'a e' e'a c)(*strict*)
   apply(case_tac n')
    apply(rename_tac d' d'a n' n'a e' e'a c)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' d'a n'a e'a c)(*strict*)
    apply(case_tac n'a)
     apply(rename_tac d' d'a n'a e'a c)(*strict*)
     apply(clarsimp)
     apply(rename_tac d' d'a c)(*strict*)
     apply(simp add: get_labels_def)
     apply(subgoal_tac "nat_seq (Suc 0) 0=[]")
      apply(rename_tac d' d'a c)(*strict*)
      apply(clarsimp)
     apply(rename_tac d' d'a c)(*strict*)
     apply (metis nat_seqEmpty zero_less_Suc)
    apply(rename_tac d' d'a n'a e'a c nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' d'a e'a c nat)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d'a 0 = Some (pair e1 c1) \<and> d'a (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
     apply(rename_tac d' d'a e'a c nat)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac d' d'a e'a c nat)(*strict*)
       apply(force)
      apply(rename_tac d' d'a e'a c nat)(*strict*)
      apply(force)
     apply(rename_tac d' d'a e'a c nat)(*strict*)
     apply(force)
    apply(rename_tac d' d'a e'a c nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' d'a e'a c nat e2 c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d' d'a e'a c nat e2 c2 l r)(*strict*)
    apply (metis setA_liftB all_not_in_conv elemInsetA)
   apply(rename_tac d' d'a n' n'a e' e'a c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' d'a n'a e' e'a c nat)(*strict*)
   apply(case_tac n'a)
    apply(rename_tac d' d'a n'a e' e'a c nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' d'a e' c nat)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d' 0 = Some (pair e1 c1) \<and> d' (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
     apply(rename_tac d' d'a e' c nat)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac d' d'a e' c nat)(*strict*)
       apply(force)
      apply(rename_tac d' d'a e' c nat)(*strict*)
      apply(force)
     apply(rename_tac d' d'a e' c nat)(*strict*)
     apply(force)
    apply(rename_tac d' d'a e' c nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' d'a e' c nat e2 c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d' d'a e' c nat e2 c2 l r)(*strict*)
    apply (metis setA_liftB all_not_in_conv elemInsetA)
   apply(rename_tac d' d'a n'a e' e'a c nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' d'a e' e'a c nat nata)(*strict*)
   apply(rename_tac n' n'a)
   apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
   apply(subgoal_tac "n'+length c=n'a")
    apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
    prefer 2
    apply(simp add: get_labels_def)
    apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n')) = (Suc n') + 1 - (Suc 0)")
     apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n'a)) = (Suc n'a) + 1 - (Suc 0)")
     apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
    apply(subgoal_tac "Suc n'+length c=Suc n'a")
     apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
     apply(force)
    apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
    apply(rule_tac
      t="Suc n'"
      and s="length(map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) (Suc n')))"
      in ssubst)
     apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
     apply(force)
    apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
    apply(rule_tac
      t="Suc n'a"
      and s="length(map (the \<circ> (\<lambda>i. get_label (d'a i))) (nat_seq (Suc 0) (Suc n'a)))"
      in ssubst)
     apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
     apply(force)
    apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
    apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) (Suc n'))) + length c"
      and s="length(map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) (Suc n')) @ c)"
      in ssubst)
     apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
     apply (metis One_nat_def length_append)
    apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
    apply(force)
   apply(rename_tac d' d'a e' e'a c n' n'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' d'a e' e'a c n')(*strict*)
   apply(subgoal_tac "\<forall>i\<le>Suc n'. d' i = d'a i")
    apply(rename_tac d' d'a e' e'a c n')(*strict*)
    apply(erule_tac
      x="Suc n'"
      in allE)
    apply(clarsimp)
    apply(case_tac c)
     apply(rename_tac d' d'a e' e'a c n')(*strict*)
     apply(clarsimp)
    apply(rename_tac d' d'a e' e'a c n' a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' d'a e' e'a n' a list)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d'a (Suc n') = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
     apply(rename_tac d' d'a e' e'a n' a list)(*strict*)
     prefer 2
     apply(rule_tac
      m="(Suc (Suc (n' + length list)))"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac d' d'a e' e'a n' a list)(*strict*)
       apply(force)
      apply(rename_tac d' d'a e' e'a n' a list)(*strict*)
      apply(force)
     apply(rename_tac d' d'a e' e'a n' a list)(*strict*)
     apply(force)
    apply(rename_tac d' d'a e' e'a n' a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' d'a e' e'a n' a list e2 c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d' d'a e' e'a n' a list e2 c2 l r)(*strict*)
    apply (metis setA_liftB all_not_in_conv elemInsetA)
   apply(rename_tac d' d'a e' e'a c n')(*strict*)
   apply(rule allI)
   apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
   apply(rule impI)
   apply(rule_tac ?m1.0="0" and ?m2.0="length c" in equal_labels_implies_equal_cfgLMderivation )
          apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
          apply(force)
         apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
         apply(force)
        apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
        apply(force)
       apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
       apply(force)
      apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
      apply(force)
     apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
     apply(force)
    apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
    apply(force)
   apply(rename_tac d' d'a e' e'a c n' i)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(thin_tac "(x2 ! x) \<sqsubseteq> (x2 ! x)")
  apply(erule_tac
      x="x"
      in allE)+
  apply(clarsimp)
  apply(rename_tac d' d'a n' n'a e' e'a)(*strict*)
  apply(subgoal_tac "n'=n'a")
   apply(rename_tac d' d'a n' n'a e' e'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' d'a n'a e' e'a)(*strict*)
   apply(case_tac n'a)
    apply(rename_tac d' d'a n'a e' e'a)(*strict*)
    apply(clarsimp)
    apply(rename_tac d' d'a)(*strict*)
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac d' d'a n'a e' e'a nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d' d'a e' e'a nat)(*strict*)
   apply(subgoal_tac "\<forall>i\<le>Suc nat. d' i = d'a i")
    apply(rename_tac d' d'a e' e'a nat)(*strict*)
    apply(erule_tac
      x="Suc nat"
      in allE)
    apply(clarsimp)
    apply(rename_tac d' d'a e' nat)(*strict*)
    apply(rule liftB_inj)
    apply(rule sym)
    apply(force)
   apply(rename_tac d' d'a e' e'a nat)(*strict*)
   apply(rule allI)
   apply(rename_tac d' d'a e' e'a nat i)(*strict*)
   apply(rule impI)
   apply(rule_tac ?m1.0="0" and ?m2.0="0" in equal_labels_implies_equal_cfgLMderivation )
          apply(rename_tac d' d'a e' e'a nat i)(*strict*)
          apply(force)
         apply(rename_tac d' d'a e' e'a nat i)(*strict*)
         apply(force)
        apply(rename_tac d' d'a e' e'a nat i)(*strict*)
        apply(force)
       apply(rename_tac d' d'a e' e'a nat i)(*strict*)
       apply(force)
      apply(rename_tac d' d'a e' e'a nat i)(*strict*)
      apply(force)
     apply(rename_tac d' d'a e' e'a nat i)(*strict*)
     apply(force)
    apply(rename_tac d' d'a e' e'a nat i)(*strict*)
    apply(force)
   apply(rename_tac d' d'a e' e'a nat i)(*strict*)
   apply(force)
  apply(rename_tac d' d'a n' n'a e' e'a)(*strict*)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) n'a) = (n'a) + 1 - (Suc 0)")
   apply(rename_tac d' d'a n' n'a e' e'a)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac d' d'a n' n'a e' e'a)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n') = (n') + 1 - (Suc 0)")
   apply(rename_tac d' d'a n' n'a e' e'a)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac d' d'a n' n'a e' e'a)(*strict*)
  apply(clarsimp)
  apply (metis length_map)
  done

lemma lemma_4_6_uniqueness_hlp1: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> foldl (@) [] x1 = \<pi> \<and>
        length x1 = length \<alpha> \<and>
        foldl (@) [] y1 = w \<and>
        length y1 = length \<alpha> \<and>
        (\<forall>i<length x1.
            \<exists>d' n' e'.
               cfgLM.derivation G d' \<and>
               cfgLM.belongs G d' \<and>
               d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
               d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y1 ! i)\<rparr>) \<and>
               x1 ! i = map the (get_labels d' n'))
  \<Longrightarrow>
        foldl (@) [] x2 = \<pi> \<and>
        length x2 = length \<alpha> \<and>
        foldl (@) [] y2 = w \<and>
        length y2 = length \<alpha> \<and>
        (\<forall>i<length x2.
            \<exists>d' n' e'.
               cfgLM.derivation G d' \<and>
               cfgLM.belongs G d' \<and>
               d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
               d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y2 ! i)\<rparr>) \<and>
               x2 ! i = map the (get_labels d' n'))
  \<Longrightarrow> i < length \<alpha>
  \<Longrightarrow> x1 ! i = x2 ! i \<and> y1 ! i = y2 ! i"
  apply(induct i rule: less_induct)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "prefix (x1!x) (x2!x) \<or> prefix (x2!x) (x1!x)")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule_tac
      b="foldl (@) [] (drop (Suc x) x1)"
      and d="foldl (@) [] (drop (Suc x) x2)"
      in mutual_prefix_prefix)
   apply(rule_tac
      w="foldl (@) [] (take x x1)"
      in append_linj)
   apply(rule_tac
      t="foldl (@) [] (take x x1) @ x2 ! x @ foldl (@) [] (drop (Suc x) x2)"
      and s="foldl (@) [] (take x x2) @ x2 ! x @ foldl (@) [] (drop (Suc x) x2)"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(simp (no_asm))
    apply(rule foldl_equal)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x y)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="foldl (@) [] (take x x1) @ x1 ! x @ foldl (@) [] (drop (Suc x) x1)"
      and s="foldl (@) [] x1"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(rule foldl_decomp)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="foldl (@) [] (take x x2) @ x2 ! x @ foldl (@) [] (drop (Suc x) x2)"
      and s="foldl (@) [] x2"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(rule foldl_decomp)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(rule lemma_4_6_uniqueness_hlp2)
                   apply(rename_tac x y)(*strict*)
                   apply(force)
                  apply(rename_tac x)(*strict*)
                  apply(force)
                 apply(rename_tac x)(*strict*)
                 apply(force)
                apply(rename_tac x)(*strict*)
                apply(force)
               apply(rename_tac x)(*strict*)
               apply(force)
              apply(rename_tac x)(*strict*)
              apply(force)
             apply(rename_tac x)(*strict*)
             apply(force)
            apply(rename_tac x)(*strict*)
            apply(force)
           apply(rename_tac x)(*strict*)
           apply(force)
          apply(rename_tac x)(*strict*)
          apply(force)
         apply(rename_tac x)(*strict*)
         apply(force)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "x2 ! x = x1 ! x \<and> y2 ! x = y1 ! x")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule lemma_4_6_uniqueness_hlp2)
                  apply(rename_tac x y)(*strict*)
                  apply(force)
                 apply(rename_tac x)(*strict*)
                 apply(force)
                apply(rename_tac x)(*strict*)
                apply(force)
               apply(rename_tac x)(*strict*)
               apply(force)
              apply(rename_tac x)(*strict*)
              apply(force)
             apply(rename_tac x)(*strict*)
             apply(force)
            apply(rename_tac x)(*strict*)
            apply(force)
           apply(rename_tac x)(*strict*)
           apply(force)
          apply(rename_tac x)(*strict*)
          apply(force)
         apply(rename_tac x)(*strict*)
         apply(force)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma lemma_4_6_uniqueness: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> foldl (@) [] x1 = \<pi> \<and>
        length x1 = length \<alpha> \<and>
        foldl (@) [] y1 = w \<and>
        length y1 = length \<alpha> \<and>
        (\<forall>i<length x1.
            \<exists>d' n' e'.
               cfgLM.derivation G d' \<and>
               cfgLM.belongs G d' \<and>
               d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
               d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y1 ! i)\<rparr>) \<and>
               x1 ! i = map the (get_labels d' n'))
  \<Longrightarrow>
        foldl (@) [] x2 = \<pi> \<and>
        length x2 = length \<alpha> \<and>
        foldl (@) [] y2 = w \<and>
        length y2 = length \<alpha> \<and>
        (\<forall>i<length x2.
            \<exists>d' n' e'.
               cfgLM.derivation G d' \<and>
               cfgLM.belongs G d' \<and>
               d' 0 = Some (pair None \<lparr>cfg_conf = \<alpha> ! i\<rparr>) \<and>
               d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y2 ! i)\<rparr>) \<and>
               x2 ! i = map the (get_labels d' n'))
  \<Longrightarrow> x1 = x2 \<and> y1 = y2"
  apply(clarsimp)
  apply(subgoal_tac "\<forall>i<(length \<alpha>). x1!i = x2!i \<and> y1!i=y2!i")
   apply(rule conjI)
    apply(rule listEqI)
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
  apply(rule lemma_4_6_uniqueness_hlp1)
          apply(rename_tac i)(*strict*)
          apply(force)+
  done

lemma lemma_4_6: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> \<exists>!\<pi>s. \<exists>!ws.
  foldl (@) [] \<pi>s = \<pi>
  \<and> length \<pi>s = length \<alpha>
  \<and> foldl (@) [] ws = w
  \<and> length ws = length \<alpha>
  \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'.
  cfgLM.derivation G d'
  \<and> cfgLM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=\<alpha>!i\<rparr>)
  \<and> d' n' = Some (pair e' \<lparr>cfg_conf=liftB (ws!i)\<rparr>)
  \<and> \<pi>s!i = map the (get_labels d' n'))"
  apply(rule ex_ex1I_double)
   apply(rule lemma_4_6_existence)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac x1 y1 x2 y2)(*strict*)
  apply(rule lemma_4_6_uniqueness)
         apply(rename_tac x1 y1 x2 y2)(*strict*)
         apply(force)+
  done

lemma lemma_4_8_hlp: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = Xseq\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> \<exists>!\<pi>s. \<exists>!ws.
  foldl (@) [] \<pi>s = \<pi>
  \<and> length \<pi>s = length Xseq
  \<and> foldl (@) [] ws = w
  \<and> length ws = length Xseq
  \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'.
  cfgLM.derivation G d'
  \<and> cfgLM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=[Xseq!i]\<rparr>)
  \<and> d' n' = Some (pair e' \<lparr>cfg_conf=liftB (ws!i)\<rparr>)
  \<and> \<pi>s!i = map the (get_labels d' n'))"
  apply(subgoal_tac "\<exists>!\<pi>s. \<exists>!ws. foldl (@) [] \<pi>s = \<pi> \<and> length \<pi>s = length (map (\<lambda>x. [x]) Xseq) \<and> foldl (@) [] ws = w \<and> length ws = length (map (\<lambda>x. [x]) Xseq) \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=(map (\<lambda>x. [x]) Xseq)!i\<rparr>) \<and> d' n' = Some (pair e' \<lparr>cfg_conf=liftB (ws!i)\<rparr>) \<and> \<pi>s!i = map the (get_labels d' n'))")
   prefer 2
   apply(rule lemma_4_6)
        apply(force)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply (metis split_string_into_single_item_strings)
    apply(force)
   apply(force)
  apply(rule_tac
      P="\<lambda>\<pi>s ws. foldl (@) [] \<pi>s = \<pi> \<and> length \<pi>s = length (map (\<lambda>x. [x]) Xseq) \<and> foldl (@) [] ws = w \<and> length ws = length (map (\<lambda>x. [x]) Xseq) \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = map (\<lambda>x. [x]) Xseq ! i\<rparr>) \<and> d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>s ! i = map the (get_labels d' n'))"
      in ex1_eq)
   apply(force)
  apply(thin_tac "\<exists>!\<pi>s. \<exists>!ws. foldl (@) [] \<pi>s = \<pi> \<and> length \<pi>s = length (map (\<lambda>x. [x]) Xseq) \<and> foldl (@) [] ws = w \<and> length ws = length (map (\<lambda>x. [x]) Xseq) \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = map (\<lambda>x. [x]) Xseq ! i\<rparr>) \<and> d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>s ! i = map the (get_labels d' n'))")
  apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac x y)(*strict*)
   apply(clarsimp)
  apply(rename_tac x y)(*strict*)
  apply(clarsimp)
  done

lemma lemma_4_8: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>)
  \<Longrightarrow> d (Suc 0) = Some (pair (Some r) \<lparr>cfg_conf = Xseq\<rparr>)
  \<Longrightarrow> d (Suc n) = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> r#\<pi>=map the (get_labels d (Suc n))
  \<Longrightarrow> \<exists>!\<pi>s. \<exists>!ws.
  foldl (@) [] \<pi>s = \<pi>
  \<and> length \<pi>s = length Xseq
  \<and> foldl (@) [] ws = w
  \<and> length ws = length Xseq
  \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'.
  cfgLM.derivation G d'
  \<and> cfgLM.belongs G d'
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=[Xseq!i]\<rparr>)
  \<and> d' n' = Some (pair e' \<lparr>cfg_conf=liftB (ws!i)\<rparr>)
  \<and> \<pi>s!i = map the (get_labels d' n'))"
  apply(rule_tac
      e="if n=0 then None else e"
      and n="n"
      and d="derivation_drop d (Suc 0)"
      in lemma_4_8_hlp)
       apply(force)
      apply(rule cfgLM.derivation_drop_preserves_derivation_prime)
       apply(force)
      apply(force)
     apply(rule cfgLM.derivation_drop_preserves_belongs)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: derivation_drop_def)
   apply(simp add: derivation_drop_def)
   apply(force)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = Suc 0 # (nat_seq (Suc (Suc 0)) (Suc n))")
   apply(clarsimp)
   apply(rule listEqI)
    apply(clarsimp)
    apply (metis length_Cons lessI nat_seqEmpty nat_seq_length_Suc0 not_gr_zero old.nat.inject zero_less_Suc)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc n)) = (Suc n) + 1 - (Suc (Suc 0))")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (derivation_drop d (Suc 0) i))) (nat_seq (Suc 0) n) ! i"
      and s=" (the \<circ> (\<lambda>i. get_label (derivation_drop d (Suc 0) i))) ((nat_seq (Suc 0) n) ! i)"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_map)
    apply (metis Suc_less_SucD gr_implies_not0 list.size(3) nat_seqEmpty nat_seq_length_Suc0 not_less_eq)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="nat_seq (Suc 0) n ! i"
      and s="Suc 0 + i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc n) ! i"
      and s="(Suc (Suc 0))+i"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_drop_def)
  apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
  done

lemma CFGlm2rm_terminates: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=[A]\<rparr>)
  \<Longrightarrow> d (Suc 0) = Some (pair e \<lparr>cfg_conf=Xseq\<rparr>)
  \<Longrightarrow> d (Suc n) = Some (pair e' \<lparr>cfg_conf=liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d (Suc n))
  \<Longrightarrow> CFGlm2rm_dom (G,\<pi>)"
  apply(induct n arbitrary: d A e e' c \<pi> Xseq w e' rule: less_induct)
  apply(rename_tac x d A e e' \<pi> Xseq w)(*strict*)
  apply(case_tac x)
   apply(rename_tac x d A e e' \<pi> Xseq w)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A e' w)(*strict*)
   apply(thin_tac "\<And>y d A e e' \<pi> Xseq w. False \<Longrightarrow> cfgLM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> d (Suc 0) = Some (pair e \<lparr>cfg_conf = Xseq\<rparr>) \<Longrightarrow> d (Suc y) = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> \<pi> = map the (get_labels d (Suc y)) \<Longrightarrow> CFGlm2rm_dom (G, map the (get_labels d (Suc y)))")
   apply(rename_tac d A e' w)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc 0)=[Suc 0]")
    apply(rename_tac d A e' w)(*strict*)
    apply(clarsimp)
    apply(rule CFGlm2rm.domintros)
    apply(rename_tac d A e' w xa)(*strict*)
    apply(subgoal_tac "xa \<in> set(map (\<lambda>x. []) w)")
     apply(rename_tac d A e' w xa)(*strict*)
     prefer 2
     apply(rule_tac
      t="map (\<lambda>x. []) w"
      and s="SOME \<pi>s. foldl (@) [] \<pi>s = [] \<and> length \<pi>s = length (prod_rhs (the (get_label (Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>))))) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs (the (get_label (Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>)))) ! i)))"
      in ssubst)
      apply(rename_tac d A e' w xa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac d A e' w xa)(*strict*)
     prefer 2
     apply(rename_tac d A e' w xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac d A e' w x)(*strict*)
     apply(rule CFGlm2rm.domintros)
    apply(rename_tac d A e' w xa)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
     apply(rename_tac d A e' w xa)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc 0"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac d A e' w xa)(*strict*)
       apply(force)
      apply(rename_tac d A e' w xa)(*strict*)
      apply(force)
     apply(rename_tac d A e' w xa)(*strict*)
     apply(force)
    apply(rename_tac d A e' w xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d A w xa e2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac d A w xa e2 l r)(*strict*)
    apply(case_tac l)
     apply(rename_tac d A w xa e2 l r)(*strict*)
     prefer 2
     apply(rename_tac d A w xa e2 l r a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac d A w xa e2 l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w xa e2)(*strict*)
    apply(rule_tac
      a="map (\<lambda>x. []) w"
      in someI2)
     apply(rename_tac d w xa e2)(*strict*)
     apply(clarsimp)
     apply(rule context_conjI)
      apply(rename_tac d w xa e2)(*strict*)
      apply(rule foldl_empty)
      apply(rename_tac d w xa e2 a)(*strict*)
      apply(clarsimp)
     apply(rename_tac d w xa e2)(*strict*)
     apply(rule context_conjI)
      apply(rename_tac d w xa e2)(*strict*)
      apply(simp add: get_label_def)
      apply (metis liftB_reflects_length)
     apply(rename_tac d w xa e2)(*strict*)
     apply(clarsimp)
     apply(rename_tac d w xa e2 i)(*strict*)
     apply(simp add: get_label_def)
     apply(simp add: CFGlmEliminators_def)
     apply(rule_tac
      x="der1 \<lparr>cfg_conf=[prod_rhs e2 ! i]\<rparr>"
      in exI)
     apply(rule conjI)
      apply(rename_tac d w xa e2 i)(*strict*)
      apply(rule cfgLM.der1_is_derivation)
     apply(rename_tac d w xa e2 i)(*strict*)
     apply(rule conjI)
      apply(rename_tac d w xa e2 i)(*strict*)
      apply(rule cfgLM.der1_belongs)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="e2"
      in ballE)
       apply(rename_tac d w xa e2 i)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac d w xa e2 i)(*strict*)
      apply(clarsimp)
      apply(simp add: cfg_configurations_def)
      apply(case_tac "prod_rhs e2!i")
       apply(rename_tac d w xa e2 i a)(*strict*)
       apply(clarsimp)
       apply (metis setA_liftB setA_set_not liftB_reflects_length emptyE nth_mem)
      apply(rename_tac d w xa e2 i b)(*strict*)
      apply(clarsimp)
      apply (metis setB_set_not liftB_reflects_length nth_mem set_setB_liftB subsetE)
     apply(rename_tac d w xa e2 i)(*strict*)
     apply(rule conjI)
      apply(rename_tac d w xa e2 i)(*strict*)
      apply(simp add: der1_def)
      apply(simp add: option_to_list_def)
     apply(rename_tac d w xa e2 i)(*strict*)
     apply(rule_tac
      x="0"
      in exI)
     apply(rule conjI)
      apply(rename_tac d w xa e2 i)(*strict*)
      apply(rule_tac
      x="None"
      in exI)
      apply(rule_tac
      x="[w!i]"
      in exI)
      apply(simp add: der1_def)
      apply(rule_tac
      t="teB (w!i)"
      and s="(liftB w)!i"
      in ssubst)
       apply(rename_tac d w xa e2 i)(*strict*)
       apply(rule teB_nth_liftB)
       apply(force)
      apply(rename_tac d w xa e2 i)(*strict*)
      apply(force)
     apply(rename_tac d w xa e2 i)(*strict*)
     apply(simp add: get_labels_def)
     apply (metis nat_seqEmpty zero_less_Suc)
    apply(rename_tac d w xa e2 x)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w xa e2 x)(*strict*)
    apply(rule listEqI)
     apply(rename_tac d w xa e2 x)(*strict*)
     apply(clarsimp)
     apply(simp add: get_label_def)
     apply (metis liftB_reflects_length)
    apply(rename_tac d w xa e2 x i)(*strict*)
    apply(clarsimp)
    apply(simp add: get_label_def)
    apply(rule_tac
      t="map (\<lambda>x. []) w ! i"
      and s="(\<lambda>x. []) (w ! i)"
      in ssubst)
     apply(rename_tac d w xa e2 x i)(*strict*)
     apply(rule nth_map)
     apply (metis liftB_reflects_length)
    apply(rename_tac d w xa e2 x i)(*strict*)
    apply(rule sym)
    apply(rule foldl_empty2)
     apply(rename_tac d w xa e2 x i)(*strict*)
     apply(force)
    apply(rename_tac d w xa e2 x i)(*strict*)
    apply (metis liftB_reflects_length)
   apply(rename_tac d A e' w)(*strict*)
   apply (metis natUptTo_n_n)
  apply(rename_tac x d A e e' \<pi> Xseq w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d A e e' Xseq w nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac d A e e' Xseq w n)(*strict*)
  apply(case_tac "map the (get_labels d (Suc (Suc n)))")
   apply(rename_tac d A e e' Xseq w n)(*strict*)
   apply(clarsimp)
   apply(rule CFGlm2rm.domintros)
  apply(rename_tac d A e e' Xseq w n a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d A e e' Xseq w n z zs)(*strict*)
  apply(rule CFGlm2rm.domintros)
  apply(rename_tac d A e e' Xseq w n z zs xa)(*strict*)
  apply(subgoal_tac "map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc (Suc n))) = z # zs")
   apply(rename_tac d A e e' Xseq w n z zs xa)(*strict*)
   prefer 2
   apply(simp add: get_labels_def)
  apply(rename_tac d A e e' Xseq w n z zs xa)(*strict*)
  apply(thin_tac "get_labels d (Suc (Suc n)) = z # zs")
  apply(subgoal_tac "nat_seq (Suc 0) (Suc (Suc n)) = Suc 0 # nat_seq (Suc (Suc 0)) (Suc (Suc n))")
   apply(rename_tac d A e e' Xseq w n z zs xa)(*strict*)
   prefer 2
   apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
  apply(rename_tac d A e e' Xseq w n z zs xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d A e e' Xseq w n xa)(*strict*)
  apply(thin_tac "nat_seq (Suc 0) (Suc (Suc n)) = Suc 0 # nat_seq (Suc (Suc 0)) (Suc (Suc n))")
  apply(subgoal_tac "\<exists>\<pi>s. \<pi>s=(SOME \<pi>s. foldl (@) [] \<pi>s = map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>))))) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>)))) ! i)))) \<and> (foldl (@) [] \<pi>s = map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>))))) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>)))) ! i))))")
   apply(rename_tac d A e e' Xseq w n xa)(*strict*)
   apply(erule exE)
   apply(rename_tac d A e e' Xseq w n xa \<pi>s)(*strict*)
   apply(erule conjE)+
   apply(subgoal_tac "xa \<in> set \<pi>s")
    apply(rename_tac d A e e' Xseq w n xa \<pi>s)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d A e e' Xseq w n xa \<pi>s)(*strict*)
   apply(thin_tac "xa \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>))))) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>)))) ! i))))")
   apply(rename_tac d A e e' Xseq w n xa \<pi>s)(*strict*)
   apply(thin_tac "\<pi>s = (SOME \<pi>s. foldl (@) [] \<pi>s = map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>))))) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>)))) ! i))))")
   apply(rename_tac d A e e' Xseq w n xa \<pi>s)(*strict*)
   apply(subgoal_tac "\<exists>j<length \<pi>s. \<pi>s!j=xa")
    apply(rename_tac d A e e' Xseq w n xa \<pi>s)(*strict*)
    prefer 2
    apply (metis in_set_conv_nth)
   apply(rename_tac d A e e' Xseq w n xa \<pi>s)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A e e' Xseq w n \<pi>s j)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
    apply(rename_tac d A e e' Xseq w n \<pi>s j)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc 0"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d A e e' Xseq w n \<pi>s j)(*strict*)
      apply(force)
     apply(rename_tac d A e e' Xseq w n \<pi>s j)(*strict*)
     apply(force)
    apply(rename_tac d A e e' Xseq w n \<pi>s j)(*strict*)
    apply(force)
   apply(rename_tac d A e e' Xseq w n \<pi>s j)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A e' Xseq w n \<pi>s j e2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d A e' w n \<pi>s j e2 l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac d A e' w n \<pi>s j e2 l r)(*strict*)
    prefer 2
    apply(rename_tac d A e' w n \<pi>s j e2 l r a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d A e' w n \<pi>s j e2 l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e' w n \<pi>s j e2)(*strict*)
   apply(simp add: get_label_def)
   apply(case_tac "\<pi>s!j")
    apply(rename_tac d e' w n \<pi>s j e2)(*strict*)
    apply(clarsimp)
    apply(rule CFGlm2rm.domintros)
   apply(rename_tac d e' w n \<pi>s j e2 a list)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="j"
      in allE)
   apply(clarsimp)
   apply(simp add: CFGlmEliminators_def)
   apply(clarsimp)
   apply(rename_tac d e' w n \<pi>s j e2 da na e z wa zs)(*strict*)
   apply(subgoal_tac "map (\<lambda>i. get_label (da i)) (nat_seq (Suc 0) na) = z # zs")
    apply(rename_tac d e' w n \<pi>s j e2 da na e z wa zs)(*strict*)
    prefer 2
    apply(simp add: get_labels_def)
   apply(rename_tac d e' w n \<pi>s j e2 da na e z wa zs)(*strict*)
   apply(thin_tac "get_labels da na = z # zs")
   apply(case_tac na)
    apply(rename_tac d e' w n \<pi>s j e2 da na e z wa zs)(*strict*)
    apply(clarsimp)
    apply(rename_tac d e' w n \<pi>s j e2 da wa za zsa)(*strict*)
    apply(subgoal_tac "nat_seq (Suc 0) 0=[]")
     apply(rename_tac d e' w n \<pi>s j e2 da wa za zsa)(*strict*)
     apply(force)
    apply(rename_tac d e' w n \<pi>s j e2 da wa za zsa)(*strict*)
    apply (metis list.simps(2) nat_seqEmpty zero_less_Suc)
   apply(rename_tac d e' w n \<pi>s j e2 da na e z wa zs nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e' w n \<pi>s j e2 da e wa nat za zsa)(*strict*)
   apply(rename_tac n za zsa)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n za zsa)(*strict*)
   apply(erule_tac
      x="n"
      in meta_allE)
   apply(erule_tac
      x="da"
      in meta_allE)
   apply(erule_tac
      x="prod_rhs e2 ! j"
      in meta_allE)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = Suc 0 # (nat_seq (Suc (Suc 0)) (Suc n))")
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n za zsa)(*strict*)
    prefer 2
    apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n za zsa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n)(*strict*)
   apply(thin_tac "nat_seq (Suc 0) (Suc n) = Suc 0 # nat_seq (Suc (Suc 0)) (Suc n)")
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. da 0 = Some (pair e1 c1) \<and> da (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d e' w na \<pi>s j e2 da e wa n)(*strict*)
      apply(force)
     apply(rename_tac d e' w na \<pi>s j e2 da e wa n)(*strict*)
     apply(force)
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n)(*strict*)
    apply(force)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a c2 l r)(*strict*)
   apply(simp add: option_to_list_def)
   apply(case_tac l)
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a c2 l r)(*strict*)
    prefer 2
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a c2 l r a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a c2 l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a c2)(*strict*)
   apply(case_tac c2)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a c2 cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
   apply(erule_tac
      x="Some e2a"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="map the (get_labels da (Suc n))"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="prod_rhs e2a"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="wa"
      in meta_allE)
   apply(clarsimp)
   apply(erule meta_impE)
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
    apply(subgoal_tac "the (get_label (Some (pair (Some e2a) \<lparr>cfg_conf = prod_rhs e2a\<rparr>)))=e2a")
     apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
     prefer 2
     apply(simp add: get_label_def)
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
    apply(clarsimp)
    apply(thin_tac "the (get_label (Some (pair (Some e2a) \<lparr>cfg_conf = prod_rhs e2a\<rparr>))) = e2a")
    apply(subgoal_tac "foldl ((+)) 0 (map length \<pi>s) = length (foldl (@) [] \<pi>s)")
     apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
     apply(subgoal_tac "length (\<pi>s!j) \<le> length (foldl (@) [] \<pi>s)")
      apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
      apply(subgoal_tac "length (\<pi>s!j) = Suc n")
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       prefer 2
       apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc n)) = (Suc n) + 1 - (Suc (Suc 0))")
        apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
        prefer 2
        apply(rule nat_seq_length_prime)
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       apply(rule_tac
      t="\<pi>s!j"
      and s="e2a # map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc (Suc 0)) (Suc n))"
      in ssubst)
        apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
        apply(force)
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       apply (metis One_nat_def Suc_eq_plus1 diff_Suc_1 diff_Suc_Suc length_map list.size(4) nat_seq_length_prime)
      apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
      apply(subgoal_tac "Suc n < Suc(Suc na)")
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       apply(force)
      apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
      apply(rule_tac
      t="Suc n"
      and s="length (\<pi>s ! j)"
      in ssubst)
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       apply(force)
      apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
      apply(rule_tac
      t="Suc na"
      and s="length(foldl (@) [] \<pi>s)"
      in ssubst)
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       apply(rule_tac
      t="foldl (@) [] \<pi>s"
      and s="map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i))) (nat_seq (Suc (Suc 0)) (Suc (Suc na)))"
      in ssubst)
        apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
        apply(force)
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       apply(rule sym)
       apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. case_option None (case_derivation_configuration (\<lambda>e c. e)) (d i))) (nat_seq (Suc (Suc 0)) (Suc (Suc na))))"
      and s="length (nat_seq (Suc (Suc 0)) (Suc (Suc na)))"
      in ssubst)
        apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
        apply(force)
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc (Suc na))) = (Suc (Suc na)) + 1 - (Suc (Suc 0))")
        apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
        prefer 2
        apply(rule nat_seq_length_prime)
       apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
       apply(force)
      apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
      apply(force)
     apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
     apply(rule length_shorter_than_in_composition)
     apply(force)
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
    apply(rule distrib_add_apppend_with_map)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
   apply(simp add: get_labels_def)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = Suc 0 # (nat_seq (Suc (Suc 0)) (Suc n))")
    apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
    prefer 2
    apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
   apply(rename_tac d e' w na \<pi>s j e2 da e wa n e2a)(*strict*)
   apply(clarsimp)
  apply(rename_tac d A e e' Xseq w n xa)(*strict*)
  apply(rule someI_existence)
  apply(thin_tac "\<And>y d A e e' \<pi> Xseq w. y < Suc n \<Longrightarrow> cfgLM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [A]\<rparr>) \<Longrightarrow> d (Suc 0) = Some (pair e \<lparr>cfg_conf = Xseq\<rparr>) \<Longrightarrow> d (Suc y) = Some (pair e' \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> \<pi> = map the (get_labels d (Suc y)) \<Longrightarrow> CFGlm2rm_dom (G, map the (get_labels d (Suc y)))")
  apply(rename_tac d A e e' Xseq w n xa)(*strict*)
  apply(thin_tac "xa \<in> set (SOME \<pi>s. foldl (@) [] \<pi>s = map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))) \<and> length \<pi>s = length (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>))))) \<and> (\<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (prod_rhs (the (get_label (Some (pair e \<lparr>cfg_conf = Xseq\<rparr>)))) ! i))))")
  apply(rename_tac d A e e' Xseq w n xa)(*strict*)
  apply(subgoal_tac "\<exists>r. e=Some r")
   apply(rename_tac d A e e' Xseq w n xa)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
    apply(rename_tac d A e e' Xseq w n xa)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc (Suc n)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d A e e' Xseq w n xa)(*strict*)
      apply(force)
     apply(rename_tac d A e e' Xseq w n xa)(*strict*)
     apply(force)
    apply(rename_tac d A e e' Xseq w n xa)(*strict*)
    apply(force)
   apply(rename_tac d A e e' Xseq w n xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac d A e e' Xseq w n xa)(*strict*)
  apply(erule exE)
  apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
  apply(subgoal_tac "r # tl (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc (Suc n)))) = map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc (Suc n)))")
   apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
   prefer 2
   apply(rule listEqI)
    apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
    apply(clarsimp)
    apply(rename_tac d A e' Xseq w n r)(*strict*)
    apply (metis diff_Suc_Suc less_Suc_eq_0_disj minus_nat.diff_0 nat_seq_length_Suc0)
   apply(rename_tac d A e e' Xseq w n xa r i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A e' Xseq w n r i)(*strict*)
   apply(case_tac i)
    apply(rename_tac d A e' Xseq w n r i)(*strict*)
    apply(clarsimp)
    apply(rename_tac d A e' Xseq w n r)(*strict*)
    apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc (Suc n))) ! 0"
      and s=" (the \<circ> (\<lambda>i. get_label (d i))) ((nat_seq (Suc 0) (Suc (Suc n))) ! 0)"
      in ssubst)
     apply(rename_tac d A e' Xseq w n r)(*strict*)
     apply(rule nth_map)
     apply (metis Zero_not_Suc nat_seq_length_Suc0 neq0_conv)
    apply(rename_tac d A e' Xseq w n r)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq (Suc 0) (Suc (Suc n)) ! 0"
      and s="(Suc 0) + 0"
      in ssubst)
     apply(rename_tac d A e' Xseq w n r)(*strict*)
     apply (simp add: nat_seq_nth_compute)
    apply(rename_tac d A e' Xseq w n r)(*strict*)
    apply(simp add: get_label_def)
   apply(rename_tac d A e' Xseq w n r i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A e' Xseq w n r nat)(*strict*)
   apply(rule_tac
      t="tl (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc (Suc n)))) ! nat"
      and s=" (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc (Suc n)))) ! (Suc nat)"
      in ssubst)
    apply(rename_tac d A e' Xseq w n r nat)(*strict*)
    apply(rule tl_nth_shift)
    apply(force)
   apply(rename_tac d A e' Xseq w n r nat)(*strict*)
   apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) (Suc (Suc n))) ! Suc nat"
      and s=" (the \<circ> (\<lambda>i. get_label (d i))) ((nat_seq (Suc 0) (Suc (Suc n))) ! Suc nat)"
      in ssubst)
    apply(rename_tac d A e' Xseq w n r nat)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac d A e' Xseq w n r nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
  apply(subgoal_tac "\<exists>!\<pi>s. \<exists>!ws. foldl (@) [] \<pi>s = SSrenPI \<and> length \<pi>s = length SSXseq \<and> foldl (@) [] ws = SSw \<and> length ws = length SSXseq \<and> (\<forall>i<length \<pi>s. \<exists>d' n' e'. cfgLM.derivation SSG d' \<and> cfgLM.belongs SSG d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [SSXseq ! i]\<rparr>) \<and> d' n' = Some (pair e' \<lparr>cfg_conf = liftB (ws ! i)\<rparr>) \<and> \<pi>s ! i = map the (get_labels d' n'))" for SSrenPI SSw SSG SSXseq)
   apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>="tl(map the (get_labels d (Suc (Suc n))))"
      in lemma_4_8)
         apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
         apply(force)
        apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
        apply(force)
       apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
       apply(force)
      apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
      apply(force)
     apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
     apply(force)
    apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
    apply(force)
   apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
   apply(simp add: get_labels_def)
  apply(rename_tac d A e e' Xseq w n xa r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
  apply(rule_tac
      x="\<pi>s"
      in exI)
  apply(thin_tac "\<forall>y y'. (\<exists>!wsa. foldl (@) [] y = tl (map the (get_labels d (Suc (Suc n)))) \<and> length y = length Xseq \<and> foldl (@) [] wsa = foldl (@) [] ws \<and> length wsa = length Xseq \<and> (\<forall>i<length y. \<exists>d'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [Xseq ! i]\<rparr>) \<and> (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (wsa ! i)\<rparr>)) \<and> y ! i = map the (get_labels d' n')))) \<and> (\<exists>!wsa. foldl (@) [] y' = tl (map the (get_labels d (Suc (Suc n)))) \<and> length y' = length Xseq \<and> foldl (@) [] wsa = foldl (@) [] ws \<and> length wsa = length Xseq \<and> (\<forall>i<length y'. \<exists>d'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [Xseq ! i]\<rparr>) \<and> (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (wsa ! i)\<rparr>)) \<and> y' ! i = map the (get_labels d' n')))) \<longrightarrow> y = y'")
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
  apply(thin_tac "\<forall>y y'. foldl (@) [] y = foldl (@) [] ws \<and> length y = length Xseq \<and> (\<forall>i<length Xseq. \<exists>d'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [Xseq ! i]\<rparr>) \<and> (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y ! i)\<rparr>)) \<and> \<pi>s ! i = map the (get_labels d' n'))) \<and> foldl (@) [] y' = foldl (@) [] ws \<and> length y' = length Xseq \<and> (\<forall>i<length Xseq. \<exists>d'. cfgLM.derivation G d' \<and> cfgLM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [Xseq ! i]\<rparr>) \<and> (\<exists>n'. (\<exists>e'. d' n' = Some (pair e' \<lparr>cfg_conf = liftB (y' ! i)\<rparr>)) \<and> \<pi>s ! i = map the (get_labels d' n'))) \<longrightarrow> y = y'")
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc(Suc n))) = (Suc(Suc n)) + 1 - (Suc (Suc 0))")
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) (Suc(Suc n))) = (Suc(Suc n)) + 1 - (Suc 0)")
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
  apply(rule conjI)
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule listEqI)
    apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
    apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (d i))) zs)"
      and s="length zs"
      in ssubst)
     apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
     apply (metis length_map)
    apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
    apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc (Suc 0)) (Suc (Suc n))))"
      and s="length (nat_seq (Suc (Suc 0)) (Suc (Suc n)))"
      in ssubst)
     apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
     apply (metis length_map)
    apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
    apply(force)
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="Suc(Suc 0)+i"
      in ssubst)
    apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
     apply(force)
    apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
    apply(force)
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc (Suc n)) = Suc 0 # nat_seq (Suc (Suc 0)) (Suc (Suc n))")
    apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
    apply(clarsimp)
    apply(rename_tac d A e' Xseq n \<pi>s ws i)(*strict*)
    apply(rule_tac
      t="nat_seq (Suc (Suc 0)) (Suc (Suc n)) ! i"
      and s="Suc(Suc 0)+i"
      in ssubst)
     apply(rename_tac d A e' Xseq n \<pi>s ws i)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac d A e' Xseq n \<pi>s ws i)(*strict*)
      apply(force)
     apply(rename_tac d A e' Xseq n \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac d A e' Xseq n \<pi>s ws i)(*strict*)
    apply(clarsimp)
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
   apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
  apply(rule conjI)
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc (Suc n)) = Suc 0 # nat_seq (Suc (Suc 0)) (Suc (Suc n))")
    apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
    prefer 2
    apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
   apply(simp add: get_label_def)
   apply(clarsimp)
   apply(rename_tac d A e' Xseq n \<pi>s ws)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
    apply(rename_tac d A e' Xseq n \<pi>s ws)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc 0"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d A e' Xseq n \<pi>s ws)(*strict*)
      apply(force)
     apply(rename_tac d A e' Xseq n \<pi>s ws)(*strict*)
     apply(force)
    apply(rename_tac d A e' Xseq n \<pi>s ws)(*strict*)
    apply(force)
   apply(rename_tac d A e' Xseq n \<pi>s ws)(*strict*)
   apply(clarsimp)
   apply(rename_tac d A e' Xseq n \<pi>s ws e2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d A e' n \<pi>s ws e2 l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac d A e' n \<pi>s ws e2 l r)(*strict*)
    apply(force)
   apply(rename_tac d A e' n \<pi>s ws e2 l r a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs)(*strict*)
  apply(clarsimp)
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
  apply(simp add: CFGlmEliminators_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc 0"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
     apply(force)
    apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
    apply(force)
   apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
   apply(force)
  apply(rename_tac d A e' Xseq n \<pi>s ws z zs i)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d A e' n \<pi>s ws z zs i l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac d A e' n \<pi>s ws z zs i l r)(*strict*)
   prefer 2
   apply(rename_tac d A e' n \<pi>s ws z zs i l r a list)(*strict*)
   apply(force)
  apply(rename_tac d A e' n \<pi>s ws z zs i l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e' n \<pi>s ws z zs i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc (Suc n)) = Suc 0 # nat_seq (Suc (Suc 0)) (Suc (Suc n))")
   apply(rename_tac d e' n \<pi>s ws z zs i)(*strict*)
   prefer 2
   apply (metis less_eq_Suc_le_raw nat_seq_pullout zero_less_Suc)
  apply(rename_tac d e' n \<pi>s ws z zs i)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e' n \<pi>s ws i)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac d e' n \<pi>s ws i d' n' e'a)(*strict*)
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
  done

lemma existence_of_elimination_string_list: "
  valid_cfg G
  \<Longrightarrow> length \<pi>s=length w
  \<Longrightarrow> \<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (w ! i))
  \<Longrightarrow> \<exists>ws. length \<pi>s = length ws \<and>
               (\<forall>k<length \<pi>s.
                   \<exists>d n e.
                      cfgLM.derivation G d \<and>
                      cfgLM.belongs G d \<and>
                      d 0 =
                      Some (pair None
                             \<lparr>cfg_conf = option_to_list (Some (w ! k))\<rparr>) \<and>
                      d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>) \<and>
                      \<pi>s ! k = map the (get_labels d n))"
  apply(induct w arbitrary: \<pi>s)
   apply(rename_tac \<pi>s)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w \<pi>s)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="drop (Suc 0) \<pi>s"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac a w \<pi>s)(*strict*)
   apply(force)
  apply(rename_tac a w \<pi>s)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w \<pi>s ws)(*strict*)
  apply(erule_tac
      x="0"
      and P="\<lambda>x. x < Suc (length ws) \<longrightarrow> \<pi>s ! x \<in> CFGlmEliminators G (Some ((a # w) ! x))"
      in allE)
  apply(clarsimp)
  apply(simp add: CFGlmEliminators_def)
  apply(clarsimp)
  apply(rename_tac a w \<pi>s ws d n e wa)(*strict*)
  apply(rule_tac
      x="wa#ws"
      in exI)
  apply(clarsimp)
  apply(rename_tac a w \<pi>s ws d n e wa k)(*strict*)
  apply(case_tac k)
   apply(rename_tac a w \<pi>s ws d n e wa k)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w \<pi>s ws d n e wa)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
  apply(rename_tac a w \<pi>s ws d n e wa k nat)(*strict*)
  apply(clarsimp)
  done

lemma unique_elimination: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = v\<rparr>)
  \<Longrightarrow> foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc 0) n)
  \<Longrightarrow> length \<pi>s = length ws
  \<Longrightarrow> length v = length ws
  \<Longrightarrow> \<forall>k<length ws.
           \<exists>d. cfgLM.derivation G d \<and>
               cfgLM.belongs G d \<and>
               d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (v ! k))\<rparr>) \<and>
               (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>)) \<and>
                    \<pi>s ! k = map the (get_labels d n))
  \<Longrightarrow> foldl (@) [] ws = w"
  apply(induct v arbitrary: d n e w \<pi>s ws)
   apply(rename_tac d n e w \<pi>s ws)(*strict*)
   apply(clarsimp)
   apply(rename_tac d n e w)(*strict*)
   apply(case_tac n)
    apply(rename_tac d n e w)(*strict*)
    apply(clarsimp)
    apply(rename_tac d w)(*strict*)
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac d n e w nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e w nat)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
    apply(rename_tac d e w nat)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d e w nat)(*strict*)
      apply(force)
     apply(rename_tac d e w nat)(*strict*)
     apply(force)
    apply(rename_tac d e w nat)(*strict*)
    apply(force)
   apply(rename_tac d e w nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d e w nat e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac a v d n e w \<pi>s ws)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some ((a # v) ! 0))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! 0)\<rparr>)) \<and> \<pi>s ! 0 = map the (get_labels d n))")
   apply(rename_tac a v d n e w \<pi>s ws)(*strict*)
   prefer 2
   apply(erule_tac
      x="0"
      in allE)
   apply(force)
  apply(rename_tac a v d n e w \<pi>s ws)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
  apply(subgoal_tac "na\<le>n")
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   prefer 2
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="na"
      and s="length(\<pi>s!0)"
      in ssubst)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(rule_tac
      t="\<pi>s!0"
      and s="map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) na)"
      in ssubst)
     apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
     apply(force)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSn + 1 - SSi" for SSn SSi)
     apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   apply(rule_tac
      t="n"
      and s="length(foldl (@) [] \<pi>s)"
      in ssubst)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(rule_tac
      t="foldl (@) [] \<pi>s"
      and s="map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc 0) n)"
      in ssubst)
     apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
     apply(force)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
     apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(force)
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   apply (metis length_shorter_than_in_composition zero_less_Suc)
  apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
  apply(subgoal_tac "derivation_map da (\<lambda>x. \<lparr>cfg_conf = (cfg_conf x)@v\<rparr>) na = d na")
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   prefer 2
   apply(rule_tac
      c="foldl (@) [] (drop (Suc 0) \<pi>s)"
      and d'a="d"
      and i="na"
      and n="na"
      and ?m1.0="0"
      and ?m2.0="n-na"
      in equal_labels_implies_equal_cfgLMderivation)
          apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
          apply(force)
         apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
         apply(rule cfgLM.derivation_map_preserves_derivation2)
          apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
          apply(force)
         apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
         apply(clarsimp)
         apply(rename_tac a v d n e w \<pi>s ws da na ea aa eb b)(*strict*)
         apply(simp add: cfgLM_step_relation_def)
         apply(clarsimp)
         apply(rename_tac a v d n e w \<pi>s ws da na ea aa eb b l r)(*strict*)
         apply(rule_tac
      x="l"
      in exI)
         apply(clarsimp)
        apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
        apply(force)
       apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
       apply(simp add: derivation_map_def)
       apply(simp add: option_to_list_def)
      apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
      apply(force)
     apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
     apply(simp add: derivation_map_def)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(force)
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   apply(rule_tac
      t="na+(n-na)"
      and s="n"
      in ssubst)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(force)
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="get_labels (derivation_map da (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ v\<rparr>)) na"
      and s="get_labels da na"
      in ssubst)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(simp add: get_labels_def)
    apply(clarsimp)
    apply(rename_tac a v d n e w \<pi>s ws da na ea x)(*strict*)
    apply(simp add: derivation_map_def)
    apply(case_tac "da x")
     apply(rename_tac a v d n e w \<pi>s ws da na ea x)(*strict*)
     apply(clarsimp)
    apply(rename_tac a v d n e w \<pi>s ws da na ea x aa)(*strict*)
    apply(clarsimp)
    apply(case_tac aa)
    apply(rename_tac a v d n e w \<pi>s ws da na ea x aa option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac a v d n e w \<pi>s ws da na ea x option b)(*strict*)
    apply(simp add: get_label_def)
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   apply(rule_tac
      t="map the (get_labels da na)"
      and s="\<pi>s!0"
      in ssubst)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(force)
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   apply(rule_tac
      t="\<pi>s ! 0 @ foldl (@) [] (drop (Suc 0) \<pi>s)"
      and s="foldl (@) [] \<pi>s"
      in ssubst)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(case_tac "\<pi>s")
     apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
     apply(force)
    apply(rename_tac a v d n e w \<pi>s ws da na ea aa list)(*strict*)
    apply (metis append_Nil drop_0 drop_Suc_Cons foldl_Nil foldl_decomp length_greater_0_conv list.simps(3) nth_Cons_0 take_0)
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   apply(simp add: get_labels_def)
  apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
  apply(subgoal_tac "prefix (ws!0) w")
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>v. cfg_conf \<lparr>cfg_conf = liftB w\<rparr> = liftB (ws!0) @ v")
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    prefer 2
    apply(rule_tac
      v="v"
      and d="d"
      and n="na"
      and m="n-na"
      in CFGLM_terminals_stay_at_front)
        apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
        apply(force)
       apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
       apply(force)
      apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
      apply(simp add: derivation_map_def)
      apply(rule sym)
      apply(force)
     apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac a v d n e w \<pi>s ws da na ea va)(*strict*)
   apply(rule_tac
      x="filterB va"
      in exI)
   apply(rule liftB_inj)
   apply(thin_tac "\<And>d n e w \<pi>s ws. cfgLM.derivation G d \<Longrightarrow> cfgLM.belongs G d \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>) \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = v\<rparr>) \<Longrightarrow> foldl (@) [] \<pi>s = map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc 0) n) \<Longrightarrow> length \<pi>s = length ws \<Longrightarrow> length v = length ws \<Longrightarrow> \<forall>k<length ws. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (v ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>)) \<and> \<pi>s ! k = map the (get_labels d n)) \<Longrightarrow> foldl (@) [] ws = w")
   apply(rename_tac a v d n e w \<pi>s ws da na ea va)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
   apply(rule_tac
      t="liftB (filterB va)"
      and s="va"
      in ssubst)
    apply(rename_tac a v d n e w \<pi>s ws da na ea va)(*strict*)
    apply(subgoal_tac "setA va={}")
     apply(rename_tac a v d n e w \<pi>s ws da na ea va)(*strict*)
     apply (metis liftBDeConv2)
    apply(rename_tac a v d n e w \<pi>s ws da na ea va)(*strict*)
    apply(rule_tac
      a="liftB (ws ! 0)"
      and c="[]"
      in setA_append)
    apply(rule_tac
      t="liftB (ws ! 0) @ va @ []"
      and s="liftB w"
      in ssubst)
     apply(rename_tac a v d n e w \<pi>s ws da na ea va)(*strict*)
     apply(force)
    apply(rename_tac a v d n e w \<pi>s ws da na ea va)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac a v d n e w \<pi>s ws da na ea va)(*strict*)
   apply(force)
  apply(rename_tac a v d n e w \<pi>s ws da na ea)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
  apply(erule_tac
      x="derivation_map (derivation_drop d na) (\<lambda>x. \<lparr>cfg_conf=drop(length(ws!0))(cfg_conf x)\<rparr>)"
      in meta_allE)
  apply(erule_tac
      x="n-na"
      in meta_allE)
  apply(erule_tac
      x="if n-na=0 then None else e"
      in meta_allE)
  apply(erule_tac
      x="c"
      in meta_allE)
  apply(erule_tac
      x="tl \<pi>s"
      in meta_allE)
  apply(erule_tac
      x="tl ws"
      in meta_allE)
  apply(subgoal_tac "cfgLM.derivation G (derivation_map (derivation_drop d na) (\<lambda>x. \<lparr>cfg_conf = drop (length (ws ! 0)) (cfg_conf x)\<rparr>))")
   apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
   prefer 2
   apply(rule_tac
      P="\<lambda>x. prefix (liftB(ws!0)) (cfg_conf x)"
      in cfgLM.derivation_map_preserves_derivation)
     apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
     apply(rule_tac
      m="n-na"
      in cfgLM.derivation_drop_preserves_derivation_prime)
      apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c i eb ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac a v d n e \<pi>s ws da na ea c i eb ca)(*strict*)
    apply(subgoal_tac "\<exists>v. cfg_conf ca = liftB (ws!0) @ v")
     apply(rename_tac a v d n e \<pi>s ws da na ea c ca i eb)(*strict*)
     prefer 2
     apply(rename_tac a v d n e \<pi>s ws da na ea c i eb ca)(*strict*)
     apply(rule_tac
      ?e2.0="if i=0 then ea else eb"
      and d="d"
      and n="na"
      and m="i"
      in CFGLM_terminals_stay_at_front)
         apply(rename_tac a v d n e \<pi>s ws da na ea c i eb ca)(*strict*)
         apply(force)
        apply(rename_tac a v d n e \<pi>s ws da na ea c i eb ca)(*strict*)
        apply(force)
       apply(rename_tac a v d n e \<pi>s ws da na ea c i eb ca)(*strict*)
       apply(simp add: derivation_map_def)
       apply(rule sym)
       apply(force)
      apply(rename_tac a v d n e \<pi>s ws da na ea c i eb ca)(*strict*)
      apply(simp add: derivation_drop_def)
      apply(case_tac i)
       apply(rename_tac a v d n e \<pi>s ws da na ea c i eb ca)(*strict*)
       apply(clarsimp)
       apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca)(*strict*)
       apply(simp add: derivation_map_def)
       apply(case_tac "d na")
        apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca)(*strict*)
        apply(force)
       apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca)(*strict*)
       apply(clarsimp)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca)(*strict*)
      apply(clarsimp)
      apply(rename_tac a v d n e \<pi>s ws da na ea c ca eb nat)(*strict*)
      apply(rule_tac
      t="na+nat"
      and s="nat+na"
      in ssubst)
       apply(rename_tac a v d n e \<pi>s ws da na ea c ca eb nat)(*strict*)
       apply(force)
      apply(rename_tac a v d n e \<pi>s ws da na ea c ca eb nat)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c ca i eb)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c ca i eb)(*strict*)
    apply(clarsimp)
    apply(rename_tac a v d n e \<pi>s ws da na ea c ca i eb va)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c aa eb b)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c aa eb b ca cb)(*strict*)
   apply(case_tac aa)
   apply(rename_tac a v d n e \<pi>s ws da na ea c aa eb b ca cb cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb b ca cb)(*strict*)
   apply(case_tac b)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb b ca cb cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb)(*strict*)
   apply(rule_tac
      t="length (ws!0)"
      and s="length(liftB(ws!0))"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb)(*strict*)
    apply(simp add: liftB_reflects_length)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb)(*strict*)
   apply(rule_tac
      t="length (liftB (ws ! 0)) - length (liftB (ws ! 0))"
      and s="0"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb)(*strict*)
   apply(rule_tac
      t="drop (length (liftB (ws ! 0))) (liftB (ws ! 0))"
      and s="[]"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r)(*strict*)
   apply(subgoal_tac "prefix (liftB (ws ! 0)) l \<or> prefix l (liftB (ws ! 0))")
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r)(*strict*)
   apply(erule disjE)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb r cc)(*strict*)
    apply(rule_tac
      x="cc"
      in exI)
    apply(clarsimp)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb cc)(*strict*)
    apply(simp add: setAConcat)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r cc)(*strict*)
   apply(case_tac cc)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb r)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r cc aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r aa list)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r aa list)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r aa list)(*strict*)
   apply(subgoal_tac "aa=teA (prod_lhs eb)")
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r aa list)(*strict*)
    apply(clarsimp)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r list)(*strict*)
    apply(subgoal_tac "setA (liftB (ws ! 0)) = {}")
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r list)(*strict*)
     apply(subgoal_tac "prod_lhs eb \<in> setA (liftB (ws ! 0))")
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r list)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r list)(*strict*)
     apply(rule_tac
      t="liftB (ws ! 0)"
      and s="l @ teA (prod_lhs eb) # list"
      in ssubst)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r list)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r list)(*strict*)
     apply(simp (no_asm) add: setAConcat)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r list)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r aa list)(*strict*)
   apply(subgoal_tac "[aa]=[teA (prod_lhs eb)]")
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r aa list)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca cb l r aa list)(*strict*)
   apply (metis append_Cons concat_asso nth_append_length)
  apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d na = Some(pair e c)")
   apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
   apply(force)
  apply(rename_tac a v d n e \<pi>s ws da na ea c)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca)(*strict*)
  apply(subgoal_tac "\<exists>v. cfg_conf ca = liftB (ws!0) @ v")
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca)(*strict*)
   prefer 2
   apply(simp add: derivation_map_def)
   apply(clarsimp)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply(simp add: derivation_map_def derivation_drop_def)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(rule_tac
      t="length (ws!0)"
      and s="length(liftB(ws!0))"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply (simp add: liftB_reflects_length)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(rule_tac
      t="length (liftB (ws ! 0)) - length (liftB (ws ! 0))"
      and s="0"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(rule_tac
      t="drop (length (liftB (ws ! 0))) (liftB (ws ! 0))"
      and s="[]"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "ca \<in> cfg_configurations G")
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(clarsimp)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb va)(*strict*)
     apply(rule conjI)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb va)(*strict*)
      apply(rule_tac
      B="setA (liftB (ws ! 0) @ va)"
      in subset_trans)
       apply(rename_tac a v d n e \<pi>s ws da na ea c eb va)(*strict*)
       apply(simp add: setAConcat)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb va)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb va)(*strict*)
     apply(rule_tac
      B="setB (liftB (ws ! 0) @ va)"
      in subset_trans)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb va)(*strict*)
      apply(simp add: setBConcat)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb va)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(force)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(simp add: derivation_map_def derivation_drop_def)
   apply(rule_tac
      t="length (ws!0)"
      and s="length(liftB(ws!0))"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply (simp add: liftB_reflects_length)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule_tac
      t="length (liftB (ws ! 0)) - length (liftB (ws ! 0))"
      and s="0"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule_tac
      t="drop (length (liftB (ws ! 0))) (liftB (ws ! 0))"
      and s="[]"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d n e \<pi>s ws da na c eb va)(*strict*)
   apply(case_tac "n=na")
    apply(rename_tac a d n e \<pi>s ws da na c eb va)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d e \<pi>s ws da na c va)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac a d n e \<pi>s ws da na c eb va)(*strict*)
   apply(clarsimp)
   apply(simp add: liftB_commutes_over_concat)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(simp add: derivation_map_def derivation_drop_def)
   apply(rule_tac
      t="length (ws!0)"
      and s="length(liftB(ws!0))"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply (simp add: liftB_reflects_length)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule_tac
      t="length (liftB (ws ! 0)) - length (liftB (ws ! 0))"
      and s="0"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule_tac
      t="drop (length (liftB (ws ! 0))) (liftB (ws ! 0))"
      and s="[]"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(clarsimp)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule_tac
      w="\<pi>s!0"
      in append_linj)
   apply(rule_tac
      t="\<pi>s ! 0 @ foldl (@) [] (tl \<pi>s)"
      and s="foldl (@) [] \<pi>s"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(case_tac \<pi>s)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va aa list)(*strict*)
    apply(rule foldl_head2)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule_tac
      t="\<pi>s!0"
      and s="map the (get_labels da na)"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule_tac
      t="foldl (@) [] \<pi>s"
      and s="map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc 0) n)"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(simp (no_asm) add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) (n-na)) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(rule listEqI)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(rule_tac
      t="length (map (\<lambda>a. the (get_label (d a))) (nat_seq (Suc 0) n))"
      and s="length ((nat_seq (Suc 0) n))"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply (metis length_map )
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) na) @ map (\<lambda>a. the (get_label (derivation_map (derivation_drop d na) (\<lambda>x. \<lparr>cfg_conf = drop (length (ws ! 0)) (cfg_conf x)\<rparr>) a))) (nat_seq (Suc 0) (n - na)))"
      and s="length (map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) na))+length(map (\<lambda>a. the (get_label (derivation_map (derivation_drop d na) (\<lambda>x. \<lparr>cfg_conf = drop (length (ws ! 0)) (cfg_conf x)\<rparr>) a))) (nat_seq (Suc 0) (n - na)))"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply (metis length_append )
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(rule_tac
      t="length (map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) na))"
      and s="length (nat_seq (Suc 0) na)"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply (metis length_map )
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(rule_tac
      t="length (map (\<lambda>a. the (get_label (derivation_map (derivation_drop d na) (\<lambda>x. \<lparr>cfg_conf = drop (length (ws ! 0)) (cfg_conf x)\<rparr>) a))) (nat_seq (Suc 0) (n - na)))"
      and s="length ((nat_seq (Suc 0) (n - na)))"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
     apply (metis length_map)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="nat_seq (Suc 0) n ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
   apply(clarsimp)
   apply(case_tac "i<na")
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(rule_tac
      t="(map (\<lambda>a. the (get_label (da a))) (nat_seq (Suc 0) na) @ map (\<lambda>a. the (get_label (derivation_map (derivation_drop d na) (\<lambda>x. \<lparr>cfg_conf = drop (length (ws ! 0)) (cfg_conf x)\<rparr>) a))) (nat_seq (Suc 0) (n - na))) ! i"
      and s="(map (\<lambda>a. the (get_label (da a))) (nat_seq (Suc 0) na)) ! i"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(rule nth_append_1)
     apply(rule_tac
      t="length (map (\<lambda>a. the (get_label (da a))) (nat_seq (Suc 0) na))"
      and s="length ((nat_seq (Suc 0) na))"
      in ssubst)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
      apply (metis length_map)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="nat_seq (Suc 0) na ! i"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "derivation_map da (\<lambda>x. \<lparr>cfg_conf = (cfg_conf x)@v\<rparr>) (Suc i) = d (Suc i)")
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     prefer 2
     apply(rule_tac
      c="foldl (@) [] (drop (Suc 0) \<pi>s)"
      and d'a="d"
      and i="Suc i"
      and n="na"
      and ?m1.0="0"
      and ?m2.0="n-na"
      in equal_labels_implies_equal_cfgLMderivation)
            apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
            apply(force)
           apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
           apply(rule cfgLM.derivation_map_preserves_derivation2)
            apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
            apply(force)
           apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
           apply(clarsimp)
           apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i aa ec b)(*strict*)
           apply(simp add: cfgLM_step_relation_def)
           apply(clarsimp)
           apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i aa ec b l r)(*strict*)
           apply(rule_tac
      x="l"
      in exI)
           apply(clarsimp)
          apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
          apply(force)
         apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
         apply(simp add: derivation_map_def)
         apply(simp add: option_to_list_def)
        apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
        apply(force)
       apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
       apply(simp add: derivation_map_def)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(rule_tac
      t="na+(n-na)"
      and s="n"
      in ssubst)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="get_labels (derivation_map da (\<lambda>x. \<lparr>cfg_conf = cfg_conf x @ v\<rparr>)) na"
      and s="get_labels da na"
      in ssubst)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
      apply(simp add: get_labels_def)
      apply(clarsimp)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i x)(*strict*)
      apply(simp add: derivation_map_def)
      apply(case_tac "da x")
       apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i x)(*strict*)
       apply(clarsimp)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i x aa)(*strict*)
      apply(clarsimp)
      apply(rename_tac a d n e \<pi>s ws da na c eb va i x aa)(*strict*)
      apply(case_tac aa)
      apply(rename_tac a d n e \<pi>s ws da na c eb va i x aa option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac a d n e \<pi>s ws da na c eb va i x option b)(*strict*)
      apply(simp add: get_label_def)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(rule_tac
      t="map the (get_labels da na)"
      and s="\<pi>s!0"
      in ssubst)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
      apply(force)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(rule_tac
      t="\<pi>s ! 0 @ foldl (@) [] (drop (Suc 0) \<pi>s)"
      and s="foldl (@) [] \<pi>s"
      in ssubst)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
      apply(case_tac "\<pi>s")
       apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
       apply(force)
      apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i aa list)(*strict*)
      apply (metis append_Nil drop_0 drop_Suc_Cons foldl_Nil foldl_decomp length_greater_0_conv list.simps(3) nth_Cons_0 take_0)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(simp add: get_labels_def)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(simp add: derivation_map_def)
    apply(case_tac "da (Suc i)")
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i aa)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d n e \<pi>s ws da na c eb va i aa)(*strict*)
    apply(case_tac aa)
    apply(rename_tac a d n e \<pi>s ws da na c eb va i aa option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac a d n e \<pi>s ws da na c eb va i option b)(*strict*)
    apply(simp add: get_label_def)
    apply(case_tac "d (Suc i)")
     apply(rename_tac a d n e \<pi>s ws da na c eb va i option b)(*strict*)
     apply(force)
    apply(rename_tac a d n e \<pi>s ws da na c eb va i option b aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
   apply(rule_tac
      t="(map (\<lambda>a. the (get_label (da a))) (nat_seq (Suc 0) na) @ map (\<lambda>a. the (get_label (derivation_map (derivation_drop d na) (\<lambda>x. \<lparr>cfg_conf = drop (length (ws ! 0)) (cfg_conf x)\<rparr>) a))) (nat_seq (Suc 0) (n - na))) ! i"
      and s="(map (\<lambda>a. the (get_label (derivation_map (derivation_drop d na) (\<lambda>x. \<lparr>cfg_conf = drop (length (ws ! 0)) (cfg_conf x)\<rparr>) a))) (nat_seq (Suc 0) (n - na))) ! (i-(length(map (\<lambda>a. the (get_label (da a))) (nat_seq (Suc 0) na))))"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
   apply(rule_tac
      t="length (map (\<lambda>a. the (get_label (da a))) (nat_seq (Suc 0) na))"
      and s="na"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply (metis length_map)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
   apply(simp)
   apply(rule_tac
      t="nat_seq (Suc 0) (n-na) ! (i-na)"
      and s="SSn + SSi" for SSn SSi
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(rule nat_seq_nth_compute)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def derivation_drop_def)
   apply(case_tac "d(Suc i)")
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va i aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d n e \<pi>s ws da na c eb va i aa)(*strict*)
   apply(simp add: get_label_def)
   apply(case_tac aa)
   apply(rename_tac a d n e \<pi>s ws da na c eb va i aa option b)(*strict*)
   apply(force)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(force)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k)(*strict*)
   apply(erule_tac
      x="Suc k"
      in allE)
   apply(clarsimp)
   apply(erule impE)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec)(*strict*)
   apply(rule_tac
      x="db"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="nb"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec)(*strict*)
    apply(case_tac ws)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec aa list)(*strict*)
    apply(rule_tac
      t="ws"
      and s="aa#list"
      in ssubst)
     apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec aa list)(*strict*)
     apply(force)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec aa list)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec)(*strict*)
   apply(rule_tac
      t="map the (get_labels db nb)"
      and s="\<pi>s ! Suc k"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec)(*strict*)
   apply(case_tac \<pi>s)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec aa list)(*strict*)
   apply(rule_tac
      t="\<pi>s"
      and s="aa#list"
      in ssubst)
    apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec aa list)(*strict*)
    apply(force)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va k db nb ec aa list)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
  apply(rule_tac
      t="c"
      and s="foldl (@) [] (tl ws)"
      in ssubst)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(force)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
  apply(rule sym)
  apply(case_tac ws)
   apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va)(*strict*)
   apply(force)
  apply(rename_tac a v d n e \<pi>s ws da na ea c eb ca va aa list)(*strict*)
  apply(rule foldl_head2)
  apply(force)
  done

lemma cfgLM_no_step_from_no_nonterminal: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> setA (cfg_conf c) = {}
  \<Longrightarrow> x>n
  \<Longrightarrow> d x = None"
  apply(case_tac "d x")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "d (Suc n) \<noteq> None")
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac n="x" in cfgLM.derivationNoFromNone2_prime)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(case_tac "Suc n=x")
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> SSd (Suc SSi) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSi)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(case_tac c)
    apply(rename_tac e2 c2 cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 c2 l r)(*strict*)
    apply(case_tac c2)
    apply(rename_tac e2 c2 l r cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 l r)(*strict*)
    apply (metis cfg_configuration.simps(1) cfgLM_no_step_without_nonterms not_None_eq)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> SSd (Suc SSi) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSi)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(case_tac c)
  apply(rename_tac a e2 c2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac a e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a e2 l r)(*strict*)
  apply (metis cfg_configuration.simps(1) cfgLM_no_step_without_nonterms not_None_eq)
  done

definition CFGlm_unambiguous :: "('a,'b) cfg \<Rightarrow> bool" where
  "CFGlm_unambiguous G \<equiv> (\<forall>d1 d2 n1 n2 e1 e2 w.
  cfgLM.derivation_initial G d1
  \<longrightarrow> cfgLM.derivation_initial G d2
  \<longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=liftB w\<rparr>)
  \<longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=liftB w\<rparr>)
  \<longrightarrow> d1 = d2)"

lemma cfgLM_edges_unique_wrt_conf_sequence: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G d1
  \<Longrightarrow> cfgLM.derivation_initial G d2
  \<Longrightarrow> d1 n \<noteq> None
  \<Longrightarrow> d2 n \<noteq> None
  \<Longrightarrow> (\<forall>i\<le>n. cfg_conf(the(get_configuration(d1 (n - i)))) = cfg_conf(the(get_configuration(d2 (n - i)))))
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> d1 i=d2 i"
  apply(induct i)
   apply(clarsimp)
   apply(rename_tac y ya)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d1 0")
    apply(rename_tac y ya)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac y ya a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya b)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac y ya b)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac y ya b a option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya b ba)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya)(*strict*)
  apply(subgoal_tac "\<exists>m. Suc i+m=n")
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule_tac
      x="n-Suc i"
      in exI)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya m)(*strict*)
  apply(erule_tac
      x="m"
      in allE)
  apply(erule impE)
   apply(rename_tac i y ya m)(*strict*)
   apply(force)
  apply(rename_tac i y ya m)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya m)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(i+m)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya m)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i y ya m)(*strict*)
    apply(force)
   apply(rename_tac i y ya m)(*strict*)
   apply(force)
  apply(rename_tac i y ya m)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya m e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i y ya m e1 e2 c1 c2 l r)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya m e1 e2 c1 c2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(i+m)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya m e1 e2 c1 c2 l r)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i y ya m e1 e2 c1 c2 l r)(*strict*)
    apply(force)
   apply(rename_tac i y ya m e1 e2 c1 c2 l r)(*strict*)
   apply(force)
  apply(rename_tac i y ya m e1 e2 c1 c2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya m e1 e2 c1 c2 l r e2a c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i y ya m e1 e2 c1 c2 l r e2a c2a la ra)(*strict*)
  apply(case_tac e2)
  apply(rename_tac i y ya m e1 e2 c1 c2 l r e2a c2a la ra prod_lhsa prod_rhsa)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac i y ya m e1 e2 c1 c2 l r e2a c2a la ra prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa)(*strict*)
  apply(rename_tac C1 r1 C2 r2)
  apply(rename_tac i y ya m e1 e2 c1 c2 l r e2a c2a la ra C1 r1 C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya m e1 c1 c2 l r c2a la ra C1 r1 C2 r2)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac i y ya m e1 c1 c2 l r c2a la ra C1 r1 C2 r2)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (metis liftBDeConv2)
  apply(rename_tac i y ya m e1 c1 c2 l r c2a la ra C1 r1 C2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya m e1 c1 c2 r c2a la ra C1 r1 C2 r2 l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "\<exists>la'. liftB la' = la")
   apply(rename_tac i y ya m e1 c1 c2 r c2a la ra C1 r1 C2 r2 l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (metis liftBDeConv2)
  apply(rename_tac i y ya m e1 c1 c2 r c2a la ra C1 r1 C2 r2 l')(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya m e1 c1 c2 r c2a ra C1 r1 C2 r2 l' la')(*strict*)
  apply(thin_tac "setA (liftB la') = {}")
  apply(subgoal_tac "l'=la'")
   apply(rename_tac i y ya m e1 c1 c2 r c2a ra C1 r1 C2 r2 l' la')(*strict*)
   prefer 2
   apply(rule identical_temrinal_maximal_prefix) 
   apply(force)
  apply(rename_tac i y ya m e1 c1 c2 r c2a ra C1 r1 C2 r2 l' la')(*strict*)
  apply(clarsimp)
  done

lemma equal_eliminators_hlp2: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d1
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> d1 0 = d2 0
  \<Longrightarrow> d1 (n+x1) \<noteq> None
  \<Longrightarrow> d2 (n+x2) \<noteq> None
  \<Longrightarrow> get_labels d1 n = get_labels d2 n
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> d1 i = d2 i"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> d1 (Suc i) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+x1"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya)(*strict*)
     apply(force)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 i = Some (pair e1 c1) \<and> d2 (Suc i) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+x2"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya)(*strict*)
     apply(force)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a c1 c2 c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac i y ya e1 e2 e2a c1 c2 c2a l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a c1 c2 l r la ra)(*strict*)
  apply(case_tac c1)
  apply(rename_tac i y ya e1 e2 e2a c1 c2 l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a c2 l r la ra)(*strict*)
  apply(case_tac c2)
  apply(rename_tac i y ya e1 e2 e2a c2 l r la ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(subgoal_tac "(get_labels d1 n)!i = (get_labels d2 n)!i")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(thin_tac "get_labels d1 n = get_labels d2 n")
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(subgoal_tac "(\<lambda>i. get_label (d1 i)) ((nat_seq (Suc 0) n) ! i) = (\<lambda>i. get_label (d2 i)) ((nat_seq (Suc 0) n) ! i)")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      t="get_label (d1 (nat_seq (Suc 0) n ! i))"
      and s="map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n) ! i"
      in subst)
    apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   apply(rule_tac
      t="get_label (d2 (nat_seq (Suc 0) n ! i))"
      and s="map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) n) ! i"
      in subst)
    apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(subgoal_tac "nat_seq (Suc 0) n ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
  apply(subgoal_tac "l=la")
   apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
  apply (metis Cons_eq_appendI append_Nil terminalHeadEquals1)
  done

lemma cfgLM_equal_labels_imply_equal_positions: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d1
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> d1 0 = d2 0
  \<Longrightarrow> get_labels d1 n = get_labels d2 n
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> d1 (n+m1) \<noteq> None
  \<Longrightarrow> d2 (n+m2) \<noteq> None
  \<Longrightarrow> d1 i = d2 i"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya)(*strict*)
  apply(subgoal_tac "get_labels d1 n ! i = get_labels d2 n !i")
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = n + 1 - Suc 0")
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i y ya)(*strict*)
  apply(subgoal_tac "(\<lambda>i. get_label (d1 i)) ((nat_seq (Suc 0) n) ! i) = (\<lambda>i. get_label (d2 i)) ((nat_seq (Suc 0) n) ! i)")
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule_tac
      t="get_label (d1 (nat_seq (Suc 0) n ! i))"
      and s="map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) n) ! i"
      in subst)
    apply(rename_tac i y ya)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(rule_tac
      t="get_label (d2 (nat_seq (Suc 0) n ! i))"
      and s="map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) n) ! i"
      in subst)
    apply(rename_tac i y ya)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(clarsimp)
  apply(rename_tac i y ya)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) n ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+m1"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya)(*strict*)
     apply(force)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+m2"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r la ra)(*strict*)
  apply(case_tac c1)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r la ra cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r la ra cfg_confa cfg_confaa)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r la ra cfg_confa cfg_confaa cfg_confb)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(simp add: get_label_def)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
  apply(subgoal_tac "l=la")
   apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
   apply(clarsimp)
  apply(rename_tac i y ya e1 e2a l r la ra)(*strict*)
  apply (metis Cons_eq_appendI append_Nil terminalHeadEquals1)
  done

lemma cfgLM_unique_terminal_configurations1: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e1 \<lparr>cfg_conf=liftB w1\<rparr>)
  \<Longrightarrow> d m = Some (pair e2 \<lparr>cfg_conf=liftB w2\<rparr>)
  \<Longrightarrow> n<m
  \<Longrightarrow> Q"
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   prefer 2
   apply(rule_tac
      m="m"
      in cfgLM.step_detail_before_some_position)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e2a c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e2a c2 l r)(*strict*)
  apply (metis suffixes_setA_1 suffixes_intro1 setA_liftB all_not_in_conv emptyE)
  done

lemma cfgLM_unique_terminal_configurations: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e1 \<lparr>cfg_conf=liftB w1\<rparr>)
  \<Longrightarrow> d m = Some (pair e2 \<lparr>cfg_conf=liftB w2\<rparr>)
  \<Longrightarrow> n=m"
  apply(case_tac "n<m")
   apply(rule_tac
      n="n"
      and m="m"
      in cfgLM_unique_terminal_configurations1)
       apply(force)+
  apply(case_tac "m<n")
   apply(rule_tac
      n="m"
      and m="n"
      in cfgLM_unique_terminal_configurations1)
       apply(force)+
  done

lemma cfgLM_equal_positions_when_same_productions: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d1
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> d1 0 = d2 0
  \<Longrightarrow> d1 n2 \<noteq> None
  \<Longrightarrow> d2 n2 \<noteq> None
  \<Longrightarrow> map the (get_labels d1 n2) = map the (get_labels d2 n2)
  \<Longrightarrow> x \<le> n2
  \<Longrightarrow> d1 x = d2 x"
  apply(induct x)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y ya)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 x = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="n2"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x y ya)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac x y ya)(*strict*)
    apply(force)
   apply(rename_tac x y ya)(*strict*)
   apply(force)
  apply(rename_tac x y ya)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 x = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="n2"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x y ya)(*strict*)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rename_tac x y ya)(*strict*)
    apply(force)
   apply(rename_tac x y ya)(*strict*)
   apply(force)
  apply(rename_tac x y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac x y ya e1 e2a c1 c2 c2a l r la ra)(*strict*)
   apply(case_tac c2a)
   apply(rename_tac x y ya e1 e2a c1 c2 c2a l r la ra cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x y ya e1 e2a c1 c2 l r la ra)(*strict*)
   apply(case_tac c2)
   apply(rename_tac x y ya e1 e2a c1 c2 l r la ra cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x y ya e1 e2a c1 l r la ra)(*strict*)
   apply(subgoal_tac "l=la")
    apply(rename_tac x y ya e1 e2a c1 l r la ra)(*strict*)
    apply(clarsimp)
   apply(rename_tac x y ya e1 e2a c1 l r la ra)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = la")
    apply(rename_tac x y ya e1 e2a c1 l r la ra)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB la"
      in exI)
    apply (rule liftBDeConv2)
    apply(force)
   apply(rename_tac x y ya e1 e2a c1 l r la ra)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac x y ya e1 e2a c1 l r la ra)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply(force)
   apply(rename_tac x y ya e1 e2a c1 l r la ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac x y ya e1 e2a c1 r ra l' l'a)(*strict*)
   apply (metis maximalPrefixB_prefix2_prime)
  apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n2) = n2 + 1 - Suc 0")
   apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) n2 ! x = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
    apply(force)
   apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
   apply(force)
  apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
  apply(rule_tac
      t="e2"
      and s="(map the (get_labels d1 n2))!x"
      in ssubst)
   apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      t="e2a"
      and s="(map the (get_labels d2 n2))!x"
      in ssubst)
    apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (d2 i))) (nat_seq (Suc 0) n2) ! x"
      and s=" (the \<circ> (\<lambda>i. get_label (d2 i))) ((nat_seq (Suc 0) n2) ! x) "
      in ssubst)
    apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
   apply(simp add: get_label_def)
  apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
  apply(simp add: get_labels_def)
  apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (d1 i))) (nat_seq (Suc 0) n2) ! x"
      and s=" (the \<circ> (\<lambda>i. get_label (d1 i))) ((nat_seq (Suc 0) n2) ! x) "
      in ssubst)
   apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
   apply(rule nth_map)
   apply(force)
  apply(rename_tac x y ya e1 e2 e2a c1 c2 c2a l r la ra)(*strict*)
  apply(simp add: get_label_def)
  done

lemma cfgLM_get_labels_eq_implies_equal_hlp: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G d1
  \<Longrightarrow> cfgLM.derivation_initial G d2
  \<Longrightarrow> d1 n = Some (pair e1 c1)
  \<Longrightarrow> d2 n = Some (pair e2 c2)
  \<Longrightarrow> get_labels d1 n = get_labels d2 n
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> d1 i = d2 i"
  apply(induct i arbitrary: e1 e2 c1 c2)
   apply(rename_tac e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d1 0")
    apply(rename_tac e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac e1 e2 c1 c2 a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 b)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac e1 e2 c1 c2 b)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac e1 e2 c1 c2 b a option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c1 c2 b ba)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i e1 e2 c1 c2)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac i e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
    apply(force)
   apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a e1b c2b)(*strict*)
  apply(erule_tac
      x="e2"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a e1b c2b)(*strict*)
  apply(simp add: get_labels_def)
  apply(erule_tac
      x="Suc i"
      in ballE)
   apply(rename_tac i e1 e2 c1 c2 e1a e2a c1a c2a e1b c2b)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c1 c2 e1a c1a c2a e1b c2b)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c1 c2 e1a c1a c2a e1b c2b l r la ra)(*strict*)
   apply(case_tac c2b)
   apply(rename_tac i e1 e2 c1 c2 e1a c1a c2a e1b c2b l r la ra cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c1 c2 e1a c1a c2a e1b l r la ra)(*strict*)
   apply(case_tac c2a)
   apply(rename_tac i e1 e2 c1 c2 c2a e1b e2b c1b l r la ra cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c1 c2 e1b e2b c1b l r la ra)(*strict*)
   apply(case_tac c1b)
   apply(rename_tac i e1 e2 c1 c2 e1b e2b c1b l r la ra cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c1 c2 e1b e2b l r la ra)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac i e1 e2 c1 c2 e1b e2b l r la ra)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply(force)
   apply(rename_tac i e1 e2 c1 c2 e1b e2b l r la ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c1 c2 e1b e2b r la ra l')(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = e1b")
    apply(rename_tac i e1 e2 c1 c2 e1b e2b r la ra l')(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB e1b"
      in exI)
    apply (rule liftBDeConv2)
    apply(force)
   apply(rename_tac i e1 e2 c1 c2 e1b e2b r la ra l')(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c1 c2 e1b e2b r ra l' l'a)(*strict*)
   apply(simp add: simpY)
   apply(subgoal_tac "l'a=l'")
    apply(rename_tac i e1 e2 c1 c2 e1b e2b r ra l' l'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac i e1 e2 c1 c2 e1b e2b r ra l' l'a)(*strict*)
   apply (metis maxTermPrefix_mixed_string maxTermPrefix_shift)
  apply(rename_tac i e1 e2 c1 c2 e2a c2a e1b e2b c1b c2b)(*strict*)
  apply(subgoal_tac "Suc i \<in> set (nat_seq (Suc 0) n)")
   apply(rename_tac i e1 e2 c1 c2 e2a c2a e1b e2b c1b c2b)(*strict*)
   apply(force)
  apply(rename_tac i e1 e2 c1 c2 e2a c2a e1b e2b c1b c2b)(*strict*)
  apply(rule nat_seq_interval)
   apply(rename_tac i e1 e2 c1 c2 e2a c2a e1b e2b c1b c2b)(*strict*)
   apply(force)
  apply(rename_tac i e1 e2 c1 c2 e2a c2a e1b e2b c1b c2b)(*strict*)
  apply(force)
  done

lemma cfgLM_get_labels_eq_implies_equal: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation_initial G d1
  \<Longrightarrow> cfgLM.derivation_initial G d2
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=liftB w1\<rparr>)
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=liftB w2\<rparr>)
  \<Longrightarrow> get_labels d1 n1 = get_labels d2 n2
  \<Longrightarrow> d1 = d2"
  apply(subgoal_tac "n1=n2 \<and> (\<forall>i\<le>n1. d1 i = d2 i)")
   apply(clarsimp)
   apply(rule ext)
   apply(rename_tac x)(*strict*)
   apply(case_tac "x\<le>n2")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "x>n2")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "d1 x = None")
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "d2 x = None")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(case_tac "d2 x")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x a)(*strict*)
    apply(subgoal_tac "x-n2 = 0")
     apply(rename_tac x a)(*strict*)
     prefer 2
     apply(rule_tac
      d="d2"
      and n="n2"
      in cfgLM_no_step_without_nontermsX)
         apply(rename_tac x a)(*strict*)
         apply(force)
        apply(rename_tac x a)(*strict*)
        apply(simp add: cfgLM.derivation_initial_def)
       apply(rename_tac x a)(*strict*)
       apply(force)
      apply(rename_tac x a)(*strict*)
      apply(clarsimp)
      apply(simp add: simpY)
     apply(rename_tac x a)(*strict*)
     apply(clarsimp)
    apply(rename_tac x a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(case_tac "d1 x")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x a)(*strict*)
   apply(subgoal_tac "x-n2 = 0")
    apply(rename_tac x a)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and n="n2"
      in cfgLM_no_step_without_nontermsX)
        apply(rename_tac x a)(*strict*)
        apply(force)
       apply(rename_tac x a)(*strict*)
       apply(simp add: cfgLM.derivation_initial_def)
      apply(rename_tac x a)(*strict*)
      apply(force)
     apply(rename_tac x a)(*strict*)
     apply(clarsimp)
     apply(simp add: simpY)
    apply(rename_tac x a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
  apply(subgoal_tac "n1=n2")
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(rule cfgLM_get_labels_eq_implies_equal_hlp)
         apply(rename_tac i)(*strict*)
         apply(force)+
  apply (metis get_labels_length)
  done

lemma cfgLM_no_position_beyond_liftB_configuration: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> d m = Some (pair e' \<lparr>cfg_conf=liftB w\<rparr>)
  \<Longrightarrow> n\<le>m"
  apply(case_tac "n\<le>m")
   apply(force)
  apply(subgoal_tac "n>m")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d m = Some (pair e1 c1) \<and> d (Suc m) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   prefer 2
   apply(rule_tac
      m="n"
      in cfgLM.step_detail_before_some_position)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e2 c2 l r)(*strict*)
  apply (metis setA_liftB elemInsetA ex_in_conv)
  done

lemma cfgLM_left_context_can_be_dropped: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=liftB w @ v0\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=liftB w @ v1\<rparr>)
  \<Longrightarrow> \<exists>d'.
  cfgLM.derivation G d'
  \<and> get_labels d' n = get_labels d n
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=v0\<rparr>)
  \<and> d' n = Some (pair e \<lparr>cfg_conf=v1\<rparr>)"
  apply(induct n arbitrary: d e v1)
   apply(rename_tac d e v1)(*strict*)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = v0\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac d)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac d)(*strict*)
   apply(rule conjI)
    apply(rename_tac d)(*strict*)
    apply(rule_tac
      t="get_labels (der1 \<lparr>cfg_conf = v0\<rparr>) 0"
      and s="[]"
      in ssubst)
     apply(rename_tac d)(*strict*)
     apply (metis get_labelsEmpty)
    apply(rename_tac d)(*strict*)
    apply(rule sym)
    apply (metis get_labelsEmpty)
   apply(rename_tac d)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac n d e v1)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="derivation_take d n"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac n d e v1)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac n d e v1)(*strict*)
     apply(force)
    apply(rename_tac n d e v1)(*strict*)
    apply(force)
   apply(rename_tac n d e v1)(*strict*)
   apply(force)
  apply(rename_tac n d e v1)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d v1 e1 e2 c1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n d v1 e1 e2 c1 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n d v1 e1 e2 c1 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d v1 e1 e2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac n d v1 e1 e2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac n d v1 e1 e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d v1 e1 e2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e2)
  apply(rename_tac n d v1 e1 e2 r l' prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac B v)
  apply(rename_tac n d v1 e1 e2 r l' B v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d v1 e1 r l' B v)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(subgoal_tac "\<exists>v. cfg_conf SSc2 = liftB SSw @ v" for SSc2 SSw)
   apply(rename_tac n d v1 e1 r l' B v)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and w="w"
      and n="0"
      and m="n"
      in CFGLM_terminals_stay_at_front)
       apply(rename_tac n d v1 e1 r l' B v)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac n d v1 e1 r l' B v)(*strict*)
      apply(force)
     apply(rename_tac n d v1 e1 r l' B v)(*strict*)
     apply(force)
    apply(rename_tac n d v1 e1 r l' B v)(*strict*)
    apply(force)
   apply(rename_tac n d v1 e1 r l' B v)(*strict*)
   apply(force)
  apply(rename_tac n d v1 e1 r l' B v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d v1 e1 r l' B v va)(*strict*)
  apply(subgoal_tac "prefix w l'")
   apply(rename_tac n d v1 e1 r l' B v va)(*strict*)
   prefer 2
   apply (metis maximalPrefixB_prefix maximalPrefixB_prefix2_prime)
  apply(rename_tac n d v1 e1 r l' B v va)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac n d v1 e1 r B v va c)(*strict*)
  apply(simp add: simpY)
  apply(erule_tac
      x="va"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n d e1 r B v c)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d e1 r B v c)(*strict*)
   apply(rule cfgLM.derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac n d e1 r B v c)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d e1 r B v c)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n d e1 r B v c)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d e1 r B v c)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n d e1 r B v c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(rule_tac
      x="derivation_append d' (der2 \<lparr>cfg_conf = liftB c @ teA B # r\<rparr> \<lparr>prod_lhs = B, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB c @ v @ r\<rparr>) n"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac n d e1 r B v c d')(*strict*)
     apply(force)
    apply(rename_tac n d e1 r B v c d')(*strict*)
    apply(rule cfgLM.der2_is_derivation)
    apply(simp add: cfgLM_step_relation_def)
    apply(rule_tac
      x="liftB c"
      in exI)
    apply(clarsimp)
    apply(simp add: simpY)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(rule conjI)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   prefer 2
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(rule_tac
      t="Suc n"
      and s="n+Suc 0"
      in ssubst)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(force)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append d' (der2 \<lparr>cfg_conf = liftB c @ teA B # r\<rparr> \<lparr>prod_lhs = B, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB c @ v @ r\<rparr>) n) (n + Suc 0)"
      and s="get_labels d' n @ (get_labels (der2 \<lparr>cfg_conf = liftB c @ teA B # r\<rparr> \<lparr>prod_lhs = B, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB c @ v @ r\<rparr>) (Suc 0))"
      in ssubst)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(rule cfgLM.get_labels_concat2)
       apply(rename_tac n d e1 r B v c d')(*strict*)
       apply(force)
      apply(rename_tac n d e1 r B v c d')(*strict*)
      apply(force)
     apply(rename_tac n d e1 r B v c d')(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="liftB c"
      in exI)
     apply(clarsimp)
     apply(simp add: simpY)
    apply(rename_tac n d e1 r B v c d')(*strict*)
    apply(clarsimp)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(rule_tac
      t="get_labels (der2 \<lparr>cfg_conf = liftB c @ teA B # r\<rparr> \<lparr>prod_lhs = B, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB c @ v @ r\<rparr>) (Suc 0)"
      and s="[Some \<lparr>prod_lhs = B, prod_rhs = v\<rparr>]"
      in ssubst)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(rule der2_get_labels)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(clarsimp)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSn + 1 - SSi" for SSn SSi)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(clarsimp)
  apply(rule listEqI)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(force)
  apply(rename_tac n d e1 r B v c d' i)(*strict*)
  apply(clarsimp)
  apply(case_tac "i<n")
   apply(rename_tac n d e1 r B v c d' i)(*strict*)
   apply(rule_tac
      t="(map (\<lambda>i. get_label (derivation_take d n i)) (nat_seq (Suc 0) n) @ [Some \<lparr>prod_lhs = B, prod_rhs = v\<rparr>]) ! i"
      and s="(map (\<lambda>i. get_label (derivation_take d n i)) (nat_seq (Suc 0) n)) ! i"
      in ssubst)
    apply(rename_tac n d e1 r B v c d' i)(*strict*)
    apply(rule nth_append_1)
    apply(force)
   apply(rename_tac n d e1 r B v c d' i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
   apply(subgoal_tac "nat_seq (Suc 0) n ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac n d e1 r B v c d' i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac n d e1 r B v c d' i)(*strict*)
     apply(force)
    apply(rename_tac n d e1 r B v c d' i)(*strict*)
    apply(force)
   apply(rename_tac n d e1 r B v c d' i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc n) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac n d e1 r B v c d' i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac n d e1 r B v c d' i)(*strict*)
     apply(force)
    apply(rename_tac n d e1 r B v c d' i)(*strict*)
    apply(force)
   apply(rename_tac n d e1 r B v c d' i)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d e1 r B v c d' i)(*strict*)
  apply(subgoal_tac "i=n")
   apply(rename_tac n d e1 r B v c d' i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d e1 r B v c d' i)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(rule_tac
      t="(map (\<lambda>i. get_label (derivation_take d n i)) (nat_seq (Suc 0) n) @ [Some \<lparr>prod_lhs = B, prod_rhs = v\<rparr>]) ! n"
      and s="[Some \<lparr>prod_lhs = B, prod_rhs = v\<rparr>] ! (n-length (map (\<lambda>i. get_label (derivation_take d n i)) (nat_seq (Suc 0) n)))"
      in ssubst)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(rule nth_append_2)
   apply(force)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc n) ! n = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac n d e1 r B v c d')(*strict*)
    apply(force)
   apply(rename_tac n d e1 r B v c d')(*strict*)
   apply(force)
  apply(rename_tac n d e1 r B v c d')(*strict*)
  apply(clarsimp)
  done

lemma cfgLM_drop_first_production: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> d (Suc 0) = Some (pair (Some e1) c1)
  \<Longrightarrow> Some e1#(get_labels (derivation_drop d (Suc 0)) n) = get_labels d (Suc n)"
  apply(simp add: get_labels_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = [Suc 0]@(nat_seq (Suc (Suc 0)) (Suc n))")
   prefer 2
   apply(rule nat_seq_drop_first)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(subgoal_tac "length (nat_seq (Suc (Suc 0)) (Suc n)) = SSn + 1 - SSi" for SSn SSi)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rule conjI)
   apply(simp add: get_label_def)
  apply(rule listEqI)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) n ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc (Suc 0)) (Suc n) ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_drop_def get_label_def)
  done

lemma cfg_sub_preserves_cfgLM_belongs: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G' d
  \<Longrightarrow> cfgLM.belongs G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgLM.belongs G d"
  apply(simp add: cfgLM.belongs_def cfg_sub_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac i option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac i b)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(simp add: cfg_configurations_def)
   apply(clarsimp)
   apply(rename_tac i c)(*strict*)
   apply(force)
  apply(rename_tac i option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b a)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac i a c)(*strict*)
  apply(simp add: cfg_step_labels_def)
  apply(force)
  done

lemma cfgLM_drop_leading_terminals: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=liftB w@w'\<rparr>)
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow>
  (\<forall>i\<le>n. prefix(liftB w)(cfg_conf(the(get_configuration(d i)))))
  \<and> cfgLM.derivation G (derivation_map d (\<lambda>v. \<lparr>cfg_conf = drop (length w) (cfg_conf v)\<rparr>))
  \<and> cfgLM.belongs G (derivation_map d (\<lambda>v. \<lparr>cfg_conf = drop (length w) (cfg_conf v)\<rparr>))"
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac y i)(*strict*)
   apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
    apply(rename_tac y i)(*strict*)
    prefer 2
    apply(rule_tac
      m="n"
      in cfgLM.pre_some_position_is_some_position)
      apply(rename_tac y i)(*strict*)
      apply(force)
     apply(rename_tac y i)(*strict*)
     apply(force)
    apply(rename_tac y i)(*strict*)
    apply(force)
   apply(rename_tac y i)(*strict*)
   apply(clarsimp)
   apply(rename_tac y i e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac c)
   apply(rename_tac y i e c cfg_confa)(*strict*)
   apply(rename_tac v)
   apply(rename_tac y i e c v)(*strict*)
   apply(clarsimp)
   apply(rename_tac y i e v)(*strict*)
   apply(subgoal_tac "\<exists>v. cfg_conf SSc2 = liftB SSw @ v" for SSc2 SSw)
    apply(rename_tac y i e v)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      and d="d"
      and n="0"
      and m="i"
      in CFGLM_terminals_stay_at_front)
        apply(rename_tac y i e v)(*strict*)
        apply(force)
       apply(rename_tac y i e v)(*strict*)
       apply(force)
      apply(rename_tac y i e v)(*strict*)
      apply(force)
     apply(rename_tac y i e v)(*strict*)
     apply(force)
    apply(rename_tac y i e v)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac y i e v)(*strict*)
   apply(clarsimp)
   apply(rename_tac y i e va)(*strict*)
   apply(simp add: prefix_def)
  apply(rule context_conjI)
   apply(rule_tac
      P="\<lambda>c. take (length w) (cfg_conf c) = liftB w"
      in cfgLM.derivation_map_preserves_derivation)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e c y)(*strict*)
    apply(case_tac c)
    apply(rename_tac i e c y cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e cfg_conf y)(*strict*)
    apply(rename_tac i e v y)(*strict*)
    apply(subgoal_tac "\<exists>v. cfg_conf SSc2 = liftB SSw @ v" for SSc2 SSw)
     apply(rename_tac y i e v)(*strict*)
     prefer 2
     apply(rename_tac i e v y)(*strict*)
     apply(rule_tac
      G="G"
      and d="d"
      and n="0"
      and m="i"
      in CFGLM_terminals_stay_at_front)
         apply(rename_tac y i e v)(*strict*)
         apply(force)
        apply(rename_tac y i e v)(*strict*)
        apply(force)
       apply(rename_tac y i e v)(*strict*)
       apply(force)
      apply(rename_tac y i e v)(*strict*)
      apply(force)
     apply(rename_tac y i e v)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac y i e v)(*strict*)
    apply(clarsimp)
    apply(rename_tac y i e va)(*strict*)
    apply (metis liftB_reflects_length append_Nil2 diff_self_eq_0 le_refl take_0 take_liftB take_all)
   apply(rename_tac c1 e c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac y a e b)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac y a e b l r)(*strict*)
   apply(case_tac "length w-length l")
    apply(rename_tac y a e b l r)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="drop (length w) l"
      in exI)
    apply(clarsimp)
    apply (metis setADropIndexSubset2 subset_empty)
   apply(rename_tac y a e b l r nat)(*strict*)
   apply(clarsimp)
   apply(case_tac b)
   apply(rename_tac y a e b l r nat option conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac y a e l r nat option conf)(*strict*)
   apply(case_tac a)
   apply(rename_tac y a e l r nat option conf prod_lhsa prod_rhsa)(*strict*)
   apply(clarsimp)
   apply(rename_tac y e l r nat option conf prod_lhs prod_rhs)(*strict*)
   apply(rename_tac y e l r nat option conf prod_lhs prod_rhs)
   apply (metis setA_liftB elemInsetA emptyE)
  apply(rule cfgLM.derivation_map_preserves_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac y ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac y ca)(*strict*)
   apply (metis setADropIndexSubset2 psubset_eq psubset_subset_trans)
  apply(rename_tac y ca)(*strict*)
  apply (metis setBDropIndexSubset2 psubset_eq psubset_subset_trans)
  done

lemma unique_CFGlmEliminators_final_string: "
  valid_cfg G
  \<Longrightarrow> \<pi> \<in> CFGlmEliminators G X
  \<Longrightarrow> \<exists>!w. \<exists>d n e.
  cfgLM.derivation G d
  \<and> cfgLM.belongs G d
  \<and> d 0 = Some (pair None \<lparr>cfg_conf=(option_to_list X)\<rparr>)
  \<and> d n = Some (pair e \<lparr>cfg_conf=liftB w\<rparr>)
  \<and> \<pi>=map the (get_labels d n)"
  apply(rule HOL.ex_ex1I)
   apply(clarsimp)
   apply(simp add: CFGlmEliminators_def)
   apply(clarsimp)
   apply(rename_tac d n e w)(*strict*)
   apply(rule_tac
      x="w"
      in exI)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
  apply(rename_tac w y)(*strict*)
  apply(clarsimp)
  apply(rename_tac w y d da n na e ea)(*strict*)
  apply(subgoal_tac "n=na")
   apply(rename_tac w y d da n na e ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac w y d da na e ea)(*strict*)
   apply(subgoal_tac "da na = d na")
    apply(rename_tac w y d da na e ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac w y d da na ea)(*strict*)
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac w y d da na e ea)(*strict*)
   apply(rule_tac
      n="na"
      and ?m1.0="0"
      and ?m2.0="0"
      in equal_labels_implies_equal_cfgLMderivation)
          apply(rename_tac w y d da na e ea)(*strict*)
          apply(force)
         apply(rename_tac w y d da na e ea)(*strict*)
         apply(force)
        apply(rename_tac w y d da na e ea)(*strict*)
        apply(force)
       apply(rename_tac w y d da na e ea)(*strict*)
       apply(force)
      apply(rename_tac w y d da na e ea)(*strict*)
      apply(force)
     apply(rename_tac w y d da na e ea)(*strict*)
     apply(force)
    apply(rename_tac w y d da na e ea)(*strict*)
    apply(force)
   apply(rename_tac w y d da na e ea)(*strict*)
   apply(force)
  apply(rename_tac w y d da n na e ea)(*strict*)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
   apply(rename_tac w y d da n na e ea)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac w y d da n na e ea)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSn + 1 - SSi" for SSn SSi)
   apply(rename_tac w y d da n na e ea)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac w y d da n na e ea)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n)) = length(map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) na))")
   apply(rename_tac w y d da n na e ea)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w y d da n na e ea)(*strict*)
  apply(rule_tac
      t="n"
      and s="length (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n))"
      in ssubst)
   apply(rename_tac w y d da n na e ea)(*strict*)
   apply (metis length_map)
  apply(rename_tac w y d da n na e ea)(*strict*)
  apply(rule_tac
      t="na"
      and s="length (map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) na))"
      in ssubst)
   apply(rename_tac w y d da n na e ea)(*strict*)
   apply (metis length_map)
  apply(rename_tac w y d da n na e ea)(*strict*)
  apply(force)
  done

lemma uniqueness_of_elimination_string_list_hlp: "
  valid_cfg G
  \<Longrightarrow> length ws1 = length w
  \<Longrightarrow> length ws2 = length w
  \<Longrightarrow> \<forall>k<length w. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and>d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (w ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws1 ! k)\<rparr>)) \<and> \<pi>s ! k = map the (get_labels d n))
  \<Longrightarrow> length \<pi>s = length w
  \<Longrightarrow> \<forall>k<length w. \<exists>d. cfgLM.derivation G d \<and> cfgLM.belongs G d \<and> d 0 = Some (pair None \<lparr>cfg_conf = option_to_list (Some (w ! k))\<rparr>) \<and> (\<exists>n. (\<exists>e. d n = Some (pair e \<lparr>cfg_conf = liftB (ws2 ! k)\<rparr>)) \<and> \<pi>s ! k = map the (get_labels d n))
  \<Longrightarrow> i < length w \<Longrightarrow> ws1 ! i = ws2 ! i"
  apply(induct i rule: less_induct)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in allE)+
  apply(clarsimp)
  apply(rename_tac x d da n na e ea)(*strict*)
  apply(subgoal_tac "n=na")
   apply(rename_tac x d da n na e ea)(*strict*)
   prefer 2
   apply(simp add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac x d da n na e ea)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac x d da n na e ea)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) (Suc na)) = SSm + 1 - SSn" for SSm SSn)
    apply(rename_tac x d da n na e ea)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac x d da n na e ea)(*strict*)
   apply (metis One_nat_def Suc_eq_plus1 diff_Suc_1 length_map nat_seq_length_prime)
  apply(rename_tac x d da n na e ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d da na e ea)(*strict*)
  apply(subgoal_tac "d na=da na")
   apply(rename_tac x d da na e ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d da na e)(*strict*)
   apply(rule liftB_inj)
   apply(rule sym)
   apply(force)
  apply(rename_tac x d da na e ea)(*strict*)
  apply(rule_tac
      d'="d"
      and d'a="da"
      and n="na"
      and ?m1.0="0"
      and ?m2.0="0"
      and i="na"
      in equal_labels_implies_equal_cfgLMderivation)
         apply(rename_tac x d da na e ea)(*strict*)
         apply(force)
        apply(rename_tac x d da na e ea)(*strict*)
        apply(force)
       apply(rename_tac x d da na e ea)(*strict*)
       apply(force)
      apply(rename_tac x d da na e ea)(*strict*)
      apply(force)
     apply(rename_tac x d da na e ea)(*strict*)
     apply(force)
    apply(rename_tac x d da na e ea)(*strict*)
    apply(force)
   apply(rename_tac x d da na e ea)(*strict*)
   apply(force)
  apply(rename_tac x d da na e ea)(*strict*)
  apply(force)
  done

lemma uniqueness_of_elimination_string_list: "
  valid_cfg G
  \<Longrightarrow> length \<pi>s=length w
  \<Longrightarrow> \<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (w ! i))
  \<Longrightarrow> length \<pi>s = length ws1 \<and>
               (\<forall>k<length \<pi>s.
                   \<exists>d n e.
                      cfgLM.derivation G d \<and>
                      cfgLM.belongs G d \<and>
                      d 0 =
                      Some (pair None
                             \<lparr>cfg_conf = option_to_list (Some (w ! k))\<rparr>) \<and>
                      d n = Some (pair e \<lparr>cfg_conf = liftB (ws1 ! k)\<rparr>) \<and>
                      \<pi>s ! k = map the (get_labels d n))
  \<Longrightarrow> length \<pi>s = length ws2 \<and>
               (\<forall>k<length \<pi>s.
                   \<exists>d n e.
                      cfgLM.derivation G d \<and>
                      cfgLM.belongs G d \<and>
                      d 0 =
                      Some (pair None
                             \<lparr>cfg_conf = option_to_list (Some (w ! k))\<rparr>) \<and>
                      d n = Some (pair e \<lparr>cfg_conf = liftB (ws2 ! k)\<rparr>) \<and>
                      \<pi>s ! k = map the (get_labels d n))
  \<Longrightarrow> ws1 = ws2"
  apply(rule listEqI)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      \<pi>s="\<pi>s"
      and w="w"
      in uniqueness_of_elimination_string_list_hlp)
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
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma unique_existence_of_elimination_string_list: "
  valid_cfg G
  \<Longrightarrow> length \<pi>s=length w
  \<Longrightarrow> \<forall>i<length \<pi>s. \<pi>s ! i \<in> CFGlmEliminators G (Some (w ! i))
  \<Longrightarrow> \<exists>!ws. length \<pi>s = length ws \<and>
               (\<forall>k<length \<pi>s.
                   \<exists>d n e.
                      cfgLM.derivation G d \<and>
                      cfgLM.belongs G d \<and>
                      d 0 =
                      Some (pair None
                             \<lparr>cfg_conf = option_to_list (Some (w ! k))\<rparr>) \<and>
                      d n = Some (pair e \<lparr>cfg_conf = liftB (ws ! k)\<rparr>) \<and>
                      \<pi>s ! k = map the (get_labels d n))"
  apply(rule HOL.ex_ex1I)
   apply(rule existence_of_elimination_string_list)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac ws y)(*strict*)
  apply(rule uniqueness_of_elimination_string_list)
      apply(rename_tac ws y)(*strict*)
      apply(force)
     apply(rename_tac ws y)(*strict*)
     apply(force)
    apply(rename_tac ws y)(*strict*)
    apply(force)
   apply(rename_tac ws y)(*strict*)
   apply(force)
  apply(rename_tac ws y)(*strict*)
  apply(force)
  done

lemma CFGlm_unambiguous_coincide: "
  valid_cfg G
  \<Longrightarrow> CFGlm_unambiguous G
  \<Longrightarrow> cfgLM.derivation_initial G d1
  \<Longrightarrow> cfgLM.derivation_initial G d2
  \<Longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=liftB w\<rparr>)
  \<Longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=liftB w\<rparr>)
  \<Longrightarrow> n1=n2 \<and> d1 = d2"
  apply(subgoal_tac "d1=d2")
   prefer 2
   apply(simp add: CFGlm_unambiguous_def)
  apply(clarsimp)
  apply(case_tac "n1<n2")
   apply(subgoal_tac "n2-n1=0")
    apply(force)
   apply(rule cfgLM_no_step_without_nontermsX)
       apply(force)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(simp add: simpX)
   apply(force)
  apply(case_tac "n2<n1")
   apply(subgoal_tac "n1-n2=0")
    apply(force)
   apply(rule_tac
      d="d2"
      and n="n2"
      in cfgLM_no_step_without_nontermsX)
       apply(force)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(simp add: simpX)
   apply(force)
  apply(force)
  done

lemma equal_eliminators_hlp1: "
  valid_cfg G
  \<Longrightarrow> take i y1 = take i y2
  \<Longrightarrow> foldl (@) [] y1 = foldl (@) [] f\<pi>2
  \<Longrightarrow> foldl (@) [] y2 = foldl (@) [] f\<pi>2
  \<Longrightarrow> length y1 = length w
  \<Longrightarrow> length y2 = length w
  \<Longrightarrow> Suc i \<le> length w
  \<Longrightarrow> y1 ! i \<in> CFGlmEliminators G (Some (w ! i))
  \<Longrightarrow> y2 ! i \<in> CFGlmEliminators G (Some (w ! i))
  \<Longrightarrow> y1 ! i @ c = y2 ! i
  \<Longrightarrow> y1 ! i = y2 ! i"
  apply(simp add: CFGlmEliminators_def)
  apply(clarsimp)
  apply(rename_tac d da n na e wa ea waa)(*strict*)
  apply(subgoal_tac "n\<le>na")
   apply(rename_tac d da n na e wa ea waa)(*strict*)
   prefer 2
   apply (metis get_labels_length drop_length_append length_map)
  apply(rename_tac d da n na e wa ea waa)(*strict*)
  apply(subgoal_tac "da n = d n")
   apply(rename_tac d da n na e wa ea waa)(*strict*)
   apply(clarsimp)
   apply(case_tac c)
    apply(rename_tac d da n na e wa ea waa)(*strict*)
    apply(force)
   apply(rename_tac d da n na e wa ea waa a list)(*strict*)
   apply(clarsimp)
   apply(case_tac "n=na")
    apply(rename_tac d da n na e wa ea waa a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d da na e wa waa a list)(*strict*)
    apply (metis get_labels_length length_map self_append_conv takePrecise)
   apply(rename_tac d da n na e wa ea waa a list)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. da n = Some (pair e1 c1) \<and> da (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
    apply(rename_tac d da n na e wa ea waa a list)(*strict*)
    prefer 2
    apply(rule_tac
      m="na"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d da n na e wa ea waa a list)(*strict*)
      apply(force)
     apply(rename_tac d da n na e wa ea waa a list)(*strict*)
     apply(force)
    apply(rename_tac d da n na e wa ea waa a list)(*strict*)
    apply(force)
   apply(rename_tac d da n na e wa ea waa a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da n na e wa ea waa a list e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac d da n na e wa ea waa a list e2 c2 l r)(*strict*)
   apply (metis hlp2 liftB_reflects_length append_self_conv drop_length_append le_neq_implies_less list.simps(3) nth_append_length take_liftB take_append_prime)
  apply(rename_tac d da n na e wa ea waa)(*strict*)
  apply(rule_tac
      ?x2.0="0"
      and n="n"
      and ?x1.0="na-n"
      in equal_eliminators_hlp2)
         apply(rename_tac d da n na e wa ea waa)(*strict*)
         apply(force)
        apply(rename_tac d da n na e wa ea waa)(*strict*)
        apply(force)
       apply(rename_tac d da n na e wa ea waa)(*strict*)
       apply(force)
      apply(rename_tac d da n na e wa ea waa)(*strict*)
      apply(force)
     apply(rename_tac d da n na e wa ea waa)(*strict*)
     apply(force)
    apply(rename_tac d da n na e wa ea waa)(*strict*)
    apply(force)
   apply(rename_tac d da n na e wa ea waa)(*strict*)
   apply(simp add: get_labels_def)
   apply(clarsimp)
   apply(rename_tac d da n na e wa ea waa x)(*strict*)
   apply(subgoal_tac "Suc 0\<le>x \<and> x\<le>n")
    apply(rename_tac d da n na e wa ea waa x)(*strict*)
    prefer 2
    apply (metis less_eq_Suc_le_raw nat_seq_in_interval)
   apply(rename_tac d da n na e wa ea waa x)(*strict*)
   apply(clarsimp)
   apply(case_tac x)
    apply(rename_tac d da n na e wa ea waa x)(*strict*)
    apply(force)
   apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
   apply(subgoal_tac "the(get_label (da x)) = the(get_label (d x))")
    apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
    apply(subgoal_tac "\<exists>e c. da (Suc nat) = Some (pair (Some e) c)")
     apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
     prefer 2
     apply(rule_tac
      m="na"
      in cfgLM.pre_some_position_is_some_position_prime)
        apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
        apply(force)
       apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
       apply(force)
      apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
      apply(force)
     apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
     apply(force)
    apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d da n na e wa ea waa nat eb ca)(*strict*)
    apply(subgoal_tac "\<exists>e c. d (Suc nat) = Some (pair (Some e) c)")
     apply(rename_tac d da n na e wa ea waa nat eb ca)(*strict*)
     prefer 2
     apply(rule_tac
      m="n"
      in cfgLM.pre_some_position_is_some_position_prime)
        apply(rename_tac d da n na e wa ea waa nat eb ca)(*strict*)
        apply(force)
       apply(rename_tac d da n na e wa ea waa nat eb ca)(*strict*)
       apply(force)
      apply(rename_tac d da n na e wa ea waa nat eb ca)(*strict*)
      apply(force)
     apply(rename_tac d da n na e wa ea waa nat eb ca)(*strict*)
     apply(force)
    apply(rename_tac d da n na e wa ea waa nat eb ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac d da n na e wa ea waa nat eb ca ec caa)(*strict*)
    apply(simp add: get_label_def)
   apply(rename_tac d da n na e wa ea waa x nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d da n na e wa ea waa nat)(*strict*)
   apply(rule_tac
      t="the (get_label (da (Suc nat)))"
      and s="(map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) na))!nat"
      in ssubst)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    prefer 2
    apply(rule_tac
      t="the (get_label (d (Suc nat)))"
      and s="(map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n) @ c)! nat"
      in ssubst)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     prefer 2
     apply(rule sym)
     apply(rule_tac
      f="\<lambda>x. x! nat"
      in HOL.arg_cong)
     apply(force)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    apply(subgoal_tac "nat_seq (Suc 0) n ! nat = (SSn)+(SSi)" for SSn SSi)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac d da n na e wa ea waa nat)(*strict*)
      apply(force)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     apply(force)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    apply(rule_tac
      t="(map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n) @ c) ! nat"
      and s="(map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n)) ! nat"
      in ssubst)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     apply(rule nth_append_1)
     apply(clarsimp)
     apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
      apply(rename_tac d da n na e wa ea waa nat)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     apply(force)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (d i))) (nat_seq (Suc 0) n) ! nat"
      and s="((the \<circ> (\<lambda>i. get_label (d i)))) ((nat_seq (Suc 0) n) ! nat)"
      in ssubst)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     apply(rule nth_map)
     apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
      apply(rename_tac d da n na e wa ea waa nat)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     apply(force)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    apply(force)
   apply(rename_tac d da n na e wa ea waa nat)(*strict*)
   apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) na) ! nat"
      and s="((the \<circ> (\<lambda>i. get_label (da i)))) ((nat_seq (Suc 0) na) ! nat)"
      in ssubst)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    apply(rule nth_map)
    apply(subgoal_tac "length (nat_seq (Suc 0) na) = SSn + 1 - SSi" for SSn SSi)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    apply(force)
   apply(rename_tac d da n na e wa ea waa nat)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) na ! nat = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac d da n na e wa ea waa nat)(*strict*)
     apply(force)
    apply(rename_tac d da n na e wa ea waa nat)(*strict*)
    apply(force)
   apply(rename_tac d da n na e wa ea waa nat)(*strict*)
   apply(force)
  apply(rename_tac d da n na e wa ea waa)(*strict*)
  apply(force)
  done

lemma equal_eliminators_hlp0: "
  valid_cfg G
  \<Longrightarrow> foldl (@) [] y1 = foldl (@) [] f\<pi>2
  \<Longrightarrow> foldl (@) [] y2 = foldl (@) [] f\<pi>2
  \<Longrightarrow> length y1 = length w
  \<Longrightarrow> \<forall>i<length w.
           y1 ! i
           \<in> CFGlmEliminators G
              (Some (w ! i))
  \<Longrightarrow> length y2 = length w
  \<Longrightarrow> \<forall>i<length w.
           y2 ! i
           \<in> CFGlmEliminators G
              (Some (w ! i))
  \<Longrightarrow> i\<le>length w
  \<Longrightarrow> take i y1 = take i y2"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="take (Suc i) y1"
      and s="take i y1 @ [y1!i]"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply (metis less_eq_Suc_le take_n_vs_take_Suc_n)
  apply(rename_tac i)(*strict*)
  apply(rule_tac
      t="take (Suc i) y2"
      and s="take i y2 @ [y2!i]"
      in ssubst)
   apply(rename_tac i)(*strict*)
   apply (metis less_eq_Suc_le take_n_vs_take_Suc_n)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)+
  apply(clarsimp)
  apply(subgoal_tac "prefix ((foldl (@) [] (take i y1)) @ y1!i) ((foldl (@) [] (take i y2)) @ y2!i) \<or> prefix ((foldl (@) [] (take i y2)) @y2!i) ((foldl (@) [] (take i y1)) @ y1!i)")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(rule_tac
      b="(foldl (@) [] (drop (Suc i) y1))"
      and d="(foldl (@) [] (drop (Suc i) y2))"
      in mutual_prefix_prefix)
   apply(rule_tac
      t="(foldl (@) [] (take i y1) @ y1 ! i) @ foldl (@) [] (drop (Suc i) y1)"
      and s="foldl (@) [] y1"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply (metis Suc_le_lessD append_take_drop_id foldl_Cons foldl_append foldl_first Cons_nth_drop_Suc)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(foldl (@) [] (take i y2) @ y2 ! i) @ foldl (@) [] (drop (Suc i) y2)"
      and s="foldl (@) [] y2"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply (metis Suc_le_lessD append_take_drop_id foldl_Cons foldl_append foldl_first Cons_nth_drop_Suc)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(erule disjE)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac i c)(*strict*)
   apply(rule equal_eliminators_hlp1)
            apply(rename_tac i c)(*strict*)
            apply(force)
           apply(rename_tac i c)(*strict*)
           apply(force)
          apply(rename_tac i c)(*strict*)
          apply(force)
         apply(rename_tac i c)(*strict*)
         apply(force)
        apply(rename_tac i c)(*strict*)
        apply(force)
       apply(rename_tac i c)(*strict*)
       apply(force)
      apply(rename_tac i c)(*strict*)
      apply(force)
     apply(rename_tac i c)(*strict*)
     apply(force)
    apply(rename_tac i c)(*strict*)
    apply(force)
   apply(rename_tac i c)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(rule sym)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac i c)(*strict*)
  apply(rule equal_eliminators_hlp1)
           apply(rename_tac i c)(*strict*)
           apply(force)
          apply(rename_tac i c)(*strict*)
          apply(force)
         apply(rename_tac i c)(*strict*)
         apply(force)
        apply(rename_tac i c)(*strict*)
        apply(force)
       apply(rename_tac i c)(*strict*)
       apply(force)
      apply(rename_tac i c)(*strict*)
      apply(force)
     apply(rename_tac i c)(*strict*)
     apply(force)
    apply(rename_tac i c)(*strict*)
    apply(force)
   apply(rename_tac i c)(*strict*)
   apply(force)
  apply(rename_tac i c)(*strict*)
  apply(force)
  done

lemma equal_eliminators: "
  valid_cfg G
  \<Longrightarrow> foldl (@) [] y1 = foldl (@) [] f\<pi>2
  \<Longrightarrow> foldl (@) [] y2 = foldl (@) [] f\<pi>2
  \<Longrightarrow> length y1 = length w
  \<Longrightarrow> \<forall>i<length w.
           y1 ! i
           \<in> CFGlmEliminators G
              (Some (w ! i))
  \<Longrightarrow> length y2 = length w
  \<Longrightarrow> \<forall>i<length w.
           y2 ! i
           \<in> CFGlmEliminators G
              (Some (w ! i))
  \<Longrightarrow> y1 = y2"
  apply(subgoal_tac "take (length w) y1 = take (length w) y2")
   prefer 2
   apply(rule equal_eliminators_hlp0)
          apply(force)+
  done

lemma cfgLM_decompose_eliminating_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1@w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> \<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=[] \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n
  \<and> get_labels d n=get_labels d1 n1@ (get_labels d2 n2)"
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2. cfgLM.belongs G d \<and> cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>} \<and> maximum_of_domain d n \<longrightarrow> (\<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = [] \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n \<and> (get_labels d n)=(get_labels d1 n1)@(get_labels d2 n2))")
   apply(blast)
  apply(thin_tac "cfgLM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>}")
  apply(thin_tac "cfgLM.belongs G d")
  apply(thin_tac "maximum_of_domain d n")
  apply(rule allI)
  apply(rename_tac n)(*strict*)
  apply(induct_tac n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(subgoal_tac "n=0")
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d)(*strict*)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d)(*strict*)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d)(*strict*)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d)(*strict*)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(rule_tac
      x="0"
      in exI)
     apply(simp add: der1_def)
    apply(rename_tac d)(*strict*)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d)(*strict*)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d)(*strict*)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(rule cfgLM.der1_is_derivation)
    apply(rename_tac d)(*strict*)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(rule_tac
      x="0"
      in exI)
     apply(simp add: der1_def)
    apply(rename_tac d)(*strict*)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(rule der1_maximum_of_domain)
    apply(rename_tac d)(*strict*)
    apply(rule conjI)
     apply(rename_tac d)(*strict*)
     apply(rule der1_maximum_of_domain)
    apply(rename_tac d)(*strict*)
    apply(simp add: get_labels_def)
    apply(rule_tac
      t="nat_seq (Suc 0) 0"
      and s="[]"
      in ssubst)
     apply(rename_tac d)(*strict*)
     apply(rule nat_seqEmpty)
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule cfgLM.maximum_of_domainUnique)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(force)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac n na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2)(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 n xa)(*strict*)
  apply(subgoal_tac "n=Suc na")
   apply(rename_tac na d w1 w2 n xa)(*strict*)
   prefer 2
   apply(rule cfgLM.maximum_of_domainUnique)
     apply(rename_tac na d w1 w2 n xa)(*strict*)
     apply(force)
    apply(rename_tac na d w1 w2 n xa)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 n xa)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac na d w1 w2 n xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 xa)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac na d w1 w2 xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac na d w1 w2 xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 xa)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac na d w1 w2 xa)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc na"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac na d w1 w2 xa)(*strict*)
     apply(force)
    apply(rename_tac na d w1 w2 xa)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 xa)(*strict*)
   apply(force)
  apply(rename_tac na d w1 w2 xa)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 xa e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac na d w1 w2 xa e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 xa e2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac na d w1 w2 xa e2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac na d w1 w2 xa e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 xa e2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac l')
   apply(rename_tac na d w1 w2 xa e2 r l')(*strict*)
   prefer 2
   apply(rename_tac na d w1 w2 xa e2 r l' a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
    prefer 2
    apply(rule_tac
      P="G"
      and d="d"
      and i="Suc 0"
      and j="na"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
         apply(force)
        apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
        apply(force)
       apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
       apply(force)
      apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
      apply(force)
     apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
     apply(force)
    apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 xa e2 r a list)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(clarsimp)
   apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
   apply(subgoal_tac "maxTermPrefix (liftB []) = []")
    apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
    prefer 2
    apply (rule maxTermPrefix_term_string)
   apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "maxTermPrefix (teB a # liftB list @ prod_rhs e2 @ r) = a#maxTermPrefix (liftB list @ prod_rhs e2 @ r)")
    apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "a # maxTermPrefix (liftB list @ prod_rhs e2 @ r)=[]")
     apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
     apply(force)
    apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
    apply(clarsimp)
    apply(thin_tac "\<forall>d w1 w2. cfgLM.belongs G d \<and> cfgLM.derivation G d \<and> (case d 0 of None \<Rightarrow> False | Some x \<Rightarrow> x \<in> {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>}) \<and> cfgLM.derivation G d \<and> (\<exists>n. d (Suc n) = None \<and> (\<exists>y. (\<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>) \<and> d n = Some y)) \<and> maximum_of_domain d na \<longrightarrow> (\<exists>d1. cfgLM.derivation G d1 \<and> (case d1 0 of None \<Rightarrow> False | Some x \<Rightarrow> x \<in> {pair None \<lparr>cfg_conf = w1\<rparr>}) \<and> cfgLM.derivation G d1 \<and> (\<exists>n. d1 (Suc n) = None \<and> (\<exists>y. (\<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>) \<and> d1 n = Some y)) \<and> (\<exists>d2. cfgLM.derivation G d2 \<and> (case d2 0 of None \<Rightarrow> False | Some x \<Rightarrow> x \<in> {pair None \<lparr>cfg_conf = w2\<rparr>}) \<and> cfgLM.derivation G d2 \<and> (\<exists>n. d2 (Suc n) = None \<and> (\<exists>y. (\<exists>xa. y = pair xa \<lparr>cfg_conf = []\<rparr>) \<and> d2 n = Some y)) \<and> (\<exists>n1. maximum_of_domain d1 n1 \<and> (\<exists>n2. maximum_of_domain d2 n2 \<and> n1 + n2 = na \<and> get_labels d na = get_labels d1 n1 @ get_labels d2 n2))))")
    apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
    apply(thin_tac "maxTermPrefix (teB a # liftB list @ prod_rhs e2 @ r) = a # maxTermPrefix (liftB list @ prod_rhs e2 @ r)")
    apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
    apply(thin_tac "w1 @ w2 = teB a # liftB list @ teA (prod_lhs e2) # r")
    apply(thin_tac "cfgLM.belongs G d")
    apply(thin_tac "maximum_of_domain d (Suc na)")
    apply(thin_tac "cfgLM.derivation G d")
    apply(thin_tac "d (Suc (Suc na)) = None")
    apply(thin_tac "d (Suc na) = Some (pair xa \<lparr>cfg_conf = []\<rparr>)")
    apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = teB a # liftB list @ teA (prod_lhs e2) # r\<rparr>)")
    apply(thin_tac "d (Suc 0) = Some (pair (Some e2) \<lparr>cfg_conf = teB a # liftB list @ prod_rhs e2 @ r\<rparr>)")
    apply(thin_tac "e2 \<in> cfg_productions G")
    apply(thin_tac "valid_cfg G")
    apply(subgoal_tac "[a]@(maxTermPrefix (liftB list @ prod_rhs e2 @ r) @ w)=[]")
     apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
     apply(force)
    apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 r a list w)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 xa e2 r a list w)(*strict*)
   apply(rule maxTermPrefix_pull_out)
  apply(rename_tac na d w1 w2 xa e2 r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 xa e2 r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac na d w1 w2 xa e2 r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac na d w1 w2 xa e2 r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 xa r A w)(*strict*)
  apply(case_tac w1)
   apply(rename_tac na d w1 w2 xa r A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac na d xa r A w)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac na d xa r A w)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac na d xa r A w)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d xa r A w)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac na d xa r A w)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d xa r A w)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac na d xa r A w)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d xa r A w)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac na d xa r A w)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac na d xa r A w)(*strict*)
    apply(rule_tac
      x="Suc na"
      in exI)
    apply(clarsimp)
   apply(rename_tac na d xa r A w)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac na d xa r A w)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac na d xa r A w)(*strict*)
   apply(rule_tac
      x="Suc na"
      in exI)
   apply(clarsimp)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="nat_seq (Suc 0) 0"
      and s="[]"
      in ssubst)
    apply(rename_tac na d xa r A w)(*strict*)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac na d xa r A w)(*strict*)
   apply(force)
  apply(rename_tac na d w1 w2 xa r A w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w2 xa A w list)(*strict*)
  apply(rename_tac w1)
  apply(rename_tac na d w2 xa A w w1)(*strict*)
  apply(erule_tac
      x="derivation_drop d (Suc 0)"
      in allE)
  apply(erule_tac
      x="w@w1"
      in allE)
  apply(erule_tac
      x="w2"
      in allE)
  apply(erule impE)
   apply(rename_tac na d w2 xa A w w1)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w2 xa A w w1)(*strict*)
    apply(rule cfgLM.derivation_drop_preserves_belongs)
      apply(rename_tac na d w2 xa A w w1)(*strict*)
      apply(force)
     apply(rename_tac na d w2 xa A w w1)(*strict*)
     apply(force)
    apply(rename_tac na d w2 xa A w w1)(*strict*)
    apply(force)
   apply(rename_tac na d w2 xa A w w1)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w2 xa A w w1)(*strict*)
    apply(rule cfgLM.derivation_drop_preserves_derivation)
     apply(rename_tac na d w2 xa A w w1)(*strict*)
     apply(force)
    apply(rename_tac na d w2 xa A w w1)(*strict*)
    apply(force)
   apply(rename_tac na d w2 xa A w w1)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w2 xa A w w1)(*strict*)
    apply(simp add: derivation_drop_def)
   apply(rename_tac na d w2 xa A w w1)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w2 xa A w w1)(*strict*)
    apply(rule cfgLM.derivation_drop_preserves_derivation)
     apply(rename_tac na d w2 xa A w w1)(*strict*)
     apply(force)
    apply(rename_tac na d w2 xa A w w1)(*strict*)
    apply(force)
   apply(rename_tac na d w2 xa A w w1)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w2 xa A w w1)(*strict*)
    apply(rule_tac
      x="na"
      in exI)
    apply(simp add: derivation_drop_def)
    apply(clarsimp)
   apply(rename_tac na d w2 xa A w w1)(*strict*)
   apply(simp add: maximum_of_domain_def)
   apply(simp add: derivation_drop_def)
  apply(rename_tac na d w2 xa A w w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(case_tac "d1 0")
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(force)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(force)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA A]@w1\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w@w1\<rparr>) d1 (Suc 0)"
      in exI)
  apply(rule conjI)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="[]"
      in exI)
     apply(clarsimp)
    apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
    apply(force)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(rule conjI)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(rule conjI)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="[]"
      in exI)
     apply(clarsimp)
    apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
    apply(force)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(rule conjI)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(rule_tac
      x="Suc 0 + n"
      in exI)
   apply(rule conjI)
    apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(rule_tac
      x="nb"
      in exI)
   apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(rule_tac
      x="Suc 0+n"
      in exI)
  apply(rule conjI)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(simp add: maximum_of_domain_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(rule_tac
      x="nb"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "n2=nb")
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in cfgLM.maximum_of_domainUnique)
     apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
     apply(force)
    apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 n2 xab)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 xab)(*strict*)
  apply(subgoal_tac "n1=n")
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 xab)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgLM.maximum_of_domainUnique)
     apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 xab)(*strict*)
     apply(force)
    apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 xab)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 xab)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb n1 xab)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb xab)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = teA A # w1\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w @ w1\<rparr>) d1 (Suc 0)) (Suc n)"
      and s="x" for x
      in ssubst)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb xab)(*strict*)
   apply(rule get_labels_der2_decompose)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb xab)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="get_labels d (Suc (n + nb))"
      and s="Some SSe#get_labels (derivation_drop d (Suc 0)) ((n + nb))" for SSe
      in ssubst)
   apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb xab)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(force)
  apply(rename_tac d w2 xa A w w1 d1 n d2 xaa nb xab)(*strict*)
  apply(rule get_labels_derivation_drop_decompose)
  apply(force)
  done

lemma coinciding_derivation_parts_are_equal_up_to_unused_context: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d1
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> cfgLM.belongs G d1
  \<Longrightarrow> cfgLM.belongs G d2
  \<Longrightarrow> length v=m
  \<Longrightarrow> length v1=n1
  \<Longrightarrow> length v2=n2
  \<Longrightarrow> get_labels d1 (m+n1) = v@v1
  \<Longrightarrow> d1 (m+n1) \<noteq> None
  \<Longrightarrow> get_labels d2 (n2+m) = v2@v
  \<Longrightarrow> d2 (n2+m) \<noteq> None
  \<Longrightarrow> d1 0 = Some (pair None c1)
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ C\<rparr>)c1 = c2
  \<Longrightarrow> i\<le>m
  \<Longrightarrow> derivation_take (derivation_drop d2 n2) m i = derivation_take (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ C\<rparr>)) m i"
  apply(induct i)
   apply(clarsimp)
   apply(rename_tac y ya)(*strict*)
   apply(simp add: derivation_take_def derivation_drop_def derivation_map_def)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya)(*strict*)
  apply(simp add: derivation_take_def derivation_drop_def derivation_map_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="length v+length v1"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya)(*strict*)
     apply(force)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2a c1a c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2a c1a c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac i y ya e1 e2a c1a c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2a c1a l r)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac i y ya e1 e2a c1a l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2a l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac i y ya e1 e2a l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac i y ya e1 e2a l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2a r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e2a)
  apply(rename_tac i y ya e1 e2a r l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 r l' prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac i y ya e1 r l' A w)(*strict*)
  apply(case_tac "i+length v2")
   apply(rename_tac i y ya e1 r l' A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya r l' A w)(*strict*)
   apply(case_tac v)
    apply(rename_tac y ya r l' A w)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya r l' A w a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac y ya r l' A w a list)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(length list)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac y ya r l' A w a list)(*strict*)
      apply(force)
     apply(rename_tac y ya r l' A w a list)(*strict*)
     apply(force)
    apply(rename_tac y ya r l' A w a list)(*strict*)
    apply(force)
   apply(rename_tac y ya r l' A w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya r l' A w a list e2a c2)(*strict*)
   apply(case_tac e2a)
   apply(rename_tac y ya r l' A w a list e2a c2 prod_lhs prod_rhs)(*strict*)
   apply(rename_tac B w')
   apply(rename_tac y ya r l' A w a list e2a c2 B w')(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya r l' A w a list c2 B w')(*strict*)
   apply(case_tac c2)
   apply(rename_tac y ya r l' A w a list c2 B w' cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya r l' A w a list B w' cfg_confa)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac y ya r l' A w a list B w' l ra)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac y ya r l' A w a list B w' l ra)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply(force)
   apply(rename_tac y ya r l' A w a list B w' l ra)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya r l' A w a list B w' ra l'a)(*strict*)
   apply(thin_tac "setA (liftB l'a) = {}")
   apply(subgoal_tac "l'=l'a")
    apply(rename_tac y ya r l' A w a list B w' ra l'a)(*strict*)
    apply(clarsimp)
    apply(rename_tac y ya r w a list B w' l'a)(*strict*)
    apply(subgoal_tac "Some\<lparr>prod_lhs = B, prod_rhs = w\<rparr>=a")
     apply(rename_tac y ya r w a list B w' l'a)(*strict*)
     apply(subgoal_tac "Some\<lparr>prod_lhs = B, prod_rhs = w'\<rparr>=a")
      apply(rename_tac y ya r w a list B w' l'a)(*strict*)
      apply(force)
     apply(rename_tac y ya r w a list B w' l'a)(*strict*)
     prefer 2
     apply(rule_tac
      t="a"
      and s="(a # list @ v1)!0"
      in ssubst)
      apply(rename_tac y ya r w a list B w' l'a)(*strict*)
      apply(force)
     apply(rename_tac y ya r w a list B w' l'a)(*strict*)
     apply(rule_tac
      t="a # list @ v1"
      and s="get_labels d1 (Suc (length list + length v1))"
      in ssubst)
      apply(rename_tac y ya r w a list B w' l'a)(*strict*)
      apply(force)
     apply(rename_tac y ya r w a list B w' l'a)(*strict*)
     apply(thin_tac "get_labels d1 (Suc (length list + length v1)) = a # list @ v1")
     apply(subgoal_tac "length (nat_seq (Suc 0) (Suc (length list + length v1))) = SSn + 1 - Suc 0" for SSn)
      apply(rename_tac y ya r w a list B w' l'a)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac y ya r w a list B w' l'a)(*strict*)
     apply(simp add: get_labels_def)
     apply(clarsimp)
     apply(rename_tac y ya r w B w' l'a z zs)(*strict*)
     apply(rule_tac
      t="map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) (Suc (length zs + length v1))) ! 0"
      and s="(\<lambda>i. get_label (d1 i)) ((nat_seq (Suc 0) (Suc (length zs + length v1))) ! 0)"
      in ssubst)
      apply(rename_tac y ya r w B w' l'a z zs)(*strict*)
      apply(rule nth_map)
      apply(force)
     apply(rename_tac y ya r w B w' l'a z zs)(*strict*)
     apply(subgoal_tac "nat_seq (Suc 0) (Suc (length zs + length v1)) ! 0 = (SSn)+(SSi)" for SSn SSi)
      apply(rename_tac y ya r w B w' l'a z zs)(*strict*)
      prefer 2
      apply(rule nat_seq_nth_compute)
       apply(rename_tac y ya r w B w' l'a z zs)(*strict*)
       apply(force)
      apply(rename_tac y ya r w B w' l'a z zs)(*strict*)
      apply(force)
     apply(rename_tac y ya r w B w' l'a z zs)(*strict*)
     apply(clarsimp)
     apply(simp add: get_label_def)
    apply(rename_tac y ya r w a list B w' l'a)(*strict*)
    apply(rule_tac
      t="a"
      and s="(a # list)!0"
      in ssubst)
     apply(rename_tac y ya r w a list B w' l'a)(*strict*)
     apply(force)
    apply(rename_tac y ya r w a list B w' l'a)(*strict*)
    apply(rule_tac
      t="a # list"
      and s="get_labels d2 (Suc (length list))"
      in ssubst)
     apply(rename_tac y ya r w a list B w' l'a)(*strict*)
     apply(force)
    apply(rename_tac y ya r w a list B w' l'a)(*strict*)
    apply(thin_tac "get_labels d2 (Suc (length list)) = a # list")
    apply(subgoal_tac "length (nat_seq (Suc 0) (Suc (length list))) = SSn + 1 - Suc 0" for SSn)
     apply(rename_tac y ya r w a list B w' l'a)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac y ya r w a list B w' l'a)(*strict*)
    apply(simp add: get_labels_def)
    apply(clarsimp)
    apply(rename_tac y ya r w list B w' l'a z zs)(*strict*)
    apply(subgoal_tac "nat_seq (Suc 0) (Suc (length list)) ! 0 = (SSn)+(SSi)" for SSn SSi)
     apply(rename_tac y ya r w list B w' l'a z zs)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac y ya r w list B w' l'a z zs)(*strict*)
      apply(force)
     apply(rename_tac y ya r w list B w' l'a z zs)(*strict*)
     apply(force)
    apply(rename_tac y ya r w list B w' l'a z zs)(*strict*)
    apply(clarsimp)
    apply(simp add: get_label_def)
   apply(rename_tac y ya r l' A w a list B w' ra l'a)(*strict*)
   apply (metis identical_temrinal_maximal_prefix)
  apply(rename_tac i y ya e1 r l' A w nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (Suc nat) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya e1 r l' A w nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="length v2+length v"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i y ya e1 r l' A w nat)(*strict*)
     apply(force)
    apply(rename_tac i y ya e1 r l' A w nat)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 r l' A w nat)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 r l' A w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 r l' A w nat e1a e2a c1a c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i y ya e1 r l' A w nat e1a e2a c1a c2 l ra)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac i y ya e1 r l' A w nat e1a e2a c1a c2 l ra cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac i y ya e1 r l' A w nat e1a e2a c1a c2 l ra cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 r l' A w nat e1a e2a l ra)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac i y ya e1 r l' A w nat e1a e2a l ra prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 r l' A w nat e1a l ra prod_lhs prod_rhs)(*strict*)
  apply(rename_tac B w')
  apply(rename_tac i y ya e1 r l' A w nat e1a l ra B w')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac i y ya e1 r l' A w nat e1a l ra B w')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac i y ya e1 r l' A w nat e1a l ra B w')(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(subgoal_tac "Some \<lparr>prod_lhs = B, prod_rhs = w'\<rparr> = Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>")
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   prefer 2
   apply(rule_tac
      t="Some \<lparr>prod_lhs = B, prod_rhs = w'\<rparr>"
      and s="(get_labels d2 (length v2 + length v))!(Suc nat)"
      in ssubst)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(thin_tac "get_labels d2 (length v2 + length v) = v2 @ v")
    apply(simp add: get_labels_def)
    apply(subgoal_tac "length (nat_seq (Suc 0) ((length v2 + length v))) = SSn + 1 - Suc 0" for SSn)
     apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(rule_tac
      t="map (\<lambda>i. get_label (d2 i)) (nat_seq (Suc 0) (length v2 + length v)) ! Suc nat"
      and s="(\<lambda>i. get_label (d2 i)) ((nat_seq (Suc 0) (length v2 + length v)) ! Suc nat)"
      in ssubst)
     apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
     apply(rule nth_map)
     apply(force)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(simp add: get_label_def)
    apply(subgoal_tac "nat_seq (Suc 0) (length v2 + length v) ! Suc nat= (SSn)+(SSi)" for SSn SSi)
     apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
      apply(force)
     apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
     apply(force)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(rule_tac
      t="Suc nat"
      and s="length v2+i"
      in ssubst)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(rule_tac
      t="get_labels d2 (length v2 + length v)"
      and s="v2 @ v"
      in ssubst)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(rule_tac
      t="(v2 @ v) ! (length v2 + i)"
      and s="v ! i"
      in ssubst)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply (metis nth_shift2 add.commute)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(rule_tac
      t="v!i"
      and s="(v@v1)!i"
      in ssubst)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply (metis nth_append less_eq_Suc_le_raw)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(rule_tac
      t="v@v1"
      and s="get_labels d1 (length v + length v1)"
      in ssubst)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(thin_tac "get_labels d1 (length v + length v1) = v @ v1")
   apply(simp add: get_labels_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) ((length v + length v1))) = SSn + 1 - Suc 0" for SSn)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(rule_tac
      t="map (\<lambda>i. get_label (d1 i)) (nat_seq (Suc 0) (length v + length v1)) ! i"
      and s="(\<lambda>i. get_label (d1 i)) ((nat_seq (Suc 0) (length v + length v1)) ! i)"
      in ssubst)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(rule nth_map)
    apply(clarsimp)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(simp add: get_label_def)
   apply(subgoal_tac "nat_seq (Suc 0) (length v + length v1) ! i= (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
     apply(force)
    apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
   apply(clarsimp)
  apply(rename_tac i y ya e1 r l' A w nat e1a ra B w' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 r l' A w nat e1a ra l'a)(*strict*)
  apply(case_tac i)
   apply(rename_tac i y ya e1 r l' A w nat e1a ra l'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac y ya r l' A w nat ra l'a)(*strict*)
   apply(subgoal_tac "l'=l'a")
    apply(rename_tac y ya r l' A w nat ra l'a)(*strict*)
    apply(force)
   apply(rename_tac y ya r l' A w nat ra l'a)(*strict*)
   apply (metis identical_temrinal_maximal_prefix)
  apply(rename_tac i y ya e1 r l' A w nat e1a ra l'a nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya e1 r l' A w ra l'a nata)(*strict*)
  apply(subgoal_tac "l'=l'a")
   apply(rename_tac y ya e1 r l' A w ra l'a nata)(*strict*)
   apply(force)
  apply(rename_tac y ya e1 r l' A w ra l'a nata)(*strict*)
  apply (metis identical_temrinal_maximal_prefix)
  done

lemma coinciding_derivation_parts_are_equal_up_to_unused_context_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d1
  \<Longrightarrow> cfgLM.derivation G d2
  \<Longrightarrow> cfgLM.belongs G d1
  \<Longrightarrow> cfgLM.belongs G d2
  \<Longrightarrow> length v=m
  \<Longrightarrow> length v1=n1
  \<Longrightarrow> length v2=n2
  \<Longrightarrow> get_labels d1 (m+n1) = v@v1
  \<Longrightarrow> d1 (m+n1) \<noteq> None
  \<Longrightarrow> get_labels d2 (n2+m) = v2@v
  \<Longrightarrow> d2 (n2+m) \<noteq> None
  \<Longrightarrow> d1 0 = Some (pair None c1)
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ C\<rparr>)c1 = c2
  \<Longrightarrow> derivation_take (derivation_drop d2 n2) m = derivation_take (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ C\<rparr>)) m"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(case_tac "x\<le>m")
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      v="v"
      and ?v1.0="v1"
      and ?v2.0="v2"
      and G="G"
      and ?d1.0="d1"
      and ?d2.0="d2"
      in coinciding_derivation_parts_are_equal_up_to_unused_context)
                  apply(rename_tac x)(*strict*)
                  apply(force)
                 apply(rename_tac x)(*strict*)
                 apply(force)
                apply(rename_tac x)(*strict*)
                apply(force)
               apply(rename_tac x)(*strict*)
               apply(force)
              apply(rename_tac x)(*strict*)
              apply(force)
             apply(rename_tac x)(*strict*)
             apply(force)
            apply(rename_tac x)(*strict*)
            apply(force)
           apply(rename_tac x)(*strict*)
           apply(force)
          apply(rename_tac x)(*strict*)
          apply(force)
         apply(rename_tac x)(*strict*)
         apply(force)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def derivation_drop_def derivation_map_def)
  done

lemma sym_proof1: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.derivation G da
  \<Longrightarrow> map the (get_labels d (length (\<pi>s1 ! i))) = \<pi>s1 ! i
  \<Longrightarrow> map the (get_labels da (length (\<pi>s2 ! i))) = \<pi>s2 ! i
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = [teA (f ! i)]\<rparr>)
  \<Longrightarrow> d (length (\<pi>s1 ! i)) = Some (pair e \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> da 0 = Some (pair None \<lparr>cfg_conf = [teA (f ! i)]\<rparr>)
  \<Longrightarrow> da (length (\<pi>s2 ! i)) = Some (pair ea \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> length (nat_seq (Suc 0) (length (\<pi>s1 ! i))) = length (\<pi>s1 ! i)
  \<Longrightarrow> length (nat_seq (Suc 0) (length (\<pi>s2 ! i))) = length (\<pi>s2 ! i)
  \<Longrightarrow> strict_prefix (\<pi>s1 ! i) (\<pi>s2 ! i)
  \<Longrightarrow> False"
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(subgoal_tac "d (length (\<pi>s1 ! i)) = da (length (\<pi>s1 ! i))")
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. da ((length (\<pi>s1 ! i))) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac c)(*strict*)
    prefer 2
    apply(rule_tac
      m="(length (\<pi>s2 ! i))"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac c)(*strict*)
      apply(force)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(rule_tac
      t="\<pi>s2 ! i"
      and s="\<pi>s1 ! i @ c"
      in ssubst)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(simp (no_asm))
    apply(case_tac c)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c a list)(*strict*)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(clarsimp)
   apply(rename_tac c e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      n="(length (\<pi>s1 ! i))"
      and ?x1.0="0"
      and ?x2.0="(length (\<pi>s2 ! i))-(length (\<pi>s1 ! i))"
      and ?d1.0="d"
      and ?d2.0="da"
      and G="G"
      in equal_eliminators_hlp2)
         apply(rename_tac c)(*strict*)
         apply(force)
        apply(rename_tac c)(*strict*)
        apply(force)
       apply(rename_tac c)(*strict*)
       apply(force)
      apply(rename_tac c)(*strict*)
      apply(force)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(rule_tac
      t="length (\<pi>s1 ! i) + (length (\<pi>s2 ! i) - length (\<pi>s1 ! i))"
      and s="length(\<pi>s2!i)"
      in ssubst)
     apply(rename_tac c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(subgoal_tac "length (\<pi>s2 ! i)\<ge>length (\<pi>s1 ! i)")
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(rule_tac
      t="\<pi>s2 ! i"
      and s="\<pi>s1 ! i @ c"
      in ssubst)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c)(*strict*)
    apply(case_tac c)
     apply(rename_tac c)(*strict*)
     apply(force)
    apply(rename_tac c a list)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c)(*strict*)
  apply(rule listEqI)
   apply(rename_tac c)(*strict*)
   apply(simp add: get_labels_def)
  apply(rename_tac c ia)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "map the (get_labels d (length (\<pi>s1 ! i)))!ia=map the (get_labels da (length (\<pi>s1 ! i)))!ia")
   apply(rename_tac c ia)(*strict*)
   prefer 2
   apply(rule_tac
      t="map the (get_labels d (length (\<pi>s1 ! i)))"
      and s="\<pi>s1!i"
      in ssubst)
    apply(rename_tac c ia)(*strict*)
    apply(force)
   apply(rename_tac c ia)(*strict*)
   apply(rule_tac
      t="map the (get_labels da (length (\<pi>s1 ! i))) ! ia"
      and s="map the (get_labels da (length (\<pi>s2 ! i))) ! ia"
      in ssubst)
    apply(rename_tac c ia)(*strict*)
    apply(simp (no_asm) add: get_labels_def)
    apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) (length (\<pi>s1 ! i))) ! ia"
      and s="(the \<circ> (\<lambda>i. get_label (da i))) ((nat_seq (Suc 0) (length (\<pi>s1 ! i))) ! ia)"
      in ssubst)
     apply(rename_tac c ia)(*strict*)
     apply(rule nth_map)
     apply(subgoal_tac "length (nat_seq (Suc 0) (length (\<pi>s1 ! i))) = (length (\<pi>s1 ! i)) + 1 - Suc 0")
      apply(rename_tac c ia)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac c ia)(*strict*)
     apply(clarsimp)
     apply(simp add: get_labels_def)
    apply(rename_tac c ia)(*strict*)
    apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (da i))) (nat_seq (Suc 0) (length (\<pi>s2 ! i))) ! ia"
      and s="(the \<circ> (\<lambda>i. get_label (da i))) ((nat_seq (Suc 0) (length (\<pi>s2 ! i))) ! ia)"
      in ssubst)
     apply(rename_tac c ia)(*strict*)
     apply(rule nth_map)
     apply(subgoal_tac "length (nat_seq (Suc 0) (length (\<pi>s2 ! i))) = (length (\<pi>s2 ! i)) + 1 - Suc 0")
      apply(rename_tac c ia)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac c ia)(*strict*)
     apply(clarsimp)
     apply(simp add: get_labels_def)
     apply(rule_tac
      t="\<pi>s2 ! i"
      and s="\<pi>s1 ! i @ c"
      in ssubst)
      apply(rename_tac c ia)(*strict*)
      apply(force)
     apply(rename_tac c ia)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac c ia)(*strict*)
    apply(clarsimp)
    apply(simp add: get_label_def)
    apply(rule_tac
      t="nat_seq (Suc 0) (length (\<pi>s1 ! i)) ! ia"
      and s="Suc 0+ia"
      in ssubst)
     apply(rename_tac c ia)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac c ia)(*strict*)
      apply(simp add: get_labels_def)
     apply(rename_tac c ia)(*strict*)
     apply(simp add: get_labels_def)
    apply(rename_tac c ia)(*strict*)
    apply(rule_tac
      t="nat_seq (Suc 0) (length (\<pi>s2 ! i)) ! ia"
      and s="Suc 0+ia"
      in ssubst)
     apply(rename_tac c ia)(*strict*)
     apply(rule nat_seq_nth_compute)
      apply(rename_tac c ia)(*strict*)
      apply(simp add: get_labels_def)
      apply(rule_tac
      t="\<pi>s2 ! i"
      and s="\<pi>s1 ! i @ c"
      in ssubst)
       apply(rename_tac c ia)(*strict*)
       apply(force)
      apply(rename_tac c ia)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac c ia)(*strict*)
     apply(rule_tac
      t="\<pi>s2 ! i"
      and s="\<pi>s1 ! i @ c"
      in ssubst)
      apply(rename_tac c ia)(*strict*)
      apply(force)
     apply(rename_tac c ia)(*strict*)
     apply(simp (no_asm))
     apply(simp add: get_labels_def)
    apply(rename_tac c ia)(*strict*)
    apply(force)
   apply(rename_tac c ia)(*strict*)
   apply(rule_tac
      t="map the (get_labels da (length (\<pi>s2 ! i)))"
      and s="\<pi>s2!i"
      in ssubst)
    apply(rename_tac c ia)(*strict*)
    apply(force)
   apply(rename_tac c ia)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="\<pi>s1 ! i ! ia"
      and s="(\<pi>s1 ! i@c) ! ia"
      in ssubst)
    apply(rename_tac c ia)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c ia)(*strict*)
   apply (metis nth_append_1)
  apply(rename_tac c ia)(*strict*)
  apply(thin_tac "map the (get_labels d (length (\<pi>s1 ! i))) = \<pi>s1 ! i")
  apply(thin_tac "map the (get_labels da (length (\<pi>s2 ! i))) = \<pi>s2 ! i")
  apply(simp add: get_labels_def)
  apply(subgoal_tac "\<exists>e c. da (Suc ia) = Some (pair (Some e) c)")
   apply(rename_tac c ia)(*strict*)
   prefer 2
   apply(rule_tac
      m="(length (\<pi>s2 ! i))"
      in cfgLM.pre_some_position_is_some_position_prime)
      apply(rename_tac c ia)(*strict*)
      apply(force)
     apply(rename_tac c ia)(*strict*)
     apply(force)
    apply(rename_tac c ia)(*strict*)
    apply(rule_tac
      t="\<pi>s2 ! i"
      and s="\<pi>s1 ! i @ c"
      in ssubst)
     apply(rename_tac c ia)(*strict*)
     apply(force)
    apply(rename_tac c ia)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac c ia)(*strict*)
   apply(force)
  apply(rename_tac c ia)(*strict*)
  apply(clarsimp)
  apply(rename_tac c ia eb ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc ia) = Some (pair (Some e) c)")
   apply(rename_tac c ia eb ca)(*strict*)
   prefer 2
   apply(rule_tac
      m="(length (\<pi>s1 ! i))"
      in cfgLM.pre_some_position_is_some_position_prime)
      apply(rename_tac c ia eb ca)(*strict*)
      apply(force)
     apply(rename_tac c ia eb ca)(*strict*)
     apply(force)
    apply(rename_tac c ia eb ca)(*strict*)
    apply(force)
   apply(rename_tac c ia eb ca)(*strict*)
   apply(force)
  apply(rename_tac c ia eb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac c ia eb ca eaa cb)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (length (\<pi>s1 ! i)) ! ia = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac c ia eb ca eaa cb)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac c ia eb ca eaa cb)(*strict*)
    apply(force)
   apply(rename_tac c ia eb ca eaa cb)(*strict*)
   apply(force)
  apply(rename_tac c ia eb ca eaa cb)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  done

lemma cfgLM_trans_der_list_drop: "
        cfgLM.trans_der_list G ds
         (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) w) \<pi>s
         (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw)
       \<Longrightarrow> cfgLM.trans_der_list G
           (drop n ds)
           (map (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>) (drop n w))
           (drop n \<pi>s) (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) (drop n fw))"
  apply(simp add: cfgLM.trans_der_list_def)
  apply(clarsimp)
  done

lemma cfgLM_derivation_can_be_decomposed: "
  valid_cfg G
  \<Longrightarrow> cfgLM.derivation G d
  \<Longrightarrow> cfgLM.belongs G d
  \<Longrightarrow> d i = Some (pair ei \<lparr>cfg_conf=w1@w2\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair ej \<lparr>cfg_conf=liftB v\<rparr>)
  \<Longrightarrow> \<exists>v1 v2 d1 d2 e1 e2 n1 n2.
  v=v1@v2
  \<and> j=n1+n2
  \<and> cfgLM.derivation G d1
  \<and> cfgLM.derivation G d2
  \<and> cfgLM.belongs G d1
  \<and> cfgLM.belongs G d2
  \<and> (get_labels d1 n1)@(get_labels d2 n2)=drop i (get_labels d (i+j))
  \<and> d1 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>)
  \<and> d2 0 = Some (pair None \<lparr>cfg_conf=w2\<rparr>)
  \<and> d1 n1 = Some (pair e1 \<lparr>cfg_conf=liftB v1\<rparr>)
  \<and> d2 n2 = Some (pair e2 \<lparr>cfg_conf=liftB v2\<rparr>)"
  apply(induct j arbitrary: ej w1 w2 v i ei)
   apply(rename_tac ej w1 w2 v i ei)(*strict*)
   apply(clarsimp)
   apply(rename_tac ej w1 w2 v i)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = w1")
    apply(rename_tac ej w1 w2 v i)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB w1"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_liftB_substring liftB_commutes_over_concat)
   apply(rename_tac ej w1 w2 v i)(*strict*)
   apply(clarsimp)
   apply(rename_tac ej w2 v i l')(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = w2")
    apply(rename_tac ej w2 v i l')(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB w2"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_liftB setA_empty_from_greater_set set_append2)
   apply(rename_tac ej w2 v i l')(*strict*)
   apply(clarsimp)
   apply(rename_tac ej v i l' l'a)(*strict*)
   apply(subgoal_tac "l'@l'a=v")
    apply(rename_tac ej v i l' l'a)(*strict*)
    prefer 2
    apply(rule liftB_inj)
    apply(simp add: simpY)
   apply(rename_tac ej v i l' l'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(thin_tac "liftB l' @ liftB l'a = liftB (l' @ l'a)")
   apply(rule_tac
      x="l'"
      in exI)
   apply(rule_tac
      x="l'a"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB l'\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB l'a\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgLM.der1_is_derivation)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgLM.der1_belongs)
    apply(subgoal_tac "\<lparr>cfg_conf = liftB (l' @ l'a)\<rparr>\<in> cfg_configurations G")
     apply(rename_tac ej i l' l'a)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: simpY)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac ej i l' l'a)(*strict*)
     apply(force)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(force)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgLM.der1_belongs)
    apply(subgoal_tac "\<lparr>cfg_conf = liftB (l' @ l'a)\<rparr>\<in> cfg_configurations G")
     apply(rename_tac ej i l' l'a)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: simpY)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac ej i l' l'a)(*strict*)
     apply(force)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(force)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule_tac
      t="get_labels (der1 \<lparr>cfg_conf = liftB l'\<rparr>) 0"
      and s="[]"
      in ssubst)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply (metis get_labelsEmpty)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule_tac
      t="get_labels (der1 \<lparr>cfg_conf = liftB l'a\<rparr>) 0"
      and s="[]"
      in ssubst)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply (metis get_labelsEmpty)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(simp add: get_labels_def)
    apply(subgoal_tac "length (nat_seq (Suc 0) i) = SSn + 1 - SSi" for SSn SSi)
     apply(rename_tac ej i l' l'a)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac j ej w1 w2 v i ei)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac j ej w1 w2 v i ei)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+j)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac j ej w1 w2 v i ei)(*strict*)
     apply(force)
    apply(rename_tac j ej w1 w2 v i ei)(*strict*)
    apply(force)
   apply(rename_tac j ej w1 w2 v i ei)(*strict*)
   apply(force)
  apply(rename_tac j ej w1 w2 v i ei)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej w1 w2 v i ei e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac j ej w1 w2 v i ei e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac j ej w1 w2 v i ei e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej w1 w2 v i ei e2 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac j ej w1 w2 v i ei e2 l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A v)
  apply(rename_tac j ej w1 w2 va i ei e2 l r A v)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej w1 w2 va i ei l r A v)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac j ej w1 w2 va i ei l r A v)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac j ej w1 w2 va i ei l r A v)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(erule_tac
      x="ej"
      in meta_allE)
  apply(subgoal_tac "prefix l' va")
   apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and i="i"
      and j="Suc j"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
         apply(force)
        apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
        apply(force)
       apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
       apply(force)
      apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
      apply(force)
     apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
     apply(force)
    apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
    apply(force)
   apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
   apply(clarsimp)
   apply(rename_tac j ej w1 w2 va i ei r A v l' w)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(subgoal_tac "maxTermPrefix (liftB l' @ teA A # r)=l'")
    apply(rename_tac j ej w1 w2 va i ei r A v l' w)(*strict*)
    prefer 2
    apply(rule_tac
      t="maxTermPrefix (liftB l' @ teA A # r)"
      and s="maxTermPrefix (liftB l')"
      in ssubst)
     apply(rename_tac j ej w1 w2 va i ei r A v l' w)(*strict*)
     apply(rule maxTermPrefix_drop_tail)
    apply(rename_tac j ej w1 w2 va i ei r A v l' w)(*strict*)
    apply(rule maxTermPrefix_term_string)
   apply(rename_tac j ej w1 w2 va i ei r A v l' w)(*strict*)
   apply(subgoal_tac "maxTermPrefix (liftB va) = va")
    apply(rename_tac j ej w1 w2 va i ei r A v l' w)(*strict*)
    prefer 2
    apply(rule maxTermPrefix_term_string)
   apply(rename_tac j ej w1 w2 va i ei r A v l' w)(*strict*)
   apply(simp add: prefix_def)
   apply(rule_tac
      x="w"
      in exI)
   apply(force)
  apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
  apply(subgoal_tac "strict_prefix (liftB l') w1 \<or> SSX" for SSX)
   apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(rule sym)
   apply(force)
  apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
  apply(erule disjE)
   apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
   prefer 2
   apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac j ej w1 w2 i ei r A v l' c ca)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac j ej w1 w2 i ei r A v l' c ca)(*strict*)
    prefer 2
    apply(rule liftB_append)
    apply(force)
   apply(rename_tac j ej w1 w2 i ei r A v l' c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac j ej w2 i ei r A v c l1 l2)(*strict*)
   apply(thin_tac "liftB l1 @ liftB l2 = liftB (l1 @ l2)")
   apply(simp add: liftB_commutes_over_concat)
   apply(clarsimp)
   apply(rename_tac j ej i ei r A v c l1 l2)(*strict*)
   apply(rule_tac
      x="l1"
      in exI)
   apply(rule_tac
      x="l2@c"
      in exI)
   apply(clarsimp)
   apply(erule_tac
      x="liftB l1"
      in meta_allE)
   apply(erule_tac
      x="liftB l2@v@r"
      in meta_allE)
   apply(erule_tac
      x="l1 @ l2 @ c"
      in meta_allE)
   apply(erule_tac
      x="Suc i"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>"
      in meta_allE)
   apply(clarsimp)
   apply(simp add: liftB_commutes_over_concat)
   apply(clarsimp)
   apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule_tac
      x="d1"
      in exI)
   apply(clarsimp)
   apply(subgoal_tac "n1=0")
    apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    prefer 2
    apply(case_tac n1)
     apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
     apply(force)
    apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n1 n2 nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n2 nat)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
     apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n2 nat)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n2 nat)(*strict*)
       apply(force)
      apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n2 nat)(*strict*)
      apply(force)
     apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n2 nat)(*strict*)
     apply(force)
    apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n2 nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n2 nat e2a c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n2 nat e2a c2 l ra)(*strict*)
    apply (metis liftB_with_nonterminal_inside)
   apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(subgoal_tac "l1=v1")
    apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e2 n2)(*strict*)
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac ej i ei r A v c l1 l2 v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(clarsimp)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(simp add: liftB_commutes_over_concat)
   apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = liftB l2 @ teA A # r\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB l2 @ v @ r\<rparr> ) d2 (Suc 0)"
      in exI)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule_tac
      x="if n2=0 then Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr> else e2"
      in exI)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      x="Suc 0+n2"
      in exI)
   apply(rule conjI)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(force)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
      apply(rule cfgLM.der2_is_derivation)
      apply(simp add: cfgLM_step_relation_def)
      apply(rule_tac
      x="liftB l2"
      in exI)
      apply(clarsimp)
      apply(rule setA_liftB)
     apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
     apply(force)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(rule cfgLM.derivation_belongs)
       apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
       apply(force)
      apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
      apply(simp add: derivation_append_def der2_def)
     apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
     apply(subgoal_tac "\<lparr>cfg_conf = liftB v1 @ liftB l2 @ teA A # r\<rparr> \<in> cfg_configurations G")
      apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
      apply(simp add: cfg_configurations_def)
      apply(simp add: simpY)
     apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
     apply(rule cfgLM.belongs_configurations)
      apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
      apply(force)
     apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
     apply(force)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(force)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def der2_def)
    apply(clarsimp)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = liftB l2 @ teA A # r\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB l2 @ v @ r\<rparr>) d2 (Suc 0)) (Suc 0 + n2)"
      and s=" (get_labels (der2 \<lparr>cfg_conf = liftB l2 @ teA A # r\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB l2 @ v @ r\<rparr>) (Suc 0)) @(get_labels d2 n2)"
      in ssubst)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(rule cfgLM.get_labels_concat2)
        apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
        apply(force)
       apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
       apply(rule cfgLM.der2_is_derivation)
       apply(simp add: cfgLM_step_relation_def)
       apply(rule_tac
      x="liftB l2"
      in exI)
       apply(clarsimp)
       apply(rule setA_liftB)
      apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
      apply(force)
     apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(force)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(rule_tac
      t="get_labels (der2 \<lparr>cfg_conf = liftB l2 @ teA A # r\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB l2 @ v @ r\<rparr>) (Suc 0)"
      and s="[Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>]"
      in ssubst)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(rule der2_get_labels)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(subgoal_tac "get_labels d1 0 = []")
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    prefer 2
    apply (metis get_labelsEmpty)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(clarsimp)
   apply(thin_tac "get_labels d2 n2 = drop (Suc i) (get_labels d (Suc (i + n2)))")
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="drop i (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc (i + n2))))"
      and s=" (map (\<lambda>i. get_label (d i)) (drop i (nat_seq (Suc 0) (Suc (i + n2)))))"
      in ssubst)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(rule drop_map)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(rule_tac
      t=" drop (Suc i) (map (\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (Suc (i + n2))))) "
      and s="(map (\<lambda>i. get_label (d i)) (drop (Suc i) (nat_seq (Suc 0) (Suc (i + n2)))))"
      in ssubst)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(rule drop_map)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) (Suc (i + n2))) = SSn + 1 - SSi" for SSn SSi)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
   apply(rule listEqI)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(force)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2 ia)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc (i + n2)) ! (i + ia) = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2 ia)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2 ia)(*strict*)
     apply(force)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2 ia)(*strict*)
    apply(force)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2 ia)(*strict*)
   apply(clarsimp)
   apply(case_tac ia)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2 ia)(*strict*)
    apply(clarsimp)
    apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2)(*strict*)
    apply(simp add: get_label_def)
   apply(rename_tac ej i ei r A v c l2 v1 d1 d2 e2 n2 ia nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac j ej w1 w2 va i ei r A v l')(*strict*)
  apply(simp add: strict_prefix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac j ej w2 i ei r A v l' c ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac j ej w2 i ei r A v l' c ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac j ej w2 i ei r A v l' c ca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej w2 i ei A v l' c list)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  apply(erule_tac
      x="liftB l' @ v @ list"
      in meta_allE)
  apply(erule_tac
      x="w2"
      in meta_allE)
  apply(erule_tac
      x="l'@c"
      in meta_allE)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: liftB_commutes_over_concat)
  apply(erule_tac
      x="Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
  apply(subgoal_tac "prefix l' v1")
   apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and i="0"
      and j="n1"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
         apply(force)
        apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
        apply(force)
       apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
       apply(force)
      apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
      apply(force)
     apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
     apply(force)
    apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(force)
   apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(clarsimp)
   apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2 w)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(subgoal_tac "maxTermPrefix (liftB l' @ v @ list)=l'@maxTermPrefix (v @ list)")
    apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2 w)(*strict*)
    prefer 2
    apply (metis maxTermPrefix_shift)
   apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2 w)(*strict*)
   apply(subgoal_tac "maxTermPrefix (liftB v1) = v1")
    apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2 w)(*strict*)
    prefer 2
    apply(rule maxTermPrefix_term_string)
   apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2 w)(*strict*)
   apply(simp add: prefix_def)
   apply(rule_tac
      x="maxTermPrefix (v @ list) @ w"
      in exI)
   apply(force)
  apply(rename_tac ej w2 i ei A v l' c list v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  apply(rule_tac
      x="l'@ca"
      in exI)
  apply(rule_tac
      x="v2"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = liftB l' @ teA A # list\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB l' @ v @ list\<rparr> ) d1 (Suc 0)"
      in exI)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(rule_tac
      x="if n1=0 then Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr> else e1"
      in exI)
  apply(rule_tac
      x="e2"
      in exI)
  apply(rule_tac
      x="Suc 0+n1"
      in exI)
  apply(rule_tac
      x="n2"
      in exI)
  apply(rule conjI)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(force)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="liftB l'"
      in exI)
     apply(clarsimp)
     apply(rule setA_liftB)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    apply(force)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(force)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
      apply(force)
     apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    apply(subgoal_tac "\<lparr>cfg_conf = liftB l' @ teA A # list @ w2\<rparr> \<in> cfg_configurations G")
     apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: simpY)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
     apply(force)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    apply(force)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(force)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(force)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   prefer 2
   apply(rule conjI)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(simp add: derivation_append_def der2_def)
   apply(simp add: liftB_commutes_over_concat)
   apply(clarsimp)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = liftB l' @ teA A # list\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB l' @ v @ list\<rparr>) d1 (Suc 0)) (Suc 0 + n1)"
      in ssubst)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(rule cfgLM.get_labels_concat2)
       apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
       apply(force)
      apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
      apply(rule cfgLM.der2_is_derivation)
      apply(simp add: cfgLM_step_relation_def)
      apply(rule_tac
      x="liftB l'"
      in exI)
      apply(clarsimp)
      apply(rule setA_liftB)
     apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
     apply(force)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(force)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule_tac
      t="get_labels (der2 \<lparr>cfg_conf = liftB l' @ teA A # list\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = liftB l' @ v @ list\<rparr>) (Suc 0)"
      and s="[Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>]"
      in ssubst)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(rule der2_get_labels)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="drop i (get_labels d (Suc (i + (n1 + n2))))"
      and s=" [Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>]@(drop (Suc i) (get_labels d (Suc (i + (n1 + n2))))) "
      in ssubst)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(simp add: get_labels_def)
  apply(rule_tac
      t="drop i (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc (i + (n1 + n2)))))"
      in ssubst)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(rule drop_map)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule_tac
      t="drop (Suc i) (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc (i + (n1 + n2)))))"
      in ssubst)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(rule drop_map)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) (Suc (i + (n1 + n2)))) = SSn + 1 - SSi" for SSn SSi)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
  apply(rule listEqI)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca ia)(*strict*)
  apply(clarsimp)
  apply(case_tac ia)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca ia)(*strict*)
   apply(clarsimp)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc (i + (n1 + n2))) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
     apply(force)
    apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
    apply(force)
   apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
  apply(rename_tac ej w2 i ei A v l' list v2 d1 d2 e1 e2 n1 n2 ca ia nat)(*strict*)
  apply(clarsimp)
  done

end
