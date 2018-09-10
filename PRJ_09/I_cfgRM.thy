section {*I\_cfgRM*}
theory
  I_cfgRM

imports
  I_cfg_base

begin

definition cfgRM_step_relation :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> bool"
  where
    "cfgRM_step_relation M c1 p c2 \<equiv>
  p \<in> cfg_productions M
  \<and> (\<exists>l r.
	 cfg_conf c1 = l @ teA (prod_lhs p) # r
	 \<and> cfg_conf c2 = l @ prod_rhs p @ r
	 \<and> setA r = {})"

lemma cfgRM_inst_AX_step_relation_preserves_belongs: "
  (\<forall>M. valid_cfg M \<longrightarrow> (\<forall>c1 e c2. cfgRM_step_relation M c1 e c2 \<longrightarrow> c1 \<in> cfg_configurations M \<longrightarrow> e \<in> cfg_step_labels M \<and> c2 \<in> cfg_configurations M))"
  apply(rule allI)
  apply(rename_tac M)(*strict*)
  apply(rule impI)+
  apply(rule allI)+
  apply(rename_tac M c1 e c2)(*strict*)
  apply(rule impI)+
  apply(simp add: cfg_configurations_def cfgRM_step_relation_def cfg_step_labels_def)
  apply(case_tac c2)
  apply(rename_tac M c1 e c2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e l r)(*strict*)
  apply(simp only: setAConcat concat_asso setBConcat)
  apply(clarsimp)
  apply(simp add: valid_cfg_def)
  done

lemma cfgRM_step_relation_both_sides_context: "
  setA right = {}
  \<Longrightarrow> \<forall>a e b. cfgRM_step_relation G a e b \<longrightarrow> cfgRM_step_relation G \<lparr>cfg_conf = left @ cfg_conf a @ right\<rparr> e \<lparr>cfg_conf = left @ cfg_conf b @ right\<rparr>"
  apply(simp add: cfgRM_step_relation_def)
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

lemma CFGRM_alt_case: "
  cfgRM_step_relation G \<lparr>cfg_conf = w1 @ w2\<rparr> e \<lparr>cfg_conf = c\<rparr>
  \<Longrightarrow> \<not> (\<exists>c'. cfgRM_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = c)
  \<Longrightarrow> \<exists>c'. cfgRM_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = c"
  apply(clarsimp)
  apply(simp add: cfgRM_step_relation_def)
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
   apply(force)
  apply(rename_tac l r A w c)(*strict*)
  apply(case_tac c)
   apply(rename_tac l r A w c)(*strict*)
   apply(force)
  apply(rename_tac l r A w c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac l A w list)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac l A w list)(*strict*)
   apply(force)
  apply(rename_tac l A w list)(*strict*)
  apply(erule_tac
      x="l @ w @ list"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x = "l"
      in allE)
  apply(erule_tac
      x = "list"
      in allE)
  apply(clarsimp)
  apply(rename_tac list)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma CFGRM_no_step_without_nonterms: "
  setA (cfg_conf ca) = {}
  \<Longrightarrow> \<forall>e c'. \<not> cfgRM_step_relation G' ca e c'"
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e c' l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

lemma cfgRM_step_relation_contextOK1: "
  valid_cfg G
  \<Longrightarrow> \<forall>a e b. cfgRM_step_relation G a e b \<longrightarrow> cfgRM_step_relation G \<lparr>cfg_conf = w1 @ cfg_conf a\<rparr> e \<lparr>cfg_conf = w1 @ cfg_conf b\<rparr>"
  apply(simp add: cfgRM_step_relation_def)
  apply(auto)
  apply(rename_tac a e b l r)(*strict*)
  apply(rule_tac
      x="w1@l"
      in exI)
  apply(rule_tac
      x="r"
      in exI)
  apply(auto)
  done

interpretation "cfgRM" : loc_cfg_0
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgRM_step_relation"
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
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgRM_inst_AX_step_relation_preserves_belongs )
  done

lemma CFGRM_derivation_initial_pos0: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation_initial G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>)"
  apply(simp add: cfgRM.derivation_initial_def)
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

lemma CFGRM_derivationCanBeDecomposed2: "
  cfgRM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1@w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> \<exists>d1 d2 w1' w2' n1 n2. cfgRM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgRM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n"
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2 w'. cfgRM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>} \<and> maximum_of_domain d n \<longrightarrow> (\<exists>d1 d2 w1' w2' n1 n2. cfgRM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgRM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n)")
   apply(blast)
  apply(thin_tac "cfgRM.derivation_from_to G d {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w'\<rparr>}")
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
    apply(rule cfgRM.modifying_derivation_is_not_empty)
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
    apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(rule cfgRM.der1_is_derivation)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 n xa)(*strict*)
     apply(rule cfgRM.der1_is_derivation)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule_tac
      x="w2"
      in exI)
   apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac d w1 w2 n xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac d w1 w2 n xa)(*strict*)
    apply(rule cfgRM.der1_is_derivation)
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
   apply(rule cfgRM.derivation_from_starts_from)
   apply(rule cfgRM.from_to_is_from)
   apply(blast)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac na d w1 w2 w')(*strict*)
     apply(rule cfgRM.from_to_is_der)
     apply(blast)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2 w')(*strict*)
   apply(arith)
  apply(rename_tac na d w1 w2 w')(*strict*)
  apply(subgoal_tac "\<exists>e. d (Suc na) = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac na d w1 w2 w')(*strict*)
   prefer 2
   apply(rule cfgRM.reachesToAtMaxDom)
    apply(rename_tac na d w1 w2 w')(*strict*)
    apply(rule cfgRM.from_to_is_to)
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
  apply(case_tac "\<exists>c'. cfgRM_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv")
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>c'. cfgRM_step_relation G \<lparr>cfg_conf = w2\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> w1 @ c' = cv")
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    prefer 2
    apply(rule CFGRM_alt_case)
     apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
     apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_def)
     apply(clarsimp)
     apply(rename_tac na d w1 w2 w' e ea cv)(*strict*)
     apply(erule_tac
      x="Suc 0"
      in allE)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
    apply(force)
   apply(rename_tac na d w1 w2 w' e ea c cv)(*strict*)
   apply(thin_tac "\<not> (\<exists>c'. cfgRM_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = c'\<rparr> \<and> c' @ w2 = cv)")
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
      in cfgRM.derivation_drop_preserves_derivation_from_to2)
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
    apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
    apply(rule conjI)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
     apply(rule cfgRM.derivation_append_preserves_derivation)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgRM.der2_is_derivation)
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
     apply(rule cfgRM.derivation_append_preserves_derivation)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgRM.der2_is_derivation)
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
      in cfgRM.derivation_drop_preserves_derivation_from_to2)
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
      in cfgRM.concatIsFromTo)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
      apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
      apply(clarsimp)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgRM.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule conjI)
       apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
       apply(rule cfgRM.der2_is_derivation)
       apply(force)
      apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2 n xa na nb xaa xab)(*strict*)
      apply(rule_tac
      x="Suc 0"
      in exI)
      apply(simp add: der2_def)
     apply(rename_tac d w1 w2 e ea c' d1 d2 w1' w2' n1 n2)(*strict*)
     apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
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

lemma CFGRM_Nonblockingness_to_elimination: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.belongs G d
  \<Longrightarrow> cfgRM.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w1@w2@w3\<rparr>)
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> \<exists>d' n' w e. maximum_of_domain d' n' \<and> cfgRM.derivation G d' \<and> cfgRM.belongs G d' \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w2\<rparr>) \<and> d' n' = Some (pair e \<lparr>cfg_conf=w\<rparr>) \<and> setA w = {}"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   prefer 2
   apply(rule cfgRM.some_position_has_details_at_0)
   apply(force)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfgRM.Nonblockingness_branching_def)
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
   apply(rule cfgRM.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac c dc x)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>cfg_conf = w1 @ w2 @ w3\<rparr> \<in> cfg_configurations G")
   apply(rename_tac c dc x)(*strict*)
   prefer 2
   apply(simp add: cfgRM.belongs_def)
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
      in cfgRM.some_position_has_details_before_max_dom)
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
      in cfgRM.noDeadEndBeforeMaxDom)
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
   apply(simp add: cfgRM_step_relation_def)
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
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac c dc x i ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac c dc x i ea ca)(*strict*)
    apply(rule cfgRM.der1_belongs)
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
   apply(subgoal_tac "\<forall>e c'. \<not> cfgRM_step_relation G \<lparr>cfg_conf = w'\<rparr> e c'")
    apply(rename_tac c dc x i ea w' y a)(*strict*)
    prefer 2
    apply(rule CFGRM_no_step_without_nonterms)
    apply(force)
   apply(rename_tac c dc x i ea w' y a)(*strict*)
   apply(subgoal_tac "\<exists>e c. dc (Suc (i - n)) = Some (pair (Some e) c)")
    apply(rename_tac c dc x i ea w' y a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(i-n)"
      in cfgRM.pre_some_position_is_some_position_prime)
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
   apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = w'\<rparr> eaa ca")
    apply(rename_tac c dc x i ea w' y eaa ca)(*strict*)
    prefer 2
    apply(rule_tac
      d="dc"
      and n="(i-n)"
      in cfgRM.position_change_due_to_step_relation)
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
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgRM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgRM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2@w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=(i-n)")
   apply(rename_tac c dc x i ea w')(*strict*)
   prefer 2
   apply(rule_tac
      d="dc"
      in CFGRM_derivationCanBeDecomposed2)
    apply(rename_tac c dc x i ea w')(*strict*)
    apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
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
  apply(thin_tac "cfgRM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' w2' n1 n2)(*strict*)
  apply(rename_tac w' n1 n')
  apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgRM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgRM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=w' \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=n'")
   apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in CFGRM_derivationCanBeDecomposed2)
    apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
    apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
   apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
   apply(force)
  apply(rename_tac c dc x i ea d1 d2 w1' w' n1 n')(*strict*)
  apply(clarsimp)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(thin_tac "cfgRM.derivation_from_to G d2a {pair None \<lparr>cfg_conf = w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(thin_tac "cfgRM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2 @ w3\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'nonterminal @ w2'\<rparr>}")
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2)(*strict*)
  apply(rule_tac
      x="d1a"
      in exI)
  apply(rule_tac
      x="n1a"
      in exI)
  apply(clarsimp)
  apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
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
   apply(rule cfgRM.derivation_belongs)
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
      in cfgRM.maximum_of_domainUnique)
    apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
    apply(force)
   apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
   apply(force)
  apply(rename_tac c dc x i ea d1 d2 w1' n1 d1a d2a w1'nonterminal w2' n1a n2 na xa)(*strict*)
  apply(simp add: maximum_of_domain_def)
  done

lemma cfgRM_step_relation_contextOK2: "
  valid_cfg G
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> \<forall>a e b. cfgRM_step_relation G a e b \<longrightarrow> cfgRM_step_relation G \<lparr>cfg_conf = cfg_conf a @ w2\<rparr> e \<lparr>cfg_conf = cfg_conf b @ w2\<rparr>"
  apply(simp add: cfgRM_step_relation_def)
  apply(auto)
  apply(rename_tac a e b l r)(*strict*)
  apply(rule_tac
      x="l"
      in exI)
  apply(rule_tac
      x="r@w2"
      in exI)
  apply(auto)
  apply(rename_tac a e b l r x)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(clarsimp)
  done

lemma cfgRM_concatExtendIsFromToBoth: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>}
  \<Longrightarrow> cfgRM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>}
  \<Longrightarrow> setA w2' = {}
  \<Longrightarrow> maximum_of_domain d1 m1
  \<Longrightarrow> maximum_of_domain d2 m2
  \<Longrightarrow> cfgRM.derivation_from_to G (derivation_append (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = w1 @ (cfg_conf v)\<rparr>)) (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ w2'\<rparr>)) m2) {pair None \<lparr>cfg_conf = w1 @ w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1' @ w2'\<rparr>}"
  apply(subgoal_tac "\<exists>e1 e2. d1 0 =Some (pair None \<lparr>cfg_conf=w1\<rparr>) \<and> d1 m1 =Some (pair e1 \<lparr>cfg_conf=w1'\<rparr>) \<and> d2 0 =Some (pair None \<lparr>cfg_conf=w2\<rparr>) \<and> d2 m2 =Some (pair e2 \<lparr>cfg_conf=w2'\<rparr>)")
   prefer 2
   apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_to_def cfgRM.derivation_from_def)
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
      in cfgRM.maximum_of_domainUnique)
      apply(rename_tac n na xa xaa)(*strict*)
      apply(force)
     apply(rename_tac n na xa xaa)(*strict*)
     apply(force)
    apply(rename_tac n na xa xaa)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac n na xa xaa)(*strict*)
   apply(rule_tac
      d="d1"
      in cfgRM.maximum_of_domainUnique)
     apply(rename_tac n na xa xaa)(*strict*)
     apply(force)
    apply(rename_tac n na xa xaa)(*strict*)
    apply(force)
   apply(rename_tac n na xa xaa)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(subgoal_tac "cfgRM.derivation G (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ w2'\<rparr>))")
   prefer 2
   apply(rule cfgRM.derivation_map_preserves_derivation2)
    apply(rule cfgRM.from_to_is_der)
    apply(force)
   apply(rule cfgRM_step_relation_contextOK2)
    apply(clarsimp)
   apply(clarsimp)
  apply(subgoal_tac "cfgRM.derivation G (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = w1 @ cfg_conf v\<rparr>))")
   prefer 2
   apply(rule cfgRM.derivation_map_preserves_derivation2)
    apply(rule cfgRM.from_to_is_der)
    apply(force)
   apply(rule cfgRM_step_relation_contextOK1)
   apply(clarsimp)
  apply(rule_tac
      dJ="\<lparr>cfg_conf=w1@w2'\<rparr>"
      in cfgRM.concatIsFromTo)
     apply(simp add: cfgRM.derivation_from_to_def)
     apply(simp add: cfgRM.derivation_from_def)
     apply(simp add: cfgRM.derivation_to_def)
     apply(simp add: derivation_map_def)
     apply(rule_tac
      x="m2"
      in exI)
     apply(clarsimp)
     apply(rename_tac n na e1 xa xaa e2)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(simp add: cfgRM.derivation_from_to_def)
    apply(simp add: cfgRM.derivation_from_def)
    apply(simp add: cfgRM.derivation_to_def)
    apply(simp add: derivation_map_def)
    apply(rule_tac
      x="m1"
      in exI)
    apply(clarsimp)
    apply(rename_tac n na e1 xa xaa e2)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rule derivation_map_preserves_maximum_of_domain)
   apply(blast)
  apply(rule derivation_map_preserves_maximum_of_domain)
  apply(blast)
  done

lemma StepPreciseRM: "
  valid_cfg G
  \<Longrightarrow> setA w2={}
  \<Longrightarrow> cfgRM_step_relation G \<lparr>cfg_conf = w1 @ [teA A] @ w2 \<rparr> e \<lparr>cfg_conf = w1 @ w @ w2\<rparr>
  \<Longrightarrow> e=\<lparr>prod_lhs=A, prod_rhs=w\<rparr>"
  apply(simp add: cfgRM_step_relation_def)
  apply(auto)
  apply(rename_tac l r)(*strict*)
  apply(case_tac e)
  apply(rename_tac l r prod_lhsa prod_rhsa)(*strict*)
  apply(subgoal_tac "w2=r")
   apply(rename_tac l r prod_lhsa prod_rhsa)(*strict*)
   apply(auto)
  apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
  apply(rule terminalTailEquals1)
    apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
    apply(blast)
   apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
   apply(blast)
  apply(rename_tac l r prod_lhs prod_rhs)(*strict*)
  apply(clarsimp)
  apply(blast)
  done

definition Lemma6__2_Goal :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> (nat \<Rightarrow> (('nonterminal, 'event) cfg_step_label, ('nonterminal, 'event) cfg_configuration) derivation_configuration option)
  \<Rightarrow> nat
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> ('nonterminal, 'event) DT_two_elements list
  \<Rightarrow> 'nonterminal
  \<Rightarrow> bool"
  where
    "Lemma6__2_Goal G d n e \<gamma> \<eta> y \<delta> A \<equiv>
  \<exists>d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' d'' m A'.
  cfgRM.derivation G d'
  \<and> maximum_of_domain d' (Suc n')
  \<and> d' 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>)
  \<and> d' n' = Some (pair e1 \<lparr>cfg_conf=\<delta>' @ [teA A'] @ y'\<rparr> )
  \<and> d' (Suc n') = Some (pair (Some e2) \<lparr>cfg_conf = \<delta>' @ \<alpha>' @ \<beta>' @ y'\<rparr>)
  \<and> \<delta>' @ \<alpha>' = \<gamma>
  \<and> setA y'={}
  \<and> take (Suc 0) (List.rev \<alpha>') = take (Suc 0) (List.rev \<gamma>)
  \<and> cfgRM.derivation G d''
  \<and> maximum_of_domain d'' m
  \<and> d'' 0 = Some (pair None \<lparr>cfg_conf = \<beta>' @ y'\<rparr>)
  \<and> d'' m = Some (pair e3 \<lparr>cfg_conf = \<eta> @ y\<rparr> )
  \<and> (Suc n') + m = Suc n
  \<and> (\<forall>i. ((i \<le> Suc n') \<longrightarrow> get_label (d i) = get_label (d' i))
  \<and> ((i > Suc n') \<longrightarrow> get_label (d i) = get_label (d'' (i - Suc n'))))"

lemma Lemma6__2: "
  valid_cfg G
  \<Longrightarrow> setA y={}
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> maximum_of_domain d (Suc n)
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>)
  \<Longrightarrow> d (Suc n) = Some (pair (Some e) \<lparr>cfg_conf=\<gamma>@\<eta>@y\<rparr> )
  \<Longrightarrow> \<gamma>@\<eta>=\<delta>@[teA A]
  \<Longrightarrow> Lemma6__2_Goal G d n e \<gamma> \<eta> y \<delta> A"
  apply(unfold Lemma6__2_Goal_def)
  apply(subgoal_tac "\<forall>n d y e \<gamma> \<eta> \<delta> A. setA y={} \<and> cfgRM.derivation G d \<and> maximum_of_domain d (Suc n) \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>) \<and> d (Suc n) = Some (pair (Some e) \<lparr>cfg_conf=\<gamma>@\<eta>@y\<rparr> ) \<and> \<gamma>@\<eta>=\<delta>@[teA A] \<longrightarrow> (\<exists>d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' d'' m A'. cfgRM.derivation G d' \<and> maximum_of_domain d' (Suc n') \<and> d' 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>) \<and> d' n' = Some (pair e1 \<lparr>cfg_conf=\<delta>'@[teA A']@y'\<rparr> ) \<and> d' (Suc n') = Some (pair (Some e2) \<lparr>cfg_conf=\<delta>'@\<alpha>'@\<beta>'@y'\<rparr>) \<and> \<delta>'@\<alpha>'=\<gamma> \<and> setA y'={} \<and> take (Suc 0) (List.rev \<alpha>') = take (Suc 0) (List.rev \<gamma>) \<and> cfgRM.derivation G d'' \<and> maximum_of_domain d'' m \<and> d'' 0 = Some (pair None \<lparr>cfg_conf=\<beta>'@y'\<rparr>) \<and> d'' m = Some (pair e3 \<lparr>cfg_conf=\<eta>@y\<rparr> ) \<and> (Suc n')+m=Suc n \<and> (\<forall>i. ((i\<le>Suc n') \<longrightarrow> get_label (d i) = get_label (d' i)) \<and> ((i>Suc n') \<longrightarrow> get_label (d i) = get_label (d'' (i-Suc n')))))")
   apply(erule_tac
      x="n"
      in allE)
   apply(erule_tac
      x="d"
      in allE)
   apply(erule_tac
      x="y"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule_tac
      x="\<gamma>"
      in allE)
   apply(erule_tac
      x="\<eta>"
      in allE)
   apply(erule_tac
      x="\<delta>"
      in allE)
   apply(erule_tac
      x="A"
      in allE)
   apply(force)
  apply(thin_tac "setA y={}")
  apply(thin_tac "cfgRM.derivation G d")
  apply(thin_tac "maximum_of_domain d (Suc n)")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>)")
  apply(thin_tac "d (Suc n) = Some (pair (Some e) \<lparr>cfg_conf=\<gamma>@\<eta>@y\<rparr> )")
  apply(thin_tac "\<gamma>@\<eta>=\<delta>@[teA A]")
  apply(rule allI)
  apply(rename_tac n)(*strict*)
  apply(rule_tac
      n="n"
      in nat_less_induct)
  apply(rename_tac n na)(*strict*)
  apply(case_tac na)
   apply(rename_tac n na)(*strict*)
   apply(thin_tac "\<forall>m<na. \<forall>d y e \<gamma> \<eta> \<delta> A. setA y = {} \<and> cfgRM.derivation G d \<and> maximum_of_domain d (Suc m) \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>) \<and> d (Suc m) = Some (pair (Some e) \<lparr>cfg_conf = \<gamma> @ \<eta> @ y\<rparr>) \<and> \<gamma> @ \<eta> = \<delta> @ [teA A] \<longrightarrow> (\<exists>d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' d'' ma A'. cfgRM.derivation G d' \<and> maximum_of_domain d' (Suc n') \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>) \<and> d' n' = Some (pair e1 \<lparr>cfg_conf = \<delta>' @ [teA A'] @ y'\<rparr>) \<and> d' (Suc n') = Some (pair (Some e2) \<lparr>cfg_conf = \<delta>' @ \<alpha>' @ \<beta>' @ y'\<rparr>) \<and> \<delta>' @ \<alpha>' = \<gamma> \<and> setA y' = {} \<and> take (Suc 0) (List.rev \<alpha>') = take (Suc 0) (List.rev \<gamma>) \<and> cfgRM.derivation G d'' \<and> maximum_of_domain d'' ma \<and> d'' 0 = Some (pair None \<lparr>cfg_conf = \<beta>' @ y'\<rparr>) \<and> d'' ma = Some (pair e3 \<lparr>cfg_conf = \<eta> @ y\<rparr>) \<and> Suc n' + ma = Suc m \<and> (\<forall>i. (i \<le> Suc n' \<longrightarrow> get_label (d i) = get_label (d' i)) \<and> (Suc n' < i \<longrightarrow> get_label (d i) = get_label (d'' (i - Suc n')))))")
   apply(rename_tac n na)(*strict*)
   apply(rule allI)+
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule impI)
   apply(erule conjE)+
   apply(rule_tac
      x="der2 \<lparr>cfg_conf = [teA (cfg_initial G)] \<rparr> e \<lparr>cfg_conf = \<gamma> @ \<eta> @ y\<rparr>"
      in exI)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="\<gamma>"
      in exI)
   apply(rule_tac
      x="\<eta>@y"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = \<eta>@y\<rparr>"
      in exI)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      x="cfg_initial G"
      in exI)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(rule cfgRM.der2_is_derivation)
    apply(clarsimp)
    apply(rename_tac d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(rule cfgRM.position_change_due_to_step_relation)
      apply(rename_tac d y e \<gamma> \<eta> \<delta> A)(*strict*)
      apply(blast)
     apply(rename_tac d y e \<gamma> \<eta> \<delta> A)(*strict*)
     apply(blast)
    apply(rename_tac d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(blast)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(clarsimp)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(clarsimp)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(clarsimp)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(simp add: cfgRM.der1_is_derivation)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(clarsimp)
    apply(rename_tac d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule conjI)
    apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(clarsimp)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(rule allI)
   apply(rename_tac n na d y e \<gamma> \<eta> \<delta> A i)(*strict*)
   apply(clarsimp)
   apply(rename_tac d y e \<gamma> \<eta> \<delta> A i)(*strict*)
   apply(rule conjI)
    apply(rename_tac d y e \<gamma> \<eta> \<delta> A i)(*strict*)
    apply(clarsimp)
    apply(simp add: get_label_def)
    apply(case_tac i)
     apply(rename_tac d y e \<gamma> \<eta> \<delta> A i)(*strict*)
     apply(clarsimp)
     apply(rename_tac d y e \<gamma> \<eta> \<delta> A)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac d y e \<gamma> \<eta> \<delta> A i nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac d y e \<gamma> \<eta> \<delta> A i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(subgoal_tac "\<forall>m>Suc 0. d m = None")
    apply(rename_tac d y e \<gamma> \<eta> \<delta> A i)(*strict*)
    apply(clarsimp)
    apply(simp add: der1_def)
   apply(rename_tac d y e \<gamma> \<eta> \<delta> A i)(*strict*)
   apply(rule cfgRM.noSomeAfterMaxDom)
    apply(rename_tac d y e \<gamma> \<eta> \<delta> A i)(*strict*)
    apply(blast)
   apply(rename_tac d y e \<gamma> \<eta> \<delta> A i)(*strict*)
   apply(blast)
  apply(rename_tac n na nat)(*strict*)
  apply(rule allI)+
  apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A)(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(erule_tac
      x="nat"
      in allE)
  apply(erule impE)
   apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(arith)
  apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A)(*strict*)
  apply(erule_tac
      x="derivation_take d (Suc nat)"
      in allE)
  apply(subgoal_tac "\<exists>e c. d (Suc nat) = Some (pair (Some e) c)")
   apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A)(*strict*)
     apply(blast)
    apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A)(*strict*)
    apply(blast)
   apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A)(*strict*)
   apply(arith)
  apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A)(*strict*)
  apply(erule exE)+
  apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
  apply(subgoal_tac "cfgRM_step_relation G c e \<lparr>cfg_conf = \<gamma> @ \<eta> @ y\<rparr>")
   apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
   prefer 2
   apply(rule cfgRM.position_change_due_to_step_relation)
     apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
     apply(blast)
    apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
    apply(blast)
   apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
   apply(blast)
  apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
  apply(subgoal_tac "\<exists>\<delta>1 A1 y1. c=\<lparr>cfg_conf=\<delta>1@[teA A1]@y1\<rparr> \<and> setA y1={}")
   apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
   prefer 2
   apply(simp add: cfgRM_step_relation_def)
   apply(rename_tac na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat d y e \<gamma> \<eta> \<delta> A ea c l r)(*strict*)
   apply(case_tac c)
   apply(rename_tac nat d y e \<gamma> \<eta> \<delta> A ea c l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat d y e \<gamma> \<eta> \<delta> A ea l r)(*strict*)
   apply(case_tac e)
   apply(rename_tac nat d y e \<gamma> \<eta> \<delta> A ea l r prod_lhsa prod_rhsa)(*strict*)
   apply(rename_tac A1 w1)
   apply(rename_tac nat d y e \<gamma> \<eta> \<delta> A ea l r A1 w1)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea l r A1 w1)(*strict*)
   apply(rule_tac
      x="l"
      in exI)
   apply(rule_tac
      x="A1"
      in exI)
   apply(rule_tac
      x="r"
      in exI)
   apply(force)
  apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c)(*strict*)
  apply(erule exE)+
  apply(rename_tac n na nat d y e \<gamma> \<eta> \<delta> A ea c \<delta>1 A1 y1)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(rename_tac na nat d y e \<gamma> \<eta> \<delta> A ea c \<delta>1 A1 y1)(*strict*)
  apply(fold cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat d y e \<gamma> \<eta> \<delta> A ea \<delta>1 A1 y1 l r)(*strict*)
  apply(case_tac e)
  apply(rename_tac nat d y e \<gamma> \<eta> \<delta> A ea \<delta>1 A1 y1 l r prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 A1 y1 l r prod_lhs prod_rhs)(*strict*)
  apply(rename_tac \<delta>1 y1 A1 w1)
  apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1a A1a y1a \<delta>1 y1 A1 w1)(*strict*)
  apply(subgoal_tac "y1a=y1")
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1a A1a y1a \<delta>1 y1 A1 w1)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="y1a"
      and ?w2.0="y1"
      and A="A1a"
      and B="A1"
      and ?v1.0="\<delta>1a"
      and ?v2.0="\<delta>1"
      in terminalTailEquals1)
     apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1a A1a y1a \<delta>1 y1 A1 w1)(*strict*)
     apply(force)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1a A1a y1a \<delta>1 y1 A1 w1)(*strict*)
    apply(force)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1a A1a y1a \<delta>1 y1 A1 w1)(*strict*)
   apply(force)
  apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1a A1a y1a \<delta>1 y1 A1 w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
  apply(subgoal_tac "\<exists>x. y=x@y1 \<and> ((\<exists>\<alpha>'. \<alpha>'\<noteq>[] \<and> \<gamma>=\<delta>1@\<alpha>' \<and> w1=\<alpha>'@\<eta>@x)\<or>(\<exists>\<alpha>. \<delta>1=\<gamma>@\<alpha>))")
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
   prefer 2
   apply(thin_tac "\<forall>y e \<gamma> \<eta>. setA y = {} \<and> cfgRM.derivation G (derivation_take d (Suc nat)) \<and> maximum_of_domain (derivation_take d (Suc nat)) (Suc nat) \<and> derivation_take d (Suc nat) 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>) \<and> derivation_take d (Suc nat) (Suc nat) = Some (pair (Some e) \<lparr>cfg_conf = \<gamma> @ \<eta> @ y\<rparr>) \<and> (\<exists>\<delta> A. \<gamma> @ \<eta> = \<delta> @ [teA A]) \<longrightarrow> (\<exists>d'. cfgRM.derivation G d' \<and> (\<exists>n'. maximum_of_domain d' (Suc n') \<and> d' 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>) \<and> (\<exists>e1 e2 e3 \<delta>' \<alpha>' \<beta>' y'. (\<exists>A'. d' n' = Some (pair e1 \<lparr>cfg_conf = \<delta>' @ teA A' # y'\<rparr>)) \<and> d' (Suc n') = Some (pair (Some e2) \<lparr>cfg_conf = \<delta>' @ \<alpha>' @ \<beta>' @ y'\<rparr>) \<and> \<delta>' @ \<alpha>' = \<gamma> \<and> setA y' = {} \<and> take (Suc 0) (List.rev \<alpha>') = take (Suc 0) (List.rev \<gamma>) \<and> (\<exists>d''. cfgRM.derivation G d'' \<and> (\<exists>m. maximum_of_domain d'' m \<and> d'' 0 = Some (pair None \<lparr>cfg_conf = \<beta>' @ y'\<rparr>) \<and> d'' m = Some (pair e3 \<lparr>cfg_conf = \<eta> @ y\<rparr>) \<and> n' + m = nat \<and> (\<forall>i. (i \<le> Suc n' \<longrightarrow> get_label (derivation_take d (Suc nat) i) = get_label (d' i)) \<and> (Suc n' < i \<longrightarrow> get_label (derivation_take d (Suc nat) i) = get_label (d'' (i - Suc n')))))))))")
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
   apply(subgoal_tac "\<exists>x. y=x@y1")
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
    prefer 2
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
    apply(rule_tac
      ?w1.0="y1"
      and ?w2.0="y"
      and A="A"
      and ?v1.0="\<delta>"
      and ?v2.0="\<delta>1"
      and u="w1"
      in terminalTailEquals2)
      apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
      apply(blast)
     apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
     apply(blast)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
    apply(simp only: concat_asso)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
   apply(erule exE)+
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
   apply(subgoal_tac "\<gamma> \<sqsubseteq> \<delta>1 \<or> \<delta>1 \<sqsubseteq> \<gamma>")
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(blast)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
   apply(erule disjE)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
    prefer 2
    apply(case_tac "\<gamma>=\<delta>1")
     apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
     apply(rule disjI2)
     apply(rule_tac
      x="[]"
      in exI)
     apply(blast)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
    apply(rule disjI1)
    apply(simp add: prefix_def)
    apply(erule exE)+
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x c)(*strict*)
    apply(rule_tac
      x="c"
      in exI)
    apply(force)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
   apply(rule disjI2)
   apply(simp add: prefix_def)
   apply(erule exE)+
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x c)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(force)
  apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1)(*strict*)
  apply(erule exE)+
  apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
  apply(erule conjE)+
  apply(erule disjE)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
   apply(erule exE)+
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(erule conjE)+
   apply(rule_tac
      x="d"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(blast)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule_tac
      x="Suc nat"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(blast)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(blast)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule_tac
      x="Some ea"
      in exI)
   apply(rule_tac
      x="\<lparr>prod_lhs = A1, prod_rhs = w1\<rparr>"
      in exI)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule_tac
      x="\<delta>1"
      in exI)
   apply(rule_tac
      x="\<alpha>'"
      in exI)
   apply(rule_tac
      x="\<eta>@x"
      in exI)
   apply(rule_tac
      x="y1"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(rule_tac
      x="A1"
      in exI)
    apply(blast)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(simp only: concat_asso)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(blast)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(blast)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(clarsimp)
    apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>')(*strict*)
    apply(case_tac \<alpha>')
     apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>')(*strict*)
     apply(clarsimp)
    apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>' a list)(*strict*)
    apply(force)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = \<eta>@y\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(simp add: maximum_of_domain_def)
    apply(rule conjI)
     apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
     apply(simp only: concat_asso)
     apply(clarsimp)
     apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>')(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x \<alpha>')(*strict*)
   apply(clarsimp)
   apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>' i)(*strict*)
   apply(subgoal_tac "\<forall>m>Suc(Suc nat). d m = None")
    apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>' i)(*strict*)
    apply(clarsimp)
    apply(simp add: get_label_def der1_def)
   apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>' i)(*strict*)
   apply(rule cfgRM.noSomeAfterMaxDom)
    apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>' i)(*strict*)
    apply(blast)
   apply(rename_tac nat d \<eta> \<delta> A ea \<delta>1 y1 A1 x \<alpha>' i)(*strict*)
   apply(blast)
  apply(rename_tac nat d y \<gamma> \<eta> \<delta> A ea \<delta>1 y1 A1 w1 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
  apply(erule_tac
      x="y1"
      in allE)
  apply(erule_tac
      x="ea"
      in allE)
  apply(erule_tac
      x="\<gamma>"
      in allE)
  apply(erule_tac
      x="\<alpha>@[teA A1]"
      in allE)
  apply(erule impE)
   apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
    apply(force)
   apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
    apply(rule_tac cfgRM.derivation_take_preserves_derivation)
    apply(blast)
   apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
    apply(rule_tac
      m="Suc 0"
      in cfgRM.derivation_take_preserves_generates_maximum_of_domain)
     apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
     apply(blast)
    apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
   apply(rule_tac
      x="\<gamma>@\<alpha>"
      in exI)
   apply(rule_tac
      x="A1"
      in exI)
   apply(clarsimp)
  apply(rename_tac nat d \<gamma> \<eta> \<delta> A ea y1 A1 w1 x \<alpha>)(*strict*)
  apply(clarsimp)
    (*
  setA (x @ y1 @ y') = {}
  G:d:(nat+2)
    d 0 = \<Rightarrow> S
    d (nat+1) = ea \<Rightarrow> \<delta>' @ \<alpha>' @ \<alpha> @ teA A1 # y1
    d (nat+2) = A1\<rightarrow>w1 \<Rightarrow> \<delta>' @ \<alpha>' @ \<alpha> @ w1 @ y1
  \<delta>' @ \<alpha>' @ \<eta> = \<delta> @ [teA A]
  \<eta> @ x = \<alpha> @ w1
  G:d':(n'+1)
    d' 0 = \<Rightarrow> S
    d' n' = e1 \<Rightarrow> \<delta>' @ teA A' # y'
    d' (n'+1) = A'\<rightarrow>\<alpha>'\<beta>' \<Rightarrow> \<delta>' @ \<alpha>' @ \<beta>' @ y'
  Suc 0 \<le> length \<alpha>' \<or> \<delta>' = []
  G:d'':m
    d'' 0 = \<Rightarrow> \<beta>' @ y'
    d'' m = e3 \<Rightarrow> \<alpha> @ teA A1 # y1
*)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule_tac
      x="n'"
      in exI)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="e2"
      in exI)
  apply(rule_tac
      x="Some \<lparr>prod_lhs = A1, prod_rhs = w1\<rparr>"
      in exI)
  apply(rule_tac
      x="\<delta>'"
      in exI)
  apply(rule_tac
      x="\<alpha>'"
      in exI)
  apply(rule_tac
      x="\<beta>'"
      in exI)
  apply(rule_tac
      x="y'"
      in exI)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(rule_tac
      x="A'"
      in exI)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule_tac
      x="derivation_append d'' (der2 \<lparr>cfg_conf = \<alpha> @ teA A1 # y1\<rparr> \<lparr>prod_lhs = A1, prod_rhs = w1\<rparr> \<lparr>cfg_conf = \<alpha> @ w1 @ y1\<rparr>) m"
      in exI)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(rule cfgRM.derivation_concat2)
      apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
      apply(blast)
     apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
     apply(blast)
    apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(blast)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule_tac
      x="m+Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
    apply(blast)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(simp add: get_label_def derivation_append_def)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "i\<le>Suc(n'+m)")
    apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
   apply(clarsimp)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i>Suc(n'+m)")
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "m<i-Suc n'")
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def)
  apply(rule conjI)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
   apply(clarsimp)
   apply(case_tac i)
    apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
    apply(clarsimp)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m nat)(*strict*)
   apply(case_tac nat)
    apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m nata)(*strict*)
   apply(subgoal_tac "nata=n'+m")
    apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m nata)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
  apply(clarsimp)
  apply(case_tac "d i")
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i)(*strict*)
   apply(clarsimp)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i option b)(*strict*)
  apply(case_tac i)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m i option b nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
  apply(subgoal_tac "Suc nat>Suc (Suc (n'+m))")
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "False")
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
  apply(rule_tac
      m="Suc nat"
      and d="d"
      in cfgRM.no_some_beyond_maximum_of_domain)
     apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
     apply(force)
    apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
    apply(force)
   apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
   apply(force)
  apply(rename_tac d \<eta> \<delta> A ea y1 A1 w1 x \<alpha> d' n' e1 e2 e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m option b nat)(*strict*)
  apply(force)
  done

lemma cfgRM_earliest_word_generated_position: "
  cfgRM.derivation G d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=w@v\<rparr>)
  \<Longrightarrow> P = (\<lambda>c. \<exists>z. w@z=cfg_conf c)
  \<Longrightarrow> \<exists>k\<le>n. (\<forall>i<k. \<not> (case d i of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)) \<and>
                  (case d k of None \<Rightarrow> False | Some (pair e c) \<Rightarrow> P c)"
  apply(rule cfgRM.existence_of_earliest_satisfaction_point)
    apply(force)
   apply(force)
  apply(force)
  done

lemma CFGRM_Nonblockingness2: "
  valid_cfg G
  \<Longrightarrow> Nonblockingness2 (cfgRM.unmarked_language G) (cfgRM.marked_language G)"
  apply(simp add: Nonblockingness2_def)
  apply(simp add: cfgRM.marked_language_def cfgRM.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(simp add: cfg_marked_effect_def cfg_marking_condition_def cfg_initial_configurations_def cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea cb ia)(*strict*)
  apply(case_tac cb)
  apply(rename_tac x d c e i ca ea cb ia cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c e i ca ea ia cfg_confa)(*strict*)
  apply(simp add: cfgRM.derivation_initial_def)
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
      in cfgRM_earliest_word_generated_position)
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

lemma cfgRM_staysInSigma: "
  valid_cfg G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgRM_step_relation G \<lparr>cfg_conf=w\<rparr> e \<lparr>cfg_conf=w'\<rparr>
  \<Longrightarrow> e \<in> cfg_productions G
  \<Longrightarrow> setB w' \<subseteq> cfg_events G"
  apply(simp add: cfgRM_step_relation_def)
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

lemma cfgRM_CFGStepNonTermBehaviour: "
  cfgRM_step_relation G \<lparr>cfg_conf = w1\<rparr> \<lparr>prod_lhs=A, prod_rhs=w\<rparr> \<lparr>cfg_conf = w2\<rparr>
  \<Longrightarrow> setA w2 \<subseteq> setA w1 \<union> setA w"
  apply(simp add: cfgRM_step_relation_def)
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

lemma cfgRM_staysInAlpha2: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>)
  \<Longrightarrow> setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G"
  apply(subgoal_tac " \<forall>e2 w'. d (i+j)=Some (pair e2 \<lparr>cfg_conf=w'\<rparr>) \<longrightarrow> (setA w' \<subseteq> cfg_nonterminals G \<and> setB w' \<subseteq> cfg_events G) ")
   apply(clarsimp)
  apply(rule_tac
      m="i"
      and n="j"
      in cfgRM.property_preseved_under_steps_is_invariant2)
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
      in cfgRM.pre_some_position_is_some_position)
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
   apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = cw\<rparr> e \<lparr>cfg_conf = w'nonterminal\<rparr>")
    apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
    apply(rule conjI)
     apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
     prefer 2
     apply(rule_tac
      w="cw"
      and e="e"
      in cfgRM_staysInSigma)
        apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
        apply(blast)
       apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
       apply(blast)
      apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
      apply(blast)
     apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
    apply(rename_tac ia e2a w'nonterminal e ea c cw)(*strict*)
    prefer 2
    apply(rule cfgRM.position_change_due_to_step_relation)
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
    apply(rule cfgRM_CFGStepNonTermBehaviour)
    apply(blast)
   apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
   apply(clarsimp del: subsetI)
   apply(rule_tac
      a="Ax"
      in prod_rhs_in_nonterms)
    apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
    apply(blast)+
   apply(rename_tac ia w'nonterminal ea cw Ax wx)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
  apply(rename_tac ia e2a w'nonterminal)(*strict*)
  apply(case_tac e2a)
   apply(rename_tac ia e2a w'nonterminal)(*strict*)
   apply(clarsimp)
   apply(rename_tac ia w'nonterminal)(*strict*)
   apply(rule cfgRM.derivation_Always_PreEdge_prime)
    apply(rename_tac ia w'nonterminal)(*strict*)
    apply(blast)+
  done

lemma cfgRM_staysInSigma2: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=w\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair e2 \<lparr>cfg_conf=w'\<rparr>)
  \<Longrightarrow> setB w' \<subseteq> cfg_events G"
  apply(subgoal_tac "setB w' \<subseteq> cfg_events G \<and> setA w' \<subseteq> cfg_nonterminals G")
   apply(force)
  apply(rule cfgRM_staysInAlpha2)
       apply(force)+
  done

lemma cfgRM_inst_lang_sound: "
  (\<forall>M. valid_cfg M \<longrightarrow> cfgRM.unmarked_language M \<subseteq> cfg_effects M)"
  apply(simp add: cfg_effects_def cfgRM.unmarked_language_def cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac M x xa d e c i z)(*strict*)
  apply(simp add: cfgRM.derivation_initial_def)
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
      in cfgRM_staysInSigma2)
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

lemma cfgRM_inst_AX_marking_condition_implies_existence_of_effect: "
  \<forall>M. valid_cfg M \<longrightarrow> (\<forall>f. cfgRM.derivation_initial M f \<longrightarrow> cfg_marking_condition M f \<longrightarrow> cfg_marked_effect M f \<noteq> {})"
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

lemma cfgRM_inst_AX_string_state_increases: "
   \<forall>G. valid_cfg G \<longrightarrow>
        (\<forall>c1. c1 \<in> cfg_configurations G \<longrightarrow>
              (\<forall>e c2. cfgRM_step_relation G c1 e c2 \<longrightarrow>
                      (\<exists>w. cfg_get_history c1 @ w = cfg_get_history c2)))"
  apply(simp add: cfg_get_history_def maxTermPrefix_def cfgRM_step_relation_def)
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
        apply(rule conjI)
         apply(rename_tac M e r w1 w1a)(*strict*)
         apply(rule setA_liftB)
        apply(rename_tac M e r w1 w1a)(*strict*)
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

lemma cfgRM_inst_ATS_axioms: "
  ATS_Language_axioms valid_cfg cfg_initial_configurations
     cfgRM_step_relation cfg_effects cfg_marking_condition cfg_marked_effect
     cfg_unmarked_effect"
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: cfgBASE_inst_AX_effect_inclusion1 cfgRM_inst_AX_unmarked_effect_persists cfgRM_inst_lang_sound cfgRM_inst_AX_marking_condition_implies_existence_of_effect )
  done

lemma cfgRM_inst_ATS_String_State_Modification_axioms: "
  ATS_String_State_Modification_axioms valid_cfg cfg_configurations cfgRM_step_relation False cfg_get_history"
  apply(simp add: ATS_String_State_Modification_axioms_def)
  apply(rule cfgRM_inst_AX_string_state_increases)
  done

interpretation "cfgRM" : loc_cfg_1
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgRM_step_relation"
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
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgRM_inst_AX_step_relation_preserves_belongs )
  apply(simp add: cfgRM_inst_ATS_String_State_Modification_axioms cfgRM_inst_ATS_axioms )
  done

lemma cfgRM_inst_Nonblockingness2: "
  \<forall>M. valid_cfg M \<longrightarrow> Nonblockingness2 (cfgRM.unmarked_language M) (cfgRM.marked_language M)"
  apply(rule allI)
  apply(rename_tac M)(*strict*)
  apply(clarsimp)
  apply(rule CFGRM_Nonblockingness2)
  apply(force)
  done

lemma cfgRM_terminals_at_beginning_are_never_modified: "
  cfgRM.derivation G d
  \<Longrightarrow> maximum_of_domain d (m + n)
  \<Longrightarrow> d m = Some (pair e1 \<lparr>cfg_conf = (liftB b) @ w\<rparr>)
  \<Longrightarrow> m \<le> x
  \<Longrightarrow> x \<le> m + n
  \<Longrightarrow> \<exists>e w. d x = Some (pair e \<lparr>cfg_conf = (liftB b) @ w\<rparr>)"
  apply(rule cfgRM.property_preseved_under_steps_is_invariant2)
      apply(blast)+
  apply(auto)
  apply(rename_tac i e wa)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac i e wa)(*strict*)
   apply(clarsimp, case_tac c)
   apply(rename_tac i e wa ea c cfg_conf)(*strict*)
   apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = (liftB b) @ wa\<rparr> ea c")
    apply(rename_tac i e wa ea c cfg_conf)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
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
    apply(rule cfgRM.position_change_due_to_step_relation)
      apply(rename_tac i e wa ea cfg_conf)(*strict*)
      apply(blast)+
   apply(rename_tac i e wa)(*strict*)
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
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

lemma cfgRM_inst_Nonblockingness_branching_correspond1: "
  (\<forall>M. valid_cfg M \<longrightarrow> cfgRM.Nonblockingness_branching M \<longrightarrow> nonblockingness_language (cfgRM.unmarked_language M) (cfgRM.marked_language M))"
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: cfgRM.Nonblockingness_branching_def)
  apply(simp add: nonblockingness_language_def cfgRM.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac M xa d)(*strict*)
  apply(subgoal_tac "cfgRM.belongs M d")
   apply(rename_tac M xa d)(*strict*)
   prefer 2
   apply(rule cfgRM.derivation_initial_belongs)
    apply(rename_tac M xa d)(*strict*)
    apply(force)
   apply(rename_tac M xa d)(*strict*)
   apply(force)
  apply(rename_tac M xa d)(*strict*)
  apply(subgoal_tac "\<exists>v. v \<in> cfgRM.marked_language M \<and> (\<exists>c. xa @ c = v)")
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
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac M xa d e c i z)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
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
   apply(rule cfgRM.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac M xa d e c i z dc x)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac M xa d e c i z dc x ca)(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_at_0)
   apply(force)
  apply(rename_tac M xa d e c i z dc x ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
  apply(subgoal_tac "cfgRM.derivation M (derivation_append (derivation_take d i) dc i)")
   apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
   prefer 2
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule cfgRM.derivation_append_preserves_derivation)
     apply(rename_tac M xa d e c i z dc x ca cb)(*strict*)
     apply(rule cfgRM.derivation_take_preserves_derivation)
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
      in cfgRM.some_position_has_details_before_max_dom)
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
   apply(simp add: cfgRM.marked_language_def)
   apply(rule_tac
      x="derivation_append (derivation_take d i) dc i"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation_initial)
      apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
      apply(force)
     apply(rename_tac M xa d e c i z dc x ca cb ea w)(*strict*)
     apply(rule cfgRM.derivation_take_preserves_derivation_initial)
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
      in cfgRM.maximum_of_domainUnique)
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
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_append (derivation_take d i) dc i) ia = Some (pair e1 c1) \<and> (derivation_append (derivation_take d i) dc i) (Suc ia) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation M c1 e2 c2")
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc ia"
      in cfgRM.step_detail_before_some_position)
       apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
       apply(simp add: cfgRM.derivation_initial_def)
      apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
      apply(force)
     apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
     apply(force)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc y ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac M xa d e c i z dc x ca cb ea w ia eb cc ya e2 c2)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
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
   apply(rule cfgRM_terminals_at_beginning_are_never_modified)
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

lemma cfgRM_inst_lang_finite: "
  (\<forall>G. valid_cfg G \<longrightarrow> cfgRM.finite_marked_language G = cfgRM.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x)(*strict*)
   apply(simp add: cfgRM.marked_language_def cfgRM.finite_marked_language_def)
   apply(clarsimp)
   apply(rename_tac G x d xa)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgRM.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: cfgRM.marked_language_def cfgRM.finite_marked_language_def)
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
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G x d e c i)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
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
   apply(rule cfgRM.belongs_configurations)
    apply(rename_tac G x d e c i ea ca ia ib eb cb)(*strict*)
    apply(rule cfgRM.derivation_initial_belongs)
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

lemma cfgRM_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_cfg G \<longrightarrow> cfgRM.finite_unmarked_language G = cfgRM.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x)(*strict*)
   apply(simp add: cfgRM.unmarked_language_def cfgRM.finite_unmarked_language_def)
   apply(clarsimp)
   apply(rename_tac G x d xa)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgRM.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: cfgRM.unmarked_language_def cfgRM.finite_unmarked_language_def)
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
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G x d e c i z)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
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

lemma cfgRM_inst_accept: "
  (\<forall>G d. cfgRM.derivation_initial G d \<longrightarrow> cfg_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> cfg_marking_configuration G))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  done

lemma cfgRM_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_cfg
     cfg_initial_configurations cfgRM_step_relation cfg_marking_condition
     cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(rule conjI)
   apply (metis cfgRM_inst_lang_finite)
  apply (metis cfgRM_inst_AX_unmarked_language_finite)
  done

lemma cfgRM_inst_BF_Bra_OpLa_axioms: "
  BF_Bra_OpLa_axioms valid_cfg cfg_configurations
     cfg_initial_configurations cfg_step_labels cfgRM_step_relation
     cfg_marking_condition cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: BF_Bra_OpLa_axioms_def)
  apply (metis cfgRM_inst_Nonblockingness_branching_correspond1)
  done

lemma cfgRM_inst_AX_marked_configuration_effect_coincides_with_marked_effect: "
(\<forall>G. valid_cfg G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial cfg_initial_configurations
               cfgRM_step_relation G d \<longrightarrow>
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
   apply(rule cfgRM.belongs_configurations)
    apply(rename_tac G d x e c i)(*strict*)
    apply(rule cfgRM.derivation_initial_belongs)
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

lemma cfgRM_inst_AX_unmarked_configuration_effect_coincides_with_unmarked_effect: "
 (\<forall>G. valid_cfg G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial cfg_initial_configurations
               cfgRM_step_relation G d \<longrightarrow>
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

interpretation "cfgRM" : loc_cfg_2
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgRM_step_relation"
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
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgRM_inst_AX_step_relation_preserves_belongs )
  apply(simp add: cfgRM_inst_ATS_String_State_Modification_axioms cfgRM_inst_ATS_axioms )
  apply(simp add: cfgRM_inst_ATS_Language_by_Finite_Derivations_axioms cfgRM_inst_BF_Bra_OpLa_axioms )
  done

lemma cfgRM_inst_Nonblockingness_branching_correspond2d: "
  valid_cfg M
  \<Longrightarrow> cfgRM.is_forward_deterministic M
  \<Longrightarrow> nonblockingness_language (cfgRM.unmarked_language M) (cfgRM.marked_language M)
  \<Longrightarrow> cfgRM.Nonblockingness_branching M"
  apply(simp add: nonblockingness_language_def)
  apply(simp add: cfgRM.Nonblockingness_branching_def)
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
  apply(subgoal_tac "\<exists>v. (maxTermPrefix w)@v \<in> cfgRM.marked_language M")
   apply(rename_tac dh n e w)(*strict*)
   prefer 2
   apply(subgoal_tac "(maxTermPrefix w) \<in> (prefix_closure (cfgRM.marked_language M))")
    apply(rename_tac dh n e w)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(subgoal_tac "(maxTermPrefix w) \<in> cfgRM.unmarked_language M")
    apply(rename_tac dh n e w)(*strict*)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(simp add: cfgRM.unmarked_language_def)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac dh n e w)(*strict*)
    prefer 2
    apply(simp add: cfgRM.derivation_initial_def)
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
  apply(thin_tac "cfgRM.unmarked_language M \<subseteq> (prefix_closure (cfgRM.marked_language M))")
  apply(simp add: cfgRM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac dh n e w v d)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac dh n e w v d ea c i)(*strict*)
  apply(simp add: cfgRM.derivation_initial_def)
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
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh i = Some (pair e1 c1) \<and> dh (Suc i) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation M c1 e2 c2")
      apply(rename_tac dh n e w v d ea i)(*strict*)
      prefer 2
      apply(rule_tac
      m="n"
      in cfgRM.step_detail_before_some_position)
        apply(rename_tac dh n e w v d ea i)(*strict*)
        apply(simp add: cfgRM.derivation_initial_def)
       apply(rename_tac dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(clarsimp)
     apply(rename_tac dh n e w v d ea i e2 c2)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
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
      in cfgRM.is_forward_deterministic_derivations_coincide)
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
      in cfgRM.derivation_drop_preserves_derivation_prime)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac dh n e w v d ea i)(*strict*)
   prefer 2
   apply(rule_tac
      m="i"
      in cfgRM.pre_some_position_is_some_position)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(blast)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(blast)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w v d ea i)(*strict*)
   apply(rule_tac cfgRM.derivation_drop_preserves_belongs)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(rule cfgRM.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(rule_tac cfgRM.derivation_take_preserves_belongs)
    apply(rule cfgRM.derivation_initial_belongs)
     apply(rename_tac dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac dh n e w v d ea i)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def)
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
      in cfgRM.is_forward_deterministic_derivations_coincide)
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
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation M c1 e2 c2")
     apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
     prefer 2
     apply(rule_tac
      m="ia"
      in cfgRM.step_detail_before_some_position)
       apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
       apply(simp add: cfgRM.derivation_initial_def)
      apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
      apply(force)
     apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n e w v d ea i ia eb c e2 c2)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac dh n e w v d ea i ia eb c e2 c2 l r)(*strict*)
    apply(simp only: setAConcat concat_asso setBConcat)
    apply(force)
   apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d ia = Some (pair e1 c1) \<and> d (Suc ia) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation M c1 e2 c2")
    apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
    prefer 2
    apply(rule_tac
      m="i"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
      apply(simp add: cfgRM.derivation_initial_def)
     apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
    apply(force)
   apply(rename_tac dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n e w v d ea i ia eb c e2 c2)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
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

lemma cfgRM_inst_BF_Bra_DetR_LaOp_axioms: "
  BF_Bra_DetR_LaOp_axioms valid_cfg cfg_configurations
     cfg_initial_configurations cfg_step_labels cfgRM_step_relation
     cfg_marking_condition cfg_marked_effect cfg_unmarked_effect"
  apply(simp add: BF_Bra_DetR_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: nonblockingness_language_def)
  apply(simp add: cfgRM.Nonblockingness_branching_def)
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
  apply(subgoal_tac "\<exists>v. (maxTermPrefix w)@v \<in> cfgRM.marked_language M")
   apply(rename_tac M dh n e w)(*strict*)
   prefer 2
   apply(subgoal_tac "(maxTermPrefix w) \<in> (prefix_closure (cfgRM.marked_language M))")
    apply(rename_tac M dh n e w)(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac M dh n e w c)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w)(*strict*)
   apply(subgoal_tac "(maxTermPrefix w) \<in> cfgRM.unmarked_language M")
    apply(rename_tac M dh n e w)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w)(*strict*)
   apply(simp add: cfgRM.unmarked_language_def)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac M dh n e w)(*strict*)
    prefer 2
    apply(simp add: cfgRM.derivation_initial_def)
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
  apply(thin_tac " cfgRM.unmarked_language M \<subseteq> (prefix_closure (cfgRM.marked_language M))")
  apply(simp add: cfgRM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d)(*strict*)
  apply(simp add: cfg_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M dh n e w v d ea c i)(*strict*)
  apply(subgoal_tac "case dh 0 of None \<Rightarrow> False | Some (pair a b) \<Rightarrow> b \<in> cfg_initial_configurations M \<and> a = None")
   apply(rename_tac M dh n e w v d ea c i)(*strict*)
   prefer 2
   apply(simp add: cfgRM.derivation_initial_def)
  apply(rename_tac M dh n e w v d ea c i)(*strict*)
  apply(subgoal_tac "case_option False (case_derivation_configuration (\<lambda>a b. b \<in> cfg_initial_configurations M \<and> a = None)) (d 0)")
   apply(rename_tac M dh n e w v d ea c i)(*strict*)
   prefer 2
   apply(simp add: cfgRM.derivation_initial_def)
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
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh i = Some (pair e1 c1) \<and> dh (Suc i) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation M c1 e2 c2")
      apply(rename_tac M dh n e w v d ea i)(*strict*)
      prefer 2
      apply(rule_tac
      m="n"
      in cfgRM.step_detail_before_some_position)
        apply(rename_tac M dh n e w v d ea i)(*strict*)
        apply(simp add: cfgRM.derivation_initial_def)
       apply(rename_tac M dh n e w v d ea i)(*strict*)
       apply(force)
      apply(rename_tac M dh n e w v d ea i)(*strict*)
      apply(force)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(clarsimp)
     apply(rename_tac M dh n e w v d ea i e2 c2)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
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
      in cfgRM.is_forward_deterministic_accessible_derivations_coincide)
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
      in cfgRM.derivation_drop_preserves_derivation_prime)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   prefer 2
   apply(rule_tac
      m="i"
      in cfgRM.pre_some_position_is_some_position)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(blast)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(blast)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(force)
  apply(rename_tac M dh n e w v d ea i)(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e w v d ea i)(*strict*)
   apply(rule_tac cfgRM.derivation_drop_preserves_belongs)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(rule cfgRM.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(rule_tac cfgRM.derivation_take_preserves_belongs)
    apply(rule cfgRM.derivation_initial_belongs)
     apply(rename_tac M dh n e w v d ea i)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i)(*strict*)
    apply(simp add: cfgRM.derivation_initial_def)
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
      in cfgRM.is_forward_deterministic_accessible_derivations_coincide)
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
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation M c1 e2 c2")
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     prefer 2
     apply(rule_tac
      m="ia"
      in cfgRM.step_detail_before_some_position)
       apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
       apply(simp add: cfgRM.derivation_initial_def)
      apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
      apply(force)
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    apply(clarsimp)
    apply(rename_tac M dh n e w v d ea i ia eb c e2 c2)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac M dh n e w v d ea i ia eb c e2 c2 l r)(*strict*)
    apply(simp only: setAConcat concat_asso setBConcat)
    apply(force)
   apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d ia = Some (pair e1 c1) \<and> d (Suc ia) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation M c1 e2 c2")
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    prefer 2
    apply(rule_tac
      m="i"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
      apply(simp add: cfgRM.derivation_initial_def)
     apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
     apply(force)
    apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
    apply(force)
   apply(rename_tac M dh n e w v d ea i ia eb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e w v d ea i ia eb c e2 c2)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
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

interpretation "cfgRM" : loc_cfg_3
  (* TSstructure *)
  "valid_cfg"
  (* configurations *)
  "cfg_configurations"
  (* initial_configurations *)
  "cfg_initial_configurations"
  (* step_labels *)
  "cfg_step_labels"
  (* step_relation *)
  "cfgRM_step_relation"
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
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgRM_inst_AX_step_relation_preserves_belongs cfgRM_inst_ATS_String_State_Modification_axioms cfgRM_inst_ATS_axioms cfgRM_inst_ATS_Language_by_Finite_Derivations_axioms cfgRM_inst_BF_Bra_OpLa_axioms cfgRM_inst_BF_Bra_DetR_LaOp_axioms )
  done

lemma CFGRM0_is_forward_target_deterministic: "
  valid_cfg M
  \<Longrightarrow> cfgRM.is_forward_target_deterministic M"
  apply(simp add: cfgRM.is_forward_target_deterministic_def)
  apply(simp add: cfgRM_step_relation_def)
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
  apply(subgoal_tac "r=ra")
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
  apply(rule terminalTailEquals1)
    apply(rename_tac l r la ra w v)(*strict*)
    apply(force)
   apply(rename_tac l r la ra w v)(*strict*)
   apply(force)
  apply(rename_tac l r la ra w v)(*strict*)
  apply(force)
  done

lemma CFGRM_Nonblockingness_is_lang_notempty: "
  valid_cfg G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> cfgRM.marked_language G \<noteq> {}"
  apply(simp add: cfgRM.marked_language_def cfgRM.Nonblockingness_branching_def)
  apply(erule_tac
      x="der1 \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>"
      in allE)
  apply(erule impE)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule conjI)
    apply(simp add: cfgRM.der1_is_derivation)
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
   apply(rule cfgRM.derivation_append_preserves_derivation)
     apply(rename_tac dc n' i e x)(*strict*)
     apply(rule cfgRM.der1_is_derivation)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(force)
   apply(rename_tac dc n' i e x)(*strict*)
   apply(simp add: der1_def)
   apply(case_tac "dc 0")
    apply(rename_tac dc n' i e x)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgRM.derivation_def)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
   apply(rename_tac dc n' i e x a)(*strict*)
   apply(case_tac "dc 0")
    apply(rename_tac dc n' i e x a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dc n' i e x a aa)(*strict*)
   apply(simp add: cfgRM.derivation_def)
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
   apply(simp add: cfgRM.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation)
      apply(rename_tac dc n' i e x)(*strict*)
      apply(rule cfgRM.der1_is_derivation)
     apply(rename_tac dc n' i e x)(*strict*)
     apply(force)
    apply(rename_tac dc n' i e x)(*strict*)
    apply(simp add: der1_def)
    apply(case_tac "dc 0")
     apply(rename_tac dc n' i e x)(*strict*)
     apply(clarsimp)
     apply(simp add: cfgRM.derivation_def)
     apply(erule_tac
      x="0"
      in allE)
     apply(clarsimp)
    apply(rename_tac dc n' i e x a)(*strict*)
    apply(case_tac "dc 0")
     apply(rename_tac dc n' i e x a)(*strict*)
     apply(clarsimp)
    apply(rename_tac dc n' i e x a aa)(*strict*)
    apply(simp add: cfgRM.derivation_def)
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

lemma cfgRM_no_step_without_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac option b)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac option b)(*strict*)
     apply(force)
    apply(rename_tac option b)(*strict*)
    apply(force)
   apply(rename_tac option b)(*strict*)
   apply(force)
  apply(rename_tac option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b e2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac b e2 l r)(*strict*)
  apply(simp only: setAConcat concat_asso)
  apply(force)
  done

interpretation "cfgRM_cfgRM_ATS_Bisimulation_Configuration_Weak" : ATS_Bisimulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_cfg"
  (* configurations1 *)
  "cfg_configurations"
  (* initial_configurations1 *)
  "cfg_initial_configurations"
  (* step_labels1 *)
  "cfg_step_labels"
  (* step_relation1 *)
  "cfgRM_step_relation"
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
  "cfgRM_step_relation"
  (* effects2 *)
  "cfg_effects"
  (* marking_condition2 *)
  "cfg_marking_condition"
  (* marked_effect2 *)
  "cfg_marked_effect"
  (* unmarked_effect2 *)
  "cfg_unmarked_effect"
  apply(simp add: LOCALE_DEFS_ALL LOCALE_DEFS_cfg ATS_Bisimulation_Configuration_Weak_def)
  apply(simp add: cfgBASE_inst_AX_initial_configuration_belongs cfgRM_inst_AX_step_relation_preserves_belongs cfgRM_inst_ATS_String_State_Modification_axioms cfgRM_inst_ATS_axioms )
  done

lemma CFGRM_terminals_stay_at_end: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> setA w = {}
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=v@w\<rparr>)
  \<Longrightarrow> d j = Some (pair e2 \<lparr>cfg_conf=x\<rparr>)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> suffix x w"
  apply(induct "j-i" arbitrary: j e2 x)
   apply(rename_tac j e2 x)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
  apply(rename_tac xa j e2 x)(*strict*)
  apply(clarsimp)
  apply(case_tac j)
   apply(rename_tac xa j e2 x)(*strict*)
   apply(force)
  apply(rename_tac xa j e2 x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e2 x nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac xa e2 x nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac xa e2 x nat)(*strict*)
     apply(force)
    apply(rename_tac xa e2 x nat)(*strict*)
    apply(force)
   apply(rename_tac xa e2 x nat)(*strict*)
   apply(force)
  apply(rename_tac xa e2 x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(erule_tac
      x="cfg_conf c1"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac xa x nat e1a e2a c1)(*strict*)
   apply(force)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa x nat e1a e2a c1)(*strict*)
   apply(force)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac xa x nat e1a e2a c1 c)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa nat e1a e2a c1 c l r)(*strict*)
  apply(case_tac "e2a")
  apply(rename_tac xa nat e1a e2a c1 c l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w1)
  apply(rename_tac xa nat e1a e2a c1 c l r A w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa nat e1a c1 c l r A w1)(*strict*)
  apply(subgoal_tac "suffix r w")
   apply(rename_tac xa nat e1a c1 c l r A w1)(*strict*)
   prefer 2
   apply(rule_tac
      l="[]"
      and v="c"
      and A="A"
      and w="l"
      in suffix_tails_terminal)
     apply(rename_tac xa nat e1a c1 c l r A w1)(*strict*)
     apply(force)
    apply(rename_tac xa nat e1a c1 c l r A w1)(*strict*)
    apply(force)
   apply(rename_tac xa nat e1a c1 c l r A w1)(*strict*)
   apply(force)
  apply(rename_tac xa nat e1a c1 c l r A w1)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  done

lemma cfgRM_derivation_map_preserves_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.derivation G (derivation_map d (\<lambda>v. \<lparr>cfg_conf = w1 @ (cfg_conf v)\<rparr>))"
  apply(simp (no_asm) add: cfgRM.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
   apply(simp add: cfgRM.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac i nat)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac i nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac i nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac i nat a)(*strict*)
     apply(force)
    apply(rename_tac i nat a)(*strict*)
    apply(force)
   apply(rename_tac i nat a)(*strict*)
   apply(force)
  apply(rename_tac i nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
  apply(rule_tac
      x="w1@l"
      in exI)
  apply(rule_tac
      x="r"
      in exI)
  apply(clarsimp)
  done

lemma cfgRM_derivation_map_preserves_belongs: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.belongs G d
  \<Longrightarrow> setA w1 \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w1 \<subseteq> cfg_events G
  \<Longrightarrow> cfgRM.belongs G (derivation_map d (\<lambda>v. \<lparr>cfg_conf = w1 @ cfg_conf v\<rparr>))"
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(rule_tac
      ca="\<lparr>cfg_conf = w1 @ cfg_conf c\<rparr>"
      in cfgRM.derivation_belongs)
      apply(rename_tac c)(*strict*)
      prefer 4
      apply(rule cfgRM_derivation_map_preserves_derivation)
       apply(rename_tac c)(*strict*)
       apply(force)+
    apply(rename_tac c)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac c)(*strict*)
   apply(subgoal_tac "c \<in> cfg_configurations G")
    apply(rename_tac c)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac ca)(*strict*)
    apply (metis setA_app setB_app)
   apply(rename_tac c)(*strict*)
   apply (metis cfgRM.belongs_configurations)
  apply (metis cfgRM.some_position_has_details_at_0)
  done

lemma CFGRM_drop_head_terminals_preserves_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> \<forall>k \<le> m. (\<forall>e c. d k = Some (pair e c) \<longrightarrow> (\<exists>w. cfg_conf c = liftB v @ w))
  \<Longrightarrow> cfgRM.derivation G (derivation_map d (\<lambda>c. \<lparr>cfg_conf = drop (length v) (cfg_conf c)\<rparr>))"
  apply(simp (no_asm) add: cfgRM.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(simp add: derivation_map_def)
    apply(clarsimp)
   apply (metis cfgRM.some_position_has_details_at_0)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "Suc nat \<le> m")
   apply(rename_tac nat a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
    apply(rename_tac nat a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc nat"
      in cfgRM.step_detail_before_some_position)
      apply(rename_tac nat a)(*strict*)
      apply(force)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(simp add: derivation_map_def)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
   apply(subgoal_tac "\<forall>e c. d nat = Some (pair e c) \<longrightarrow> (\<exists>w. cfg_conf c = liftB v @ w)")
    apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
    apply(subgoal_tac "\<forall>e c. d (Suc nat) = Some (pair e c) \<longrightarrow> (\<exists>w. cfg_conf c = liftB v @ w)")
     apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 l r w)(*strict*)
     apply(subgoal_tac "prefix l (liftB v) \<or> prefix (liftB v) l")
      apply(rename_tac nat e1 e2 c1 c2 l r w)(*strict*)
      prefer 2
      apply(rule mutual_prefix_prefix)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 l r w)(*strict*)
     apply(case_tac "liftB v \<sqsubseteq> l")
      apply(rename_tac nat e1 e2 c1 c2 l r w)(*strict*)
      apply(clarsimp)
      apply(simp add: prefix_def)
      apply(clarsimp)
      apply(rename_tac nat e1 e2 c1 c2 r c)(*strict*)
      apply(rule_tac
      t="length (liftB v)"
      and s="length v"
      in ssubst)
       apply(rename_tac nat e1 e2 c1 c2 r c)(*strict*)
       apply (metis liftB_reflects_length)
      apply(rename_tac nat e1 e2 c1 c2 r c)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      s="length (liftB v)"
      and t="length v"
      in ssubst)
       apply(rename_tac nat e1 e2 c1 c2 r c)(*strict*)
       apply (simp add: liftB_reflects_length)
      apply(rename_tac nat e1 e2 c1 c2 r c)(*strict*)
      apply(rule_tac
      t="drop (length (liftB v)) (liftB v)"
      and s="[]"
      in ssubst)
       apply(rename_tac nat e1 e2 c1 c2 r c)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 r c)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      x="c"
      in exI)
      apply(rule_tac
      x="r"
      in exI)
      apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 l r w)(*strict*)
     apply(clarsimp)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 l r w c)(*strict*)
     apply(erule_tac
      x="[]"
      in allE)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>l'. liftB l'=l")
      apply(rename_tac nat e1 e2 c1 c2 l r w c)(*strict*)
      apply(subgoal_tac "\<exists>c'. liftB c'=c")
       apply(rename_tac nat e1 e2 c1 c2 l r w c)(*strict*)
       apply(clarsimp)
       apply(rename_tac nat e1 e2 c1 c2 r w l' c')(*strict*)
       apply(subgoal_tac "l'@c'=v")
        apply(rename_tac nat e1 e2 c1 c2 r w l' c')(*strict*)
        apply(clarsimp)
        apply(case_tac c')
         apply(rename_tac nat e1 e2 c1 c2 r w l' c')(*strict*)
         apply(force)
        apply(rename_tac nat e1 e2 c1 c2 r w l' c' a list)(*strict*)
        apply(subgoal_tac "False")
         apply(rename_tac nat e1 e2 c1 c2 r w l' c' a list)(*strict*)
         apply(force)
        apply(rename_tac nat e1 e2 c1 c2 r w l' c' a list)(*strict*)
        apply(clarsimp)
        apply(rename_tac nat e1 e2 c1 c2 r w l' a list)(*strict*)
        apply(subgoal_tac "teA (prod_lhs e2) # r = liftB (a # list) @ w")
         apply(rename_tac nat e1 e2 c1 c2 r w l' a list)(*strict*)
         apply(clarsimp)
        apply(rename_tac nat e1 e2 c1 c2 r w l' a list)(*strict*)
        apply (metis append_Cons concat_asso list.simps(3) maxTermPrefix_drop_tail maxTermPrefix_shift maxTermPrefix_term_string self_append_conv)
       apply(rename_tac nat e1 e2 c1 c2 r w l' c')(*strict*)
       apply (metis liftB_commutes_over_concat liftB_inj)
      apply(rename_tac nat e1 e2 c1 c2 l r w c)(*strict*)
      apply (metis liftB_commutes_over_concat append_injective2 maxTermPrefix_shift maxTermPrefix_term_string)
     apply(rename_tac nat e1 e2 c1 c2 l r w c)(*strict*)
     apply (metis setA_liftB setA_setmp_concat_1 liftBDeConv2 all_not_in_conv bot_apply empty_subsetI ex_in_conv)
    apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
    apply(erule_tac
      x="Suc nat"
      in allE)
    apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply (metis cfgRM.allPreMaxDomSome_prime not_Some_eq)
  done

definition cfgRM_produce_and_eliminate_from :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal
  \<Rightarrow> 'event list set"
  where
    "cfgRM_produce_and_eliminate_from G A \<equiv>
  {w. \<exists>d.
    cfgRM.derivation G d
    \<and> cfgRM.belongs G d
    \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)
    \<and> (\<exists>i e. d i = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>))}"

lemma cfgRM_produce_and_eliminate_from_concatenate: "
  valid_cfg G
  \<Longrightarrow> w1 \<in> cfgRM_produce_and_eliminate_from G B
  \<Longrightarrow> w2 \<in> cfgRM_produce_and_eliminate_from G A
  \<Longrightarrow> \<lparr>prod_lhs = C, prod_rhs = [teA B, teA A]\<rparr> \<in> cfg_productions G
  \<Longrightarrow> w1 @ w2 \<in> cfgRM_produce_and_eliminate_from G C"
  apply(simp add: cfgRM_produce_and_eliminate_from_def)
  apply(clarsimp)
  apply(rename_tac d da i e ia ea)(*strict*)
  apply(subgoal_tac "\<exists>dA nA eA. cfgRM.derivation G dA \<and> cfgRM.belongs G dA \<and> maximum_of_domain dA nA \<and> dA 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>) \<and> dA nA = Some (pair eA \<lparr>cfg_conf = liftB w2\<rparr>) ")
   apply(rename_tac d da i e ia ea)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take da ia"
      in exI)
   apply(rule_tac
      x="ia"
      in exI)
   apply(rule_tac
      x="ea"
      in exI)
   apply(rule conjI)
    apply(rename_tac d da i e ia ea)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d da i e ia ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da i e ia ea)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac d da i e ia ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da i e ia ea)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d da i e ia ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da i e ia ea)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da i e ia ea)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d da i e ia ea)(*strict*)
  apply(subgoal_tac "\<exists>dB nB eB. cfgRM.derivation G dB \<and> cfgRM.belongs G dB \<and> maximum_of_domain dB nB \<and> dB 0 = Some (pair None \<lparr>cfg_conf = [teA B]\<rparr>) \<and> dB nB = Some (pair eB \<lparr>cfg_conf = liftB w1\<rparr>) ")
   apply(rename_tac d da i e ia ea)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d i"
      in exI)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule conjI)
    apply(rename_tac d da i e ia ea)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d da i e ia ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da i e ia ea)(*strict*)
    apply(rule cfgRM.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac d da i e ia ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da i e ia ea)(*strict*)
    apply(rule maximum_of_domain_derivation_take)
    apply(force)
   apply(rename_tac d da i e ia ea)(*strict*)
   apply(rule conjI)
    apply(rename_tac d da i e ia ea)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d da i e ia ea)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d da i e ia ea)(*strict*)
  apply(thin_tac "cfgRM.derivation G d")
  apply(thin_tac "cfgRM.derivation G da")
  apply(thin_tac "cfgRM.belongs G d")
  apply(thin_tac "cfgRM.belongs G da")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = [teA B]\<rparr>)")
  apply(thin_tac "d i = Some (pair e \<lparr>cfg_conf = liftB w1\<rparr>)")
  apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)")
  apply(thin_tac "da ia = Some (pair ea \<lparr>cfg_conf = liftB w2\<rparr>)")
  apply(erule exE)+
  apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf=[teA C]\<rparr> \<lparr>prod_lhs = C, prod_rhs = [teA B, teA A]\<rparr> \<lparr>cfg_conf=[teA B, teA A]\<rparr>) (derivation_append (derivation_map dA (\<lambda>v. \<lparr>cfg_conf = [teA B] @ (cfg_conf v)\<rparr>)) (derivation_map dB (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v) @ (liftB w2)\<rparr>)) nA) (Suc 0)"
      in exI)
  apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
   apply(rule cfgRM.derivation_append_preserves_derivation)
     apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
     apply(rule cfgRM.der2_is_derivation)
     apply(simp add: cfgRM_step_relation_def)
     apply(rename_tac dA dB nA nB eA eB)(*strict*)
     apply(force)
    apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
    apply(subgoal_tac "cfgRM.derivation_from_to G (derivation_append (derivation_map dA (\<lambda>v. \<lparr>cfg_conf = [teA B] @ cfg_conf v\<rparr>)) (derivation_map dB (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB w2\<rparr>)) nA) {pair None \<lparr>cfg_conf = SSw1 @ SSw2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = SSw1' @ SSw2'\<rparr>}" for SSw1 SSw2 SSw1' SSw2')
     apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
     prefer 2
     apply(rule cfgRM_concatExtendIsFromToBoth)
          apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
          apply(force)
         apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
         apply(simp add: cfgRM.derivation_to_def cfgRM.derivation_from_def cfgRM.derivation_from_to_def)
         apply(rule_tac
      x="nB"
      in exI)
         apply(clarsimp)
         apply(simp add: maximum_of_domain_def)
        apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
        apply(simp add: cfgRM.derivation_to_def cfgRM.derivation_from_def cfgRM.derivation_from_to_def)
        apply(rule conjI)
         apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
         apply(force)
        apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
        apply(rule_tac
      x="nA"
      in exI)
        apply(clarsimp)
        apply(rename_tac dA dB nA nB eA eB)(*strict*)
        apply(simp add: maximum_of_domain_def)
       apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
       apply (metis setA_liftB)
      apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
      apply(force)
     apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
     apply(force)
    apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
    apply(simp add: cfgRM.derivation_to_def cfgRM.derivation_from_def cfgRM.derivation_from_to_def)
   apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
   apply(rule cfgRM.derivation_append_preserves_belongs)
     apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
     apply(force)
    apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
    apply(rule cfgRM.der2_belongs_prime)
      apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
      apply(force)
     apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(rename_tac dA dB nA nB eA eB)(*strict*)
     apply (metis prod_lhs_in_nonterms)
    apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(rename_tac dA dB nA nB eA eB)(*strict*)
    apply(force)
   apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
   apply(force)
  apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
  apply(rule conjI)
   apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac d da i e ia ea dA dB nA nB eA eB)(*strict*)
  apply(rule_tac
      x="Suc (nA+nB)"
      in exI)
  apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac dA dB nA nB eA eB)(*strict*)
  apply(case_tac nB)
   apply(rename_tac dA dB nA nB eA eB)(*strict*)
   apply(clarsimp)
   apply(rename_tac dA dB nA eA)(*strict*)
   apply(case_tac w1)
    apply(rename_tac dA dB nA eA)(*strict*)
    apply(clarsimp)
   apply(rename_tac dA dB nA eA a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac dA dB nA nB eA eB nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac dA dB nA eA eB nat)(*strict*)
  apply(case_tac nA)
   apply(rename_tac dA dB nA eA eB nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac dA dB eB nat)(*strict*)
   apply(case_tac w2)
    apply(rename_tac dA dB eB nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac dA dB eB nat a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac dA dB nA eA eB nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac dA dB eA eB nat nata)(*strict*)
  apply (metis liftB_commutes_over_concat)
  done

definition cfg_LRk :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "cfg_LRk G k \<equiv>
  \<forall>d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v.
  cfgRM.derivation_initial G d1
  \<and> d1 n1 = Some (pair e1 \<lparr>cfg_conf = \<delta>1 @ [teA A1] @ liftB y1\<rparr>)
  \<and> d1 (Suc n1) = Some (pair (Some e1') \<lparr>cfg_conf = \<delta>1 @ \<omega>1 @ liftB y1\<rparr>)
  \<and> cfgRM.derivation_initial G d2
  \<and> d2 n2 = Some (pair e2 \<lparr>cfg_conf = \<delta>2 @ [teA A2] @ liftB y2\<rparr>)
  \<and> d2 (Suc n2) = Some (pair (Some e2') \<lparr>cfg_conf = \<delta>2 @ \<omega>2 @ liftB y2\<rparr>)
  \<and> \<delta>1 @ \<omega>1 @ liftB v = \<delta>2 @ \<omega>2
  \<and> kPrefix k y1 = kPrefix k (v @ y2)
  \<longrightarrow> (\<delta>1 = \<delta>2 \<and> A1 = A2 \<and> \<omega>1 = \<omega>2)"

definition cfg_LRkDo :: "('a,'b) cfg \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> bool" where
  "cfg_LRkDo G' Do S' k =
  (\<forall>d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v.
  cfgRM.derivation_initial G' d1
  \<and> d1 (Suc n1) = Some (pair e1 \<lparr>cfg_conf=\<delta>1@[teA A1]@(liftB y1)\<rparr>)
  \<and> d1 (Suc (Suc n1)) = Some (pair (Some e1') \<lparr>cfg_conf=\<delta>1@\<omega>1@(liftB y1)\<rparr>)
  \<and> cfgRM.derivation_initial G' d2
  \<and> d2 (Suc n2) = Some (pair e2 \<lparr>cfg_conf=\<delta>2@[teA A2]@(liftB y2)\<rparr>)
  \<and> d2 (Suc (Suc n2)) = Some (pair (Some e2') \<lparr>cfg_conf=\<delta>2@\<omega>2@(liftB y2)\<rparr>)
  \<and> \<delta>1@\<omega>1@(liftB v)=\<delta>2@\<omega>2
  \<and> kPrefix k y1 = kPrefix k (v@y2)
  \<longrightarrow> (\<delta>1=\<delta>2 \<and> A1=A2 \<and> \<omega>1=\<omega>2))"

lemma supCFGRMhasAllStepsOfsub: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfgRM_step_relation G1 c1 e c2
  \<Longrightarrow> cfgRM_step_relation G2 c1 e c2"
  apply(simp add: cfgRM_step_relation_def)
  apply(auto)
  apply(rename_tac l r)(*strict*)
  apply(simp add: cfg_sub_def)
  apply(auto)
  done

definition cfgRM_accessible_nonterminals :: "
  ('nonterminal,'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgRM_accessible_nonterminals G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n c.
      cfgRM.derivation_initial G d
      \<and> get_configuration (d n) = Some c
      \<and> (\<exists>w1 w2. cfg_conf c = w1 @ teA A # liftB w2)}"

definition cfgRM_accessible_nonterminals_ALT :: "
  ('nonterminal,'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgRM_accessible_nonterminals_ALT G \<equiv>
  {A. \<exists>d n e w1 w2.
      cfgRM.derivation_initial G d
      \<and> d n = Some (pair e \<lparr>cfg_conf = w1 @ teA A # liftB w2 \<rparr>)}"

lemma cfgRM_accessible_nonterminals_ALT_vs_cfgRM_accessible_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgRM_accessible_nonterminals_ALT G = cfgRM_accessible_nonterminals G"
  apply(simp add: cfgRM_accessible_nonterminals_ALT_def cfgRM_accessible_nonterminals_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rename_tac x d n e w1 w2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x d n e w1 w2)(*strict*)
    prefer 2
    apply(rule cfgRM.belongs_configurations)
     apply(rename_tac x d n e w1 w2)(*strict*)
     apply(rule cfgRM.derivation_initial_belongs)
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

definition cfgRM_Nonblockingness_nonterminals :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgRM_Nonblockingness_nonterminals G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n e w'.
      cfgRM.derivation G d
      \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)
      \<and> d n = Some (pair e \<lparr>cfg_conf = w'\<rparr>)
      \<and> setA w' = {}}"

definition cfgRM_Nonblockingness_nonterminals_ALT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set"
  where
    "cfgRM_Nonblockingness_nonterminals_ALT G \<equiv>
  {A \<in> cfg_nonterminals G.
    \<exists>d n e w.
      cfgRM.derivation G d
      \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA A]\<rparr>)
      \<and> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)}"

lemma cfgRM_Nonblockingness_branching_implies_cfgRM_accessible_nonterminals_contained_in_cfgRM_Nonblockingness_nonterminals: "
  valid_cfg G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> cfgRM_accessible_nonterminals G \<subseteq> cfgRM_Nonblockingness_nonterminals G"
  apply(simp add: cfgRM_accessible_nonterminals_def)
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
  apply(subgoal_tac "\<exists>d. cfgRM.derivation_initial G d \<and> maximum_of_domain d n \<and> d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # liftB w2\<rparr>)")
   apply(rename_tac x d n w1 w2 e)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_take d n"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply (metis cfgRM.derivation_take_preserves_derivation_initial)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d n w1 w2 e)(*strict*)
    apply (metis maximum_of_domain_derivation_take not_None_eq)
   apply(rename_tac x d n w1 w2 e)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac x d n w1 w2 e)(*strict*)
  apply(thin_tac "cfgRM.derivation_initial G d")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # liftB w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac x n w1 w2 e d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x n w1 w2 e d)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and ?w1.0="w1"
      and ?w2.0="[teA x]"
      and ?w3.0="liftB w2"
      in CFGRM_Nonblockingness_to_elimination)
         apply(rename_tac x n w1 w2 e d)(*strict*)
         apply(force)
        apply(rename_tac x n w1 w2 e d)(*strict*)
        apply(simp add: cfgRM.derivation_initial_def)
       apply(rename_tac x n w1 w2 e d)(*strict*)
       apply(rule cfgRM.derivation_initial_belongs)
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
  apply(thin_tac "cfgRM.Nonblockingness_branching G")
  apply(thin_tac "maximum_of_domain d n")
  apply(thin_tac "cfgRM.derivation_initial G d")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # liftB w2\<rparr>)")
  apply(clarsimp)
  apply(rename_tac x d' n' w e)(*strict*)
  apply(simp add: cfgRM_Nonblockingness_nonterminals_def)
  apply(rule conjI)
   apply(rename_tac x d' n' w e)(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf = [teA x]\<rparr> \<in> cfg_configurations G")
    apply(rename_tac x d' n' w e)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac x d' n' w e)(*strict*)
   apply (metis cfgRM.belongs_configurations)
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

lemma cfgRM_Nonblockingness_branching_implies_FB_iterated_elimination: "
  valid_cfg G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> cfgRM.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> cfg_conf c = w1 @ teA x # w2
  \<Longrightarrow> \<exists>d. cfgRM.derivation_initial G d \<and>
  (\<exists>n c. get_configuration (d n) = Some c \<and>
  (\<exists>w1 w2. cfg_conf c = w1 @ teA x # liftB w2))"
  apply(induct "length (filterA w2)" arbitrary: w2 d n e c)
   apply(rename_tac w2 d n e c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule conjI)
    apply(rename_tac w2 d n e c)(*strict*)
    apply(force)
   apply(rename_tac w2 d n e c)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      x="w1"
      in exI)
   apply(subgoal_tac "\<exists>w. liftB w = w2")
    apply(rename_tac w2 d n e c)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB w2"
      in exI)
    apply(rule liftBDeConv2)
    apply(rule filterA_setA)
    apply(force)
   apply(rename_tac w2 d n e c)(*strict*)
   apply(force)
  apply(rename_tac xa w2 d n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa w2 d n e c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa w2 d n e)(*strict*)
  apply(subgoal_tac "\<exists>wx1 A wx2. w2 = wx1 @[teA A]@liftB wx2")
   apply(rename_tac xa w2 d n e)(*strict*)
   prefer 2
   apply(rule filterA_gt_0_then_rm_nonterminal)
   apply(force)
  apply(rename_tac xa w2 d n e)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa d n e wx1 A wx2)(*strict*)
  apply(subgoal_tac "A \<in> cfgRM_Nonblockingness_nonterminals G")
   apply(rename_tac xa d n e wx1 A wx2)(*strict*)
   prefer 2
   apply(rule_tac
      A="cfgRM_accessible_nonterminals G"
      in set_mp)
    apply(rename_tac xa d n e wx1 A wx2)(*strict*)
    apply(rule cfgRM_Nonblockingness_branching_implies_cfgRM_accessible_nonterminals_contained_in_cfgRM_Nonblockingness_nonterminals)
     apply(rename_tac xa d n e wx1 A wx2)(*strict*)
     apply(force)
    apply(rename_tac xa d n e wx1 A wx2)(*strict*)
    apply(force)
   apply(rename_tac xa d n e wx1 A wx2)(*strict*)
   apply(simp add: cfgRM_accessible_nonterminals_def)
   apply(subgoal_tac "\<lparr>cfg_conf = w1 @ teA x # wx1 @ teA A # liftB wx2\<rparr> \<in> cfg_configurations G")
    apply(rename_tac xa d n e wx1 A wx2)(*strict*)
    prefer 2
    apply (rule cfgRM.belongs_configurations)
     apply(rename_tac xa d n e wx1 A wx2)(*strict*)
     apply(rule cfgRM.derivation_initial_belongs)
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
      x="w1@teA x#wx1"
      in exI)
   apply(force)
  apply(rename_tac xa d n e wx1 A wx2)(*strict*)
  apply(simp add: cfgRM_Nonblockingness_nonterminals_def)
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
  apply(subgoal_tac "\<exists>d n e c. cfgRM.derivation_initial G d \<and> d n = Some (pair e c) \<and> cfg_conf c = w1 @ teA x # wx1 @ liftB w @ liftB wx2")
   apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
   prefer 2
   apply(rule_tac
      x="derivation_append d (derivation_map da (\<lambda>c. \<lparr>cfg_conf=w1@teA x#wx1@(cfg_conf c)@liftB wx2\<rparr>)) n"
      in exI)
   apply(rule_tac
      x="n+Suc na"
      in exI)
   apply(rule_tac
      x="ea"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf=w1 @ teA x # wx1 @ liftB w @ liftB wx2\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule context_conjI)
    apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation_initial)
      apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
      apply(force)
     apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
     apply(force)
    apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation)
      apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
      apply(simp add: cfgRM.derivation_initial_def)
     apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
     apply(rule cfgRM.derivation_map_preserves_derivation)
       apply(rename_tac xa d n e wx1 A wx2 da ea w na)(*strict*)
       apply(force)
      apply(rename_tac xa d n e wx1 A wx2 da ea w na i eb c)(*strict*)
      apply(force)
     apply(rename_tac xa d n e wx1 A wx2 da ea w na c1 eb c2)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac xa d n e wx1 A wx2 da ea w na c1 eb c2 l r)(*strict*)
     apply(rule_tac
      x="w1 @ teA x # wx1 @ l"
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
  apply(thin_tac "cfgRM.derivation_initial G d")
  apply(thin_tac "cfgRM.Nonblockingness_branching G ")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = w1 @ teA x # wx1 @ teA A # liftB wx2\<rparr>)")
  apply(thin_tac "cfgRM.derivation G da")
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
      x="wx1 @ liftB w @ liftB wx2"
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
      x="\<lparr>cfg_conf = w1 @ teA x # wx1 @ liftB w @ liftB wx2\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: filterA_commutes_over_concat filterA_liftB)
  done

corollary cfg_dependency_between_Nonblockingnessness_properties1RM: "
  valid_cfg G
  \<Longrightarrow> cfgRM.Nonblockingness_branching G
  \<Longrightarrow> nonblockingness_language (cfgRM.unmarked_language G) (cfgRM.marked_language G)"
  apply(simp add: nonblockingness_language_def)
  apply (metis nonblockingness_language_def cfgRM.AX_BF_Bra_OpLa)
  done

lemma cfgRM_no_nonterminal_at_end_in_marking_condition: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
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
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac i ea ca)(*strict*)
     apply(force)
    apply(rename_tac i ea ca)(*strict*)
    apply(force)
   apply(rename_tac i ea ca)(*strict*)
   apply (metis (mono_tags) cfgRM.allPreMaxDomSome_prime le_antisym not_less_eq_eq option.distinct(1))
  apply(rename_tac i ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea ca e2 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i ea ca e2 c2 l r)(*strict*)
  apply(case_tac ca)
  apply(rename_tac i ea ca e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea e2 c2 l r)(*strict*)
  apply (metis elemInsetA empty_iff)
  done

lemma cfgRM_Nonblockingness_nonterminals_ALT_vs_cfgRM_Nonblockingness_nonterminals: "
  cfgRM_Nonblockingness_nonterminals_ALT G = cfgRM_Nonblockingness_nonterminals G"
  apply(rule antisym)
   apply(simp add: cfgRM_Nonblockingness_nonterminals_ALT_def cfgRM_Nonblockingness_nonterminals_def)
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
  apply(simp add: cfgRM_Nonblockingness_nonterminals_ALT_def cfgRM_Nonblockingness_nonterminals_def)
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

lemma cfg_sub_preserves_derivationRM: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgRM.derivation G d"
  apply(simp (no_asm) add: cfgRM.derivation_def cfgRM.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgRM.derivation_def cfgRM.derivation_initial_def)
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule cfgRM.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(simp add: cfg_sub_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
  apply(force)
  done

lemma cfg_sub_preserves_derivation_initialRM: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation_initial G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgRM.derivation_initial G d"
  apply(rule cfgRM.derivation_initialI)
   apply(simp (no_asm) add: cfgRM.derivation_def cfgRM.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(simp add: cfgRM.derivation_def cfgRM.derivation_initial_def)
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
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation SSG c1 e2 c2" for SSd SSn SSG)
    apply(rename_tac nat a)(*strict*)
    prefer 2
    apply(rule cfgRM.step_detail_before_some_position)
      apply(rename_tac nat a)(*strict*)
      apply(simp add: cfgRM.derivation_initial_def)
      apply(force)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(simp add: cfg_sub_def)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
   apply(force)
  apply(simp add: cfgRM.derivation_def cfgRM.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: cfg_initial_configurations_def get_configuration_def cfg_configurations_def cfg_sub_def)
  apply(force)
  done

lemma empty_start_then_cfgRM_deri_is_empty: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = []\<rparr>)
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> n=0"
  apply(case_tac n)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e2 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  done

lemma cfgRM_no_step_without_nontermsX: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> setA (cfg_conf c)={}
  \<Longrightarrow> d (n+m) \<noteq> None
  \<Longrightarrow> m=0"
  apply(case_tac m)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+m"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat y e2 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat y e2 c2 l r)(*strict*)
  apply(case_tac c)
  apply(rename_tac nat y e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat y e2 c2 l r)(*strict*)
  apply (metis elemInsetA emptyE)
  done

definition SententialRM :: "('a,'b) cfg \<Rightarrow> ('a,'b)DT_two_elements list \<Rightarrow> bool" where
  "SententialRM G w = (\<exists>d e n v. cfgRM.derivation G d \<and> cfgRM.belongs G d \<and> cfgRM.derivation_initial G d \<and> d n = Some (pair e \<lparr>cfg_conf=w@v\<rparr>))"

lemma Nonterminal_free_SententialRM_in_unmarked_language: "
  valid_cfg G
  \<Longrightarrow> SententialRM G (liftB w)
  \<Longrightarrow> w \<in> cfgRM.unmarked_language G"
  apply(simp add: cfgRM.unmarked_language_def SententialRM_def)
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

lemma CFGRM_noStep: "
  setA (cfg_conf c)={}
  \<Longrightarrow> \<not> cfgRM_step_relation G c e c'"
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac l r)(*strict*)
  apply(subgoal_tac "prod_lhs e \<in> setA (l @ teA (prod_lhs e) # r)")
   apply(rename_tac l r)(*strict*)
   apply(force)
  apply(rename_tac l r)(*strict*)
  apply(rule elemInsetA)
  done

lemma CFGRM_terminals_stays_context: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> setA w1 = {}
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=w1@v@w2\<rparr>)
  \<Longrightarrow> d j = Some (pair e2 \<lparr>cfg_conf=x\<rparr>)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> \<exists>y. w1@y@w2=x"
  apply(induct "j-i" arbitrary: j e2 x)
   apply(rename_tac j e2 x)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa j e2 x)(*strict*)
  apply(case_tac j)
   apply(rename_tac xa j e2 x)(*strict*)
   apply(force)
  apply(rename_tac xa j e2 x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e2 x nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac xa e2 x nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac xa e2 x nat)(*strict*)
     apply(force)
    apply(rename_tac xa e2 x nat)(*strict*)
    apply(force)
   apply(rename_tac xa e2 x nat)(*strict*)
   apply(force)
  apply(rename_tac xa e2 x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(erule_tac
      x="cfg_conf c1"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac xa x nat e1a e2a c1)(*strict*)
   apply(force)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa x nat e1a e2a c1)(*strict*)
   apply(force)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x nat e1a e2a c1 y)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa nat e1a e2a c1 y l r)(*strict*)
  apply(case_tac "e2a")
  apply(rename_tac xa nat e1a e2a c1 y l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac xa nat e1a e2a c1 y l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa nat e1a c1 y l r A w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac xa nat e1a c1 y l r A w cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa nat e1a y l r A w)(*strict*)
  apply(subgoal_tac "prefix w1 l \<or> prefix l w1")
   apply(rename_tac xa nat e1a y l r A w)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac xa nat e1a y l r A w)(*strict*)
  apply(erule disjE)
   apply(rename_tac xa nat e1a y l r A w)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac xa nat e1a y l r A w c)(*strict*)
   apply(case_tac c)
    apply(rename_tac xa nat e1a y l r A w c)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa nat e1a y l r A w)(*strict*)
    apply(case_tac y)
     apply(rename_tac xa nat e1a y l r A w)(*strict*)
     apply(clarsimp)
    apply(rename_tac xa nat e1a y l r A w a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa nat e1a y l r A w c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa nat e1a y l A w list)(*strict*)
   apply (metis elemInsetA emptyE)
  apply(rename_tac xa nat e1a y l r A w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac xa nat e1a y r A w c)(*strict*)
  apply(subgoal_tac "prefix y c \<or> prefix c y")
   apply(rename_tac xa nat e1a y r A w c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac xa nat e1a y r A w c)(*strict*)
  apply(erule disjE)
   apply(rename_tac xa nat e1a y r A w c)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac xa nat e1a r A w c ca)(*strict*)
   apply(case_tac ca)
    apply(rename_tac xa nat e1a r A w c ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa nat e1a r A w c ca a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa nat e1a y r A w c)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac xa nat e1a y r A w ca)(*strict*)
  apply (metis elemInsetA emptyE)
  done

lemma cfgRM_no_step_from_no_nonterminal: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.belongs G d
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
   apply(rule_tac n="x" in cfgRM.derivationNoFromNone2_prime)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(case_tac "Suc n=x")
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> SSd (Suc SSi) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSi)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 c2)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(case_tac c)
    apply(rename_tac e2 c2 cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 c2 l r)(*strict*)
    apply(case_tac c2)
    apply(rename_tac e2 c2 l r cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e2 l r)(*strict*)
    apply (metis cfg_configuration.simps(1) cfgRM_no_step_without_nonterms not_None_eq)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> SSd (Suc SSi) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSi)
   apply(rename_tac a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a e2 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(case_tac c)
  apply(rename_tac a e2 c2 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac a e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a e2 l r)(*strict*)
  apply (metis cfg_configuration.simps(1) cfgRM_no_step_without_nonterms not_None_eq)
  done

lemma cfgRM_equal_terminating_derivations_smae_length: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d1
  \<Longrightarrow> cfgRM.derivation G d2
  \<Longrightarrow> cfgRM.belongs G d1
  \<Longrightarrow> cfgRM.belongs G d2
  \<Longrightarrow> d1 n1 = Some (pair e1 c1)
  \<Longrightarrow> d2 n2 = Some (pair e2 c2)
  \<Longrightarrow> setA (cfg_conf c1) = {}
  \<Longrightarrow> setA (cfg_conf c2) = {}
  \<Longrightarrow> d1 = d2
  \<Longrightarrow> n1 = n2"
  apply(clarsimp)
  apply(case_tac "n1<n2")
   apply(subgoal_tac "d2 n2 = None")
    apply(force)
   apply(rule_tac
      n="n1"
      in cfgRM_no_step_from_no_nonterminal)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(case_tac "n2<n1")
   apply(subgoal_tac "d2 n1 = None")
    apply(force)
   apply(rule_tac
      n="n2"
      in cfgRM_no_step_from_no_nonterminal)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

definition CFGrm_unambiguous :: "('a,'b) cfg \<Rightarrow> bool" where
  "CFGrm_unambiguous G \<equiv> (\<forall>d1 d2 n1 n2 e1 e2 w.
  cfgRM.derivation_initial G d1
  \<longrightarrow> cfgRM.derivation_initial G d2
  \<longrightarrow> d1 n1 = Some (pair e1 \<lparr>cfg_conf=liftB w\<rparr>)
  \<longrightarrow> d2 n2 = Some (pair e2 \<lparr>cfg_conf=liftB w\<rparr>)
  \<longrightarrow> d1 = d2)"

lemma lemma_4_7_existence: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.belongs G d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = foldl (@) [] \<alpha>\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = liftB w\<rparr>)
  \<Longrightarrow> \<pi>=map the (get_labels d n)
  \<Longrightarrow> \<exists>\<pi>s ws.
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
     apply(rule cfgRM.der1_is_derivation)
    apply(rename_tac d \<alpha> w i)(*strict*)
    apply(rule conjI)
     apply(rename_tac d \<alpha> w i)(*strict*)
     apply(rule cfgRM.der1_belongs)
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
     apply(rule cfgRM.belongs_configurations)
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac n d \<alpha> w e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac n d \<alpha> w e)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> w e)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> w e)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> w e e2 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
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
  apply(clarsimp)
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
   apply(rule cfgRM.derivation_drop_preserves_derivation_prime)
    apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d \<alpha> w e e2 na l2 r2)(*strict*)
   apply(rule cfgRM.derivation_drop_preserves_belongs)
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
  apply(subgoal_tac "min (length \<alpha>) na = na")
   apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d \<alpha> w e e2 na l2 r2 \<pi>s)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(thin_tac "min (length \<alpha>) na = na")
  apply(subgoal_tac "Suc (length \<alpha> - Suc 0) = length \<alpha>")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(clarsimp)
  apply(thin_tac "Suc (length \<alpha> - Suc 0) = length \<alpha>")
  apply(rule_tac
      t="map the (get_labels d (Suc n))"
      and s="e2#(foldl (@) [] (rev \<pi>s))"
      in ssubst)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   apply(simp (no_asm) add: get_labels_def)
   apply(rule listEqI)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_drop_def)
    apply(simp (no_asm) add: get_labels_def)
    apply (metis gr0I list.size(3) nat_seqEmpty nat_seq_length_Suc0 zero_less_Suc)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
   apply(clarsimp)
   apply(simp (no_asm) add: get_labels_def)
   apply(simp add: derivation_drop_def)
   apply(subgoal_tac "length (nat_seq (Suc 0) (Suc n)) = SSn + 1 - SSi" for SSn SSi)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) n) = SSn + 1 - SSi" for SSn SSi)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc n) ! i = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
   apply(clarsimp)
   apply(case_tac i)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
    apply(simp add: get_label_def)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
   apply(rule_tac
      t="map (the \<circ> (\<lambda>i. get_label (if i = 0 then case_option undefined (case_derivation_configuration (\<lambda>e c. Some (pair None c))) (d (Suc 0)) else d (i + Suc 0)))) (nat_seq (Suc 0) n) ! nat"
      and s="(the \<circ> (\<lambda>i. get_label (if i = 0 then case_option undefined (case_derivation_configuration (\<lambda>e c. Some (pair None c))) (d (Suc 0)) else d (i + Suc 0)))) ((nat_seq (Suc 0) n) ! nat)"
      in ssubst)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
    apply(rule nth_map)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
   apply(subgoal_tac "nat_seq (Suc 0) n ! nat = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
    apply(clarify)
    apply(subgoal_tac "False")
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
    apply(arith)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(subgoal_tac "foldl (@) [] (drop (Suc na) \<pi>s) = []")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   prefer 2
   apply(rule foldl_empty)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws a)(*strict*)
   apply(subgoal_tac "\<exists>i<length (drop (Suc na) \<pi>s). (drop (Suc na) \<pi>s)!i = a")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws a)(*strict*)
    prefer 2
    apply (metis in_set_conv_nth)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
   apply(erule_tac
      x="i+Suc na"
      in allE)
   apply(erule impE)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(subgoal_tac "(take na \<alpha> @ (l2 @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>) ! Suc (i + na) = \<alpha>!(Suc(i+na))")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    prefer 2
    apply(rule select_from_drop)
    apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(subgoal_tac "setA (\<alpha> ! Suc (i + na)) = {}")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(case_tac n')
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
     apply(clarsimp)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d')(*strict*)
     apply(rule_tac
      t="na+i"
      and s="i+na"
      in ssubst)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d')(*strict*)
      apply(force)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d')(*strict*)
     apply(clarsimp)
     apply(simp add: get_labels_def)
     apply (metis nat_seqEmpty zero_less_Suc)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e' nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' e' nat)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d' 0 = Some (pair e1 c1) \<and> d' (Suc 0) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' e' nat)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc nat"
      in cfgRM.step_detail_before_some_position)
       apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' e' nat)(*strict*)
       apply(force)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' e' nat)(*strict*)
      apply(force)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' e' nat)(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' e' nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' e' nat e2a c2)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' e' nat e2a c2 l r)(*strict*)
    apply (metis List.set_simps(1) elemInsetA length_pos_if_in_set less_not_refl3 list.size(3))
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(rule_tac
      v="r2 @ foldl (@) [] (drop (Suc na) \<alpha>)"
      in setA_empty_from_greater_set)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(rule_tac
      B="set(foldl (@) [] (drop (Suc na) \<alpha>))"
      in subset_trans)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(rule elements_preserved_under_foldl)
    apply(rule_tac
      t="Suc (i+na)"
      and s="Suc na + i"
      in ssubst)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(rule nth_drop_elem)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(rule_tac
      x="(take na \<pi>s @ [e2#(\<pi>s!na)] @ drop (Suc na) \<pi>s)"
      in exI)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   apply(rule foldl_rev_take_drop)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(rule_tac
      x="ws"
      in exI)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(rule conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws)(*strict*)
  apply(rule allI)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
  apply(rule impI)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "min (length \<alpha>) na=na")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Suc (length \<alpha> - Suc 0) = length \<alpha>")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i)(*strict*)
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
    apply(case_tac "i<na")
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
     apply(rule_tac
      t="(take na \<alpha> @ (l2 @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>) ! i"
      in ssubst)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
      apply(rule nth_append_1)
      apply(force)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
     apply (metis List.length_take List.nth_append length_take_min nth_take)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(subgoal_tac "length (take na \<alpha>)=na")
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
     prefer 2
     apply (metis List.length_take)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(rule_tac
      t="(take na \<alpha> @ (l2 @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>) ! i"
      and s="((l2 @ prod_rhs e2 @ r2) # drop (Suc na) \<alpha>) ! (i-(length(take na \<alpha>)))"
      in ssubst)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
     apply(rule nth_append_2)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(clarsimp)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(rule_tac
      x="n'"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="map the (get_labels d' n')"
      and s="\<pi>s ! i"
      in ssubst)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(subgoal_tac "length (take na \<pi>s)=na")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    prefer 2
    apply (metis List.length_take)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(case_tac "i<na")
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(rule_tac
      t="(take na \<pi>s @ (e2 # \<pi>s ! na) # drop (Suc na) \<pi>s) ! i"
      and s="(take na \<pi>s) ! i"
      in ssubst)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
     apply(rule nth_append_1)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply (metis nth_take)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(rule_tac
      t="(take na \<pi>s @ (e2#\<pi>s!na) # drop (Suc na) \<pi>s) ! i"
      and s="((e2#\<pi>s!na) # drop (Suc na) \<pi>s) ! (i-(length(take na \<pi>s)))"
      in ssubst)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
    apply(rule nth_append_2)
    apply(force)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
  apply(subgoal_tac "\<exists>n. na+n=i")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
   prefer 2
   apply(rule_tac
      x="i-na"
      in exI)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws i d' n' e')(*strict*)
  apply(clarsimp)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = l2 @ teA (prod_lhs e2) # r2\<rparr> e2 \<lparr>cfg_conf = l2 @ prod_rhs e2 @ r2\<rparr>) d' (Suc 0)"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(rule cfgRM.derivation_append_preserves_derivation)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
     apply(rule cfgRM.der2_is_derivation)
     apply(simp add: cfgRM_step_relation_def)
     apply(rule_tac
      x="l2"
      in exI)
     apply(rule_tac
      x="r2"
      in exI)
     apply(clarsimp)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
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
   apply(rule cfgRM.derivation_belongs)
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
    apply(rule cfgRM.belongs_configurations)
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
  apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = l2 @ teA (prod_lhs e2) # r2\<rparr> e2 \<lparr>cfg_conf = l2 @ prod_rhs e2 @ r2\<rparr>) d' (Suc 0)) (Suc n')"
      and s="Some e2 # (get_labels d' n')"
      in ssubst)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule_tac
      t="(Suc n')"
      and s="Suc 0+ n'"
      in ssubst)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(force)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = l2 @ teA (prod_lhs e2) # r2\<rparr> e2 \<lparr>cfg_conf = l2 @ prod_rhs e2 @ r2\<rparr>) d' (Suc 0)) (Suc 0 + n')"
      in ssubst)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(rule cfgRM.get_labels_concat2)
       apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
       apply(force)
      apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
      apply(rule cfgRM.der2_is_derivation)
      apply(simp add: cfgRM_step_relation_def)
      apply(rule_tac
      x="l2"
      in exI)
      apply(clarsimp)
      apply(simp add: setAConcat)
     apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
     apply(force)
    apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(clarsimp)
  apply(simp add: get_labels_def der2_def get_label_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc 0) = [Suc 0]")
   apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
   prefer 2
   apply (metis natUptTo_n_n)
  apply(rename_tac n d \<alpha> e e2 na l2 r2 \<pi>s ws d' n' e')(*strict*)
  apply(clarsimp)
  done

lemma equal_labels_implies_equal_cfgRMderivation: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d'
  \<Longrightarrow> cfgRM.derivation G d'a
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d' i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+m1"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac i y ya)(*strict*)
     apply(force)
    apply(rename_tac i y ya)(*strict*)
    apply(force)
   apply(rename_tac i y ya)(*strict*)
   apply(force)
  apply(rename_tac i y ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d'a i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      m="n+m2"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 c1 c2 e2a c2a l r)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
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
  apply(subgoal_tac "\<exists>ra'. liftB ra' = ra")
   apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB ra"
      in exI)
   apply (metis liftBDeConv2)
  apply(rename_tac i y ya e1 e2 e2a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a l r la ra')(*strict*)
  apply(thin_tac "setA (liftB ra') = {}")
  apply(subgoal_tac "\<exists>r'. liftB r' = r")
   apply(rename_tac i y ya e1 e2 e2a l r la ra')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB r"
      in exI)
   apply (metis liftBDeConv2)
  apply(rename_tac i y ya e1 e2 e2a l r la ra')(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a l la ra' r')(*strict*)
  apply(thin_tac "setA (liftB r') = {}")
  apply(subgoal_tac "liftB r' = liftB ra'")
   apply(rename_tac i y ya e1 e2 e2a l la ra' r')(*strict*)
   prefer 2
   apply(rule terminalTailEquals1_prime)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l la ra' r')(*strict*)
  apply(subgoal_tac "r'=ra'")
   apply(rename_tac i y ya e1 e2 e2a l la ra' r')(*strict*)
   prefer 2
   apply(rule liftB_inj)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a l la ra' r')(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 e2 e2a la ra')(*strict*)
  apply(subgoal_tac "prod_rhs e2 = prod_rhs e2a")
   apply(rename_tac i y ya e1 e2 e2a la ra')(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 e2 e2a la ra')(*strict*)
  apply(case_tac e2)
  apply(rename_tac i y ya e1 e2 e2a la ra' prod_lhsa prod_rhsa)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac i y ya e1 e2 e2a la ra' prod_lhsa prod_rhsa prod_lhsaa prod_rhsaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i y ya e1 la ra' prod_rhs prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac w1 A w2)
  apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
  apply(subgoal_tac "(map the (get_labels d' (n + m1)) @ c)!i = (map the (get_labels d'a (n + m2)))!i")
   apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
  apply(thin_tac "map the (get_labels d' (n + m1)) @ c = map the (get_labels d'a (n + m2))")
  apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
  apply(simp add: get_labels_def)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n + m1)) = (n+m1) + 1 - (Suc 0)")
   apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
  apply(subgoal_tac "length (nat_seq (Suc 0) (n + m2)) = (n+m2) + 1 - (Suc 0)")
   apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) (n + m1)) @ c) ! i = (map (the \<circ> (\<lambda>i. get_label (d' i))) (nat_seq (Suc 0) (n + m1))) ! i")
   apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule nth_appendX)
   apply(force)
  apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat_seq (Suc 0) (n + m1) ! i = (Suc 0)+i")
   apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (n + m2) ! i = (Suc 0)+i")
   apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
    apply(force)
   apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
   apply(force)
  apply(rename_tac i y ya e1 la ra' w1 A w2)(*strict*)
  apply(clarsimp)
  apply(simp add: get_label_def)
  done

theorem cfg_sub_preserves_cfg_LRk: "
  valid_cfg G1
  \<Longrightarrow> valid_cfg G2
  \<Longrightarrow> cfg_sub G1 G2
  \<Longrightarrow> cfg_LRk G2 k
  \<Longrightarrow> cfg_LRk G1 k"
  apply(unfold cfg_LRk_def)
  apply(rule allI)+
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule impI)
  apply(erule_tac x="d1" in allE)
  apply(erule_tac x="n1" in allE)
  apply(erule_tac x="\<delta>1" in allE)
  apply(erule_tac x="A1" in allE)
  apply(erule_tac x="y1" in allE)
  apply(erule_tac x="e1" in allE)
  apply(erule_tac x="e1'" in allE)
  apply(erule_tac x="\<omega>1" in allE)
  apply(erule_tac x="d2" in allE)
  apply(erule_tac x="n2" in allE)
  apply(erule_tac x="\<delta>2" in allE)
  apply(erule_tac x="A2" in allE)
  apply(erule_tac x="y2" in allE)
  apply(erule_tac x="e2" in allE)
  apply(erule_tac x="e2'" in allE)
  apply(erule_tac x="\<omega>2" in allE)
  apply(erule_tac x="v" in allE)
  apply(erule impE)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(rule_tac cfg_sub_preserves_derivation_initialRM)
     apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
     apply(force)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(rule_tac cfg_sub_preserves_derivation_initialRM)
    apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
    apply(force)
   apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
   apply(force)
  apply(rename_tac d1 n1 \<delta>1 A1 y1 e1 e1' \<omega>1 d2 n2 \<delta>2 A2 y2 e2 e2' \<omega>2 v)(*strict*)
  apply(force)
  done

lemma cfg_sub_preserves_cfgRM_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgRM.derivation G d"
  apply(simp (no_asm) add: cfgRM.derivation_def cfgRM.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgRM.derivation_def cfgRM.derivation_initial_def)
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation SSG c1 e2 c2" for SSd SSn SSG)
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule cfgRM.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: cfgRM.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(simp add: cfg_sub_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 l r)(*strict*)
  apply(force)
  done

lemma cfg_sub_preserves_cfgRM_belongs: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G' d
  \<Longrightarrow> cfgRM.belongs G' d
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfgRM.belongs G d"
  apply(simp add: cfgRM.belongs_def cfg_sub_def)
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

lemma cfgRM_deri_can_be_decomposed: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> cfgRM.belongs G d
  \<Longrightarrow> d i = Some (pair ei \<lparr>cfg_conf=w1@w2\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair ej \<lparr>cfg_conf=liftB v\<rparr>)
  \<Longrightarrow> \<exists>v1 v2 d1 d2 e1 e2 n1 n2.
  v=v1@v2
  \<and> j=n1+n2
  \<and> cfgRM.derivation G d1
  \<and> cfgRM.derivation G d2
  \<and> cfgRM.belongs G d1
  \<and> cfgRM.belongs G d2
  \<and> (get_labels d2 n2)@(get_labels d1 n1)=drop i (get_labels d (i+j))
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
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = liftB l'a\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgRM.der1_belongs)
    apply(subgoal_tac "\<lparr>cfg_conf = liftB (l' @ l'a)\<rparr>\<in> cfg_configurations G")
     apply(rename_tac ej i l' l'a)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: simpY)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgRM.belongs_configurations)
     apply(rename_tac ej i l' l'a)(*strict*)
     apply(force)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(force)
   apply(rename_tac ej i l' l'a)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgRM.der1_belongs)
    apply(subgoal_tac "\<lparr>cfg_conf = liftB (l' @ l'a)\<rparr>\<in> cfg_configurations G")
     apply(rename_tac ej i l' l'a)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: simpY)
    apply(rename_tac ej i l' l'a)(*strict*)
    apply(rule cfgRM.belongs_configurations)
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac j ej w1 w2 v i ei)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+j)"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac j ej w1 w2 v i ei)(*strict*)
     apply(force)
    apply(rename_tac j ej w1 w2 v i ei)(*strict*)
    apply(force)
   apply(rename_tac j ej w1 w2 v i ei)(*strict*)
   apply(force)
  apply(rename_tac j ej w1 w2 v i ei)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej w1 w2 v i ei e2 c2)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
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
  apply(subgoal_tac "\<exists>l'. liftB l' = r")
   apply(rename_tac j ej w1 w2 va i ei l r A v)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB r"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac j ej w1 w2 va i ei l r A v)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej w1 w2 va i ei l A v l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(erule_tac
      x="ej"
      in meta_allE)
  apply(case_tac "prefix w1 l")
   apply(rename_tac j ej w1 w2 va i ei l A v l')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac j ej w1 va i ei A v l' c)(*strict*)
   apply(erule_tac
      x="w1"
      in meta_allE)
   apply(erule_tac
      x="c@v@liftB l'"
      in meta_allE)
   apply(erule_tac
      x="va"
      in meta_allE)
   apply(erule_tac
      x="Suc i"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule_tac
      x="v1"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="d1"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = c @ teA A # liftB l'\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = c @ v @ liftB l'\<rparr> ) d2 (Suc 0)"
      in exI)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule_tac
      x="e1"
      in exI)
   apply(rule_tac
      x="if n2=0 then Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr> else e2"
      in exI)
   apply(rule_tac
      x="n1"
      in exI)
   apply(rule_tac
      x="Suc 0+n2"
      in exI)
   apply(rule conjI)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(force)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation)
      apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
      apply(rule cfgRM.der2_is_derivation)
      apply(simp add: cfgRM_step_relation_def)
      apply(rule_tac
      x="c"
      in exI)
      apply(clarsimp)
      apply(rule setA_liftB)
     apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
     apply(force)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(rule cfgRM.derivation_belongs)
       apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
       apply(force)
      apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
      apply(simp add: derivation_append_def der2_def)
     apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
     apply(subgoal_tac "\<lparr>cfg_conf = w1 @ c @ teA A # liftB l'\<rparr> \<in> cfg_configurations G")
      apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
      apply(simp add: cfg_configurations_def)
      apply(simp add: simpY)
     apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
     apply(rule cfgRM.belongs_configurations)
      apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
      apply(force)
     apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
     apply(force)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(force)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def der2_def)
    apply(clarsimp)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = c @ teA A # liftB l'\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = c @ v @ liftB l'\<rparr>) d2 (Suc 0)) (Suc 0 + n2)"
      and s=" (get_labels (der2 \<lparr>cfg_conf = c @ teA A # liftB l'\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = c @ v @ liftB l'\<rparr>) (Suc 0)) @(get_labels d2 n2)"
      in ssubst)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(rule cfgRM.get_labels_concat2)
        apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
        apply(force)
       apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
       apply(rule cfgRM.der2_is_derivation)
       apply(simp add: cfgRM_step_relation_def)
       apply(rule_tac
      x="c"
      in exI)
       apply(clarsimp)
       apply(rule setA_liftB)
      apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
      apply(force)
     apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(force)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule_tac
      t="get_labels (der2 \<lparr>cfg_conf = c @ teA A # liftB l'\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = c @ v @ liftB l'\<rparr>) (Suc 0)"
      and s="[Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>]"
      in ssubst)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(rule der2_get_labels)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule_tac
      t="drop i (get_labels d (Suc (i + (n1 + n2))))"
      and s=" [Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>]@(drop (Suc i) (get_labels d (Suc (i + (n1 + n2))))) "
      in ssubst)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(thin_tac "get_labels d2 n2 @ get_labels d1 n1 = drop (Suc i) (get_labels d (Suc (i + (n1 + n2))))")
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="drop i (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc (i + (n1 + n2)))))"
      and s=" (map (\<lambda>i. get_label (d i)) (drop i (nat_seq (Suc 0) (Suc (i + (n1 + n2))))))"
      in ssubst)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(rule drop_map)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule_tac
      t=" drop (Suc i) (map (\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (Suc (i + (n1 + n2)))))) "
      and s="(map (\<lambda>i. get_label (d i)) (drop (Suc i) (nat_seq (Suc 0) (Suc (i + (n1 + n2))))))"
      in ssubst)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(rule drop_map)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(subgoal_tac "length (nat_seq (Suc 0) (Suc (i + (n1 + n2)))) = SSn + 1 - SSi" for SSn SSi)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    prefer 2
    apply(rule nat_seq_length_prime)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule listEqI)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(force)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2 ia)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc (i + (n1 + n2))) ! (i + ia) = (SSn)+(SSi)" for SSn SSi)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2 ia)(*strict*)
    prefer 2
    apply(rule nat_seq_nth_compute)
     apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2 ia)(*strict*)
     apply(force)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2 ia)(*strict*)
    apply(force)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2 ia)(*strict*)
   apply(clarsimp)
   apply(case_tac ia)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2 ia)(*strict*)
    apply(clarsimp)
    apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(simp add: get_label_def)
   apply(rename_tac ej w1 i ei A v l' c v1 v2 d1 d2 e1 e2 n1 n2 ia nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac j ej w1 w2 va i ei l A v l')(*strict*)
  apply(subgoal_tac "prefix w1 l \<or> prefix l w1")
   apply(rename_tac j ej w1 w2 va i ei l A v l')(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac j ej w1 w2 va i ei l A v l')(*strict*)
  apply(erule disjE)
   apply(rename_tac j ej w1 w2 va i ei l A v l')(*strict*)
   apply(force)
  apply(rename_tac j ej w1 w2 va i ei l A v l')(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac j ej w2 va i ei l A v l' c)(*strict*)
  apply(case_tac c)
   apply(rename_tac j ej w2 va i ei l A v l' c)(*strict*)
   apply(clarsimp)
  apply(rename_tac j ej w2 va i ei l A v l' c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej w2 va i ei l A v l' list)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = w2")
   apply(rename_tac j ej w2 va i ei l A v l' list)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB w2"
      in exI)
   apply (rule liftBDeConv2)
   apply (rule_tac
      a="l'"
      and b="list"
      and c="[]"
      in setA_liftB_substring)
   apply(force)
  apply(rename_tac j ej w2 va i ei l A v l' list)(*strict*)
  apply(erule exE)
  apply(rename_tac j ej w2 va i ei l A v l' list l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej va i ei l A v l' list l'a)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = list")
   apply(rename_tac j ej va i ei l A v l' list l'a)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB list"
      in exI)
   apply (rule liftBDeConv2)
   apply (rule_tac
      a="l'"
      and b="[]"
      and c="liftB l'a"
      in setA_liftB_substring)
   apply(force)
  apply(rename_tac j ej va i ei l A v l' list l'a)(*strict*)
  apply(erule exE)
  apply(rename_tac j ej va i ei l A v l' list l'a l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej va i ei l A v l' l'a l'b)(*strict*)
  apply(subgoal_tac "l'b@l'a=l'")
   apply(rename_tac j ej va i ei l A v l' l'a l'b)(*strict*)
   prefer 2
   apply(rule liftB_inj)
   apply(simp add: simpY)
  apply(rename_tac j ej va i ei l A v l' l'a l'b)(*strict*)
  apply(clarsimp)
  apply(rename_tac j ej va i ei l A v l'a l'b)(*strict*)
  apply(thin_tac "liftB l'b @ liftB l'a = liftB (l'b @ l'a)")
  apply(simp add: simpY)
  apply(erule_tac
      x="l @ v @ liftB l'b"
      in meta_allE)
  apply(erule_tac
      x="liftB l'a"
      in meta_allE)
  apply(erule_tac
      x="va"
      in meta_allE)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
  apply(subgoal_tac "n2=0")
   apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(clarsimp)
   apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(subgoal_tac "l'a=v2")
    apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 n1)(*strict*)
    prefer 2
    apply(rule liftB_inj)
    apply(force)
   apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(clarsimp)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule_tac
      x="v1"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="derivation_append (der2 \<lparr>cfg_conf = l @ teA A # liftB l'b\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = l @ v @ liftB l'b\<rparr> ) d1 (Suc 0)"
      in exI)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule_tac
      x="d2"
      in exI)
   apply(rule_tac
      x="if n1=0 then Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr> else e1"
      in exI)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule_tac
      x="Suc 0+n1"
      in exI)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule conjI)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(force)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(rule cfgRM.derivation_append_preserves_derivation)
      apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
      apply(rule cfgRM.der2_is_derivation)
      apply(simp add: cfgRM_step_relation_def)
      apply(rule_tac
      x="l"
      in exI)
      apply(clarsimp)
      apply(rule setA_liftB)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(force)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(simp add: der2_def)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(force)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(rule cfgRM.derivation_belongs)
       apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
       apply(force)
      apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
      apply(simp add: derivation_append_def der2_def)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(subgoal_tac "\<lparr>cfg_conf = l @ teA A # liftB l'b @ liftB v2\<rparr> \<in> cfg_configurations G")
      apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
      apply(simp add: cfg_configurations_def)
      apply(simp add: simpY)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(rule cfgRM.belongs_configurations)
      apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
      apply(force)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(force)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(force)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(force)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule conjI)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def der2_def)
    apply(clarsimp)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule_tac
      t="get_labels (derivation_append (der2 \<lparr>cfg_conf = l @ teA A # liftB l'b\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = l @ v @ liftB l'b\<rparr>) d1 (Suc 0)) (Suc 0 + n1)"
      and s=" (get_labels (der2 \<lparr>cfg_conf = l @ teA A # liftB l'b\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = l @ v @ liftB l'b\<rparr>) (Suc 0)) @(get_labels d1 n1)"
      in ssubst)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(rule cfgRM.get_labels_concat2)
        apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
        apply(force)
       apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
       apply(rule cfgRM.der2_is_derivation)
       apply(simp add: cfgRM_step_relation_def)
       apply(rule_tac
      x="l"
      in exI)
       apply(clarsimp)
       apply(rule setA_liftB)
      apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
      apply(force)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(force)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(rule_tac
      t="get_labels (der2 \<lparr>cfg_conf = l @ teA A # liftB l'b\<rparr> \<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<lparr>cfg_conf = l @ v @ liftB l'b\<rparr>) (Suc 0)"
      and s="[Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>]"
      in ssubst)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(rule der2_get_labels)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply(subgoal_tac "get_labels d2 0=[]")
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(clarsimp)
    apply(simp add: get_labels_def)
    apply(rule_tac
      t="drop i (map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (Suc (i + n1))))"
      and s=" (map (\<lambda>i. get_label (d i)) (drop i (nat_seq (Suc 0) (Suc (i + (n1 ))))))"
      in ssubst)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(rule drop_map)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(rule_tac
      t=" drop (Suc i) (map (\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (Suc (i + n1))))) "
      and s="(map (\<lambda>i. get_label (d i)) (drop (Suc i) (nat_seq (Suc 0) (Suc (i + (n1 ))))))"
      in ssubst)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(rule drop_map)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(subgoal_tac "length (nat_seq (Suc 0) (Suc (i + n1))) = SSn + 1 - SSi" for SSn SSi)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     prefer 2
     apply(rule nat_seq_length_prime)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
    apply(rule listEqI)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(force)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1 ia)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "nat_seq (Suc 0) (Suc (i + n1)) ! (i + ia) = (SSn)+(SSi)" for SSn SSi)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1 ia)(*strict*)
     prefer 2
     apply(rule nat_seq_nth_compute)
      apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1 ia)(*strict*)
      apply(force)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1 ia)(*strict*)
     apply(force)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1 ia)(*strict*)
    apply(clarsimp)
    apply(case_tac ia)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1 ia)(*strict*)
     apply(clarsimp)
     apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
     apply(simp add: get_label_def)
    apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1 ia nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac ej i ei l A v l'b v1 v2 d1 d2 e1 n1)(*strict*)
   apply (metis get_labelsEmpty)
  apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
  apply(rule_tac
      d="d2"
      and n="0"
      in cfgRM_no_step_without_nontermsX)
      apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
      apply(force)
     apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
     apply(force)
    apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(force)
   apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(clarsimp)
   apply(rule setA_liftB)
  apply(rename_tac ej i ei l A v l'a l'b v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
  apply(force)
  done

lemma CFGRM_terminals_stay_at_front: "
  valid_cfg G
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> setA v = {}
  \<Longrightarrow> d i = Some (pair e1 \<lparr>cfg_conf=v@w\<rparr>)
  \<Longrightarrow> d j = Some (pair e2 \<lparr>cfg_conf=x\<rparr>)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> prefix v x"
  apply(induct "j-i" arbitrary: j e2 x)
   apply(rename_tac j e2 x)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
  apply(rename_tac xa j e2 x)(*strict*)
  apply(clarsimp)
  apply(case_tac j)
   apply(rename_tac xa j e2 x)(*strict*)
   apply(force)
  apply(rename_tac xa j e2 x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e2 x nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> cfgRM_step_relation G c1 e2 c2")
   apply(rename_tac xa e2 x nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgRM.step_detail_before_some_position)
     apply(rename_tac xa e2 x nat)(*strict*)
     apply(force)
    apply(rename_tac xa e2 x nat)(*strict*)
    apply(force)
   apply(rename_tac xa e2 x nat)(*strict*)
   apply(force)
  apply(rename_tac xa e2 x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(erule_tac
      x="cfg_conf c1"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac xa x nat e1a e2a c1)(*strict*)
   apply(force)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa x nat e1a e2a c1)(*strict*)
   apply(force)
  apply(rename_tac xa x nat e1a e2a c1)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac xa x nat e1a e2a c1 c)(*strict*)
  apply(simp add: cfgRM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa nat e1a e2a c1 c l r)(*strict*)
  apply(case_tac "e2a")
  apply(rename_tac xa nat e1a e2a c1 c l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w1)
  apply(rename_tac xa nat e1a e2a c1 c l r A w1)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa nat e1a c1 c l r A w1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac xa nat e1a c1 c l r A w1 cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa nat e1a c l r A w1)(*strict*)
  apply(subgoal_tac "prefix v l \<or> prefix l v")
   apply(rename_tac xa nat e1a c l r A w1)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac xa nat e1a c l r A w1)(*strict*)
  apply(erule disjE)
   apply(rename_tac xa nat e1a c l r A w1)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac xa nat e1a c l r A w1)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac xa nat e1a c l r A w1 ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac xa nat e1a c l r A w1 ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa nat e1a c l r A w1 ca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa nat e1a c l A w1 list)(*strict*)
  apply(subgoal_tac "xa+i=nat")
   apply(rename_tac xa nat e1a c l A w1 list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa nat e1a c l A w1 list)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1a c l A w1 list)(*strict*)
  apply(simp add: simpY)
  done

end
