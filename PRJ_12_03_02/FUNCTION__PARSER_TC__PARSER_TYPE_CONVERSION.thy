section {*FUNCTION\_\_PARSER\_TC\_\_PARSER\_TYPE\_CONVERSION*}
theory
  FUNCTION__PARSER_TC__PARSER_TYPE_CONVERSION

imports
  PRJ_12_03_02__ENTRY

begin

theorem F_PARSER_TC__preserves_parser_no_top_rules: "
  valid_parser G
  \<Longrightarrow> parser_no_top_rules G
  \<Longrightarrow> parser_no_top_rules (F_PARSER_TC G)"
  apply(simp add: parser_no_top_rules_def F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TC__rule_def)
  done

theorem F_PARSER_TC__preserves_parser_not_observes_input_terminator: "
  valid_parser G
  \<Longrightarrow> parser_not_observes_input_terminator G
  \<Longrightarrow> parser_not_observes_input_terminator (F_PARSER_TC G)"
  apply(simp add: parser_not_observes_input_terminator_def F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TC__rule_def)
  done

definition F_PARSER_TC__ruleRev :: "
  ('stackB DT_symbol \<Rightarrow> 'stackA)
  \<Rightarrow> ('stackB DT_symbol, 'event) parser_step_label
  \<Rightarrow> ('stackA, 'event) parser_step_label"
  where
    "F_PARSER_TC__ruleRev fq e \<equiv>
  \<lparr>rule_lpop = map fq (rule_lpop e),
  rule_rpop = rule_rpop e,
  rule_lpush = map fq (rule_lpush e),
  rule_rpush = rule_rpush e\<rparr>"

definition F_PARSER_TCRRev :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event) parser_step_label
  \<Rightarrow> ('stackA, 'event) parser_step_label"
  where
    "F_PARSER_TCRRev G e \<equiv>
  F_PARSER_TC__ruleRev
    (inv_into (parser_nonterms G) (SOME f. inj_on f (parser_nonterms G)))
    e"

lemma rule_reversal: "
  valid_parser G
  \<Longrightarrow> x \<in> parser_rules G
  \<Longrightarrow> F_PARSER_TC__ruleRev (inv_into (parser_nonterms G) (SOME f. inj_on f (parser_nonterms G))) (F_PARSER_TC__rule (SOME f. inj_on f (parser_nonterms G)) x) = x"
  apply(simp add: F_PARSER_TC__ruleRev_def)
  apply(rule_tac
      t="\<lparr>rule_lpop = map (inv_into (parser_nonterms G) (SOME f. inj_on f (parser_nonterms G))) (rule_lpop (F_PARSER_TC__rule (SOME f. inj_on f (parser_nonterms G)) x)), rule_rpop = rule_rpop (F_PARSER_TC__rule (SOME f. inj_on f (parser_nonterms G)) x), rule_lpush = map (inv_into (parser_nonterms G) (SOME f. inj_on f (parser_nonterms G))) (rule_lpush (F_PARSER_TC__rule (SOME f. inj_on f (parser_nonterms G)) x)), rule_rpush = rule_rpush (F_PARSER_TC__rule (SOME f. inj_on f (parser_nonterms G)) x)\<rparr>"
      and s="x"
      in ssubst)
   prefer 2
   apply(force)
  apply(subgoal_tac "valid_parser_step_label G x")
   prefer 2
   apply(simp add: valid_parser_def)
  apply(simp add: valid_parser_step_label_def)
  apply(case_tac x)
  apply(rename_tac rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac rule_lpopa rule_lpusha rule_rpusha k w xb)(*strict*)
  apply(simp add: F_PARSER_TC__rule_def)
  apply(rename_tac rule_lpop rule_lpush rule_rpush k w xb)(*strict*)
  apply(rule conjI)
   apply(rename_tac rule_lpop rule_lpush rule_rpush k w xb)(*strict*)
   apply(rule inv_into_f_eq_map2)
    apply(rename_tac rule_lpop rule_lpush rule_rpush k w xb)(*strict*)
    apply (metis valid_parser_def SOME_injective_is_injective)
   apply(rename_tac rule_lpop rule_lpush rule_rpush k w xb)(*strict*)
   apply(force)
  apply(rename_tac rule_lpop rule_lpush rule_rpush k w xb)(*strict*)
  apply(rule inv_into_f_eq_map2)
   apply(rename_tac rule_lpop rule_lpush rule_rpush k w xb)(*strict*)
   apply (metis valid_parser_def SOME_injective_is_injective)
  apply(rename_tac rule_lpop rule_lpush rule_rpush k w xb)(*strict*)
  apply(force)
  done

lemma F_PARSER_TCRRev_preserves_edges: "
  valid_parser G
  \<Longrightarrow> e \<in> parser_rules (F_PARSER_TC G)
  \<Longrightarrow> F_PARSER_TCRRev G e \<in> parser_rules G"
  apply(simp add: F_PARSER_TCRRev_def)
  apply(simp add: F_PARSER_TC_def F_PARSER_TC__parser_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t="F_PARSER_TC__ruleRev (inv_into (parser_nonterms G) (SOME f. inj_on f (parser_nonterms G))) (F_PARSER_TC__rule (SOME f. inj_on f (parser_nonterms G)) x)"
      and s="x"
      in ssubst)
   apply(rename_tac x)(*strict*)
   apply(rule rule_reversal)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

definition F_PARSER_TC__parserC :: "
  ('stackA \<Rightarrow> 'stackB DT_symbol)
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf"
  where
    "F_PARSER_TC__parserC fq c \<equiv>
  \<lparr>parserHFS_conf_fixed = parserHFS_conf_fixed c,
  parserHFS_conf_history = parserHFS_conf_history c,
  parserHFS_conf_stack = map fq (parserHFS_conf_stack c),
  parserHFS_conf_scheduler = parserHFS_conf_scheduler c\<rparr>"

definition F_PARSER_TCC :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf"
  where
    "F_PARSER_TCC G c \<equiv>
  F_PARSER_TC__parserC (SOME f. inj_on f (parser_nonterms G)) c"

definition F_PARSER_TC__parserCRev :: "
  ('stackB DT_symbol \<Rightarrow> 'stackA)
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> ('stackA, 'event) parserHFS_conf"
  where
    "F_PARSER_TC__parserCRev fq c \<equiv>
  \<lparr>parserHFS_conf_fixed = parserHFS_conf_fixed c,
  parserHFS_conf_history = parserHFS_conf_history c,
  parserHFS_conf_stack = map fq (parserHFS_conf_stack c),
  parserHFS_conf_scheduler = parserHFS_conf_scheduler c\<rparr>"

definition F_PARSER_TCCRev :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> ('stackA, 'event) parserHFS_conf"
  where
    "F_PARSER_TCCRev G c \<equiv>
  F_PARSER_TC__parserCRev
    (inv_into (parser_nonterms G) (SOME f. inj_on f (parser_nonterms G)))
    c"

lemma PARSERToSymbolE_preserves_valid_parser_step_label: "
  valid_parser G
  \<Longrightarrow> e \<in> parser_rules G
  \<Longrightarrow> valid_parser_step_label G e
  \<Longrightarrow> G' = F_PARSER_TC__parser G fq
  \<Longrightarrow> inj_on fq (parser_nonterms G)
  \<Longrightarrow> e' = F_PARSER_TC__rule fq e
  \<Longrightarrow> valid_parser_step_label G' e'"
  apply(simp add: F_PARSER_TC__parser_def Let_def)
  apply(subgoal_tac "\<exists>f. inj_on f (parser_nonterms G) \<and> f = (SOME f::'a\<Rightarrow>'d DT_symbol. inj_on f (parser_nonterms G))")
   prefer 2
   apply(rule exists_SOME_injective_is_injective)
   apply(simp add: valid_parser_def)
  apply(erule exE)+
  apply(rename_tac f)(*strict*)
  apply(rule_tac
      t="(SOME f::'a \<Rightarrow> 'd DT_symbol. inj_on f (parser_nonterms G))"
      and s="f"
      in ssubst)
   apply(rename_tac f)(*strict*)
   apply(force)
  apply(rename_tac f)(*strict*)
  apply(erule conjE)
  apply(thin_tac "f = (SOME f. inj_on f (parser_nonterms G))")
  apply(simp add: valid_parser_def valid_parser_step_label_def F_PARSER_TC__rule_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac f)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac f)(*strict*)
  apply(clarsimp)
  apply(rename_tac f k w xa)(*strict*)
  apply(force)
  done

lemma F_PARSER_TC__parser_preserves_PDA: "
  valid_parser G
  \<Longrightarrow> inj_on fq (parser_nonterms G)
  \<Longrightarrow> valid_parser (F_PARSER_TC__parser G fq)"
  apply(simp add: valid_parser_def F_PARSER_TC__parser_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      G="G"
      in PARSERToSymbolE_preserves_valid_parser_step_label)
       apply(rename_tac x)(*strict*)
       apply(simp add: valid_parser_def)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_PARSER_TC__parser_def)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

theorem F_PARSER_TC__preserves_PARSER: "
  valid_parser G
  \<Longrightarrow> valid_parser (F_PARSER_TC G)"
  apply(simp add: F_PARSER_TC_def)
  apply(rule F_PARSER_TC__parser_preserves_PDA)
   apply(force)
  apply(rule SOME_injective_is_injective)
  apply(simp add: valid_parser_def valid_parser_def)
  done

theorem F_PARSER_TC__preserves_PARSERk: "
  valid_bounded_parser G k
  \<Longrightarrow> valid_bounded_parser (F_PARSER_TC G) k"
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TC__rule_def)
  apply(clarsimp)
  apply(simp add: F_PARSER_TC__rule_def)
  done

lemma F_PARSER_TC__parserC_preserves_configurations: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> inj_on fq (parser_nonterms G)
  \<Longrightarrow> F_PARSER_TC__parserC fq c \<in> parserHFS_configurations (F_PARSER_TC__parser G fq)"
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac f h l w)(*strict*)
  apply(simp add: F_PARSER_TC__parserC_def)
  apply(rule conjI)
   apply(rename_tac f h l w)(*strict*)
   apply(simp add: F_PARSER_TC__parser_def Let_def)
   apply(force)
  apply(rename_tac f h l w)(*strict*)
  apply(rule conjI)
   apply(rename_tac f h l w)(*strict*)
   apply(simp add: F_PARSER_TC__parser_def Let_def)
  apply(rename_tac f h l w)(*strict*)
  apply(rule conjI)
   apply(rename_tac f h l w)(*strict*)
   apply(simp add: F_PARSER_TC__parser_def Let_def)
  apply(rename_tac f h l w)(*strict*)
  apply(rule conjI)
   apply(rename_tac f h l w)(*strict*)
   apply(simp add: F_PARSER_TC__parser_def Let_def)
  apply(rename_tac f h l w)(*strict*)
  apply(simp add: F_PARSER_TC__parser_def Let_def)
  done

lemma F_PARSER_TC__parserC_preserves_initial_configurations: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHFS_initial_configurations G
  \<Longrightarrow> inj_on fq (parser_nonterms G)
  \<Longrightarrow> F_PARSER_TC__parserC fq c \<in> parserHFS_initial_configurations (F_PARSER_TC__parser G fq)"
  apply(simp add: parserHFS_initial_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_PARSER_TC__parserC_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_TC__parserC_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_TC__parserC_def)
   apply(simp add: F_PARSER_TC__parser_def Let_def)
  apply(rule F_PARSER_TC__parserC_preserves_configurations)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_PARSER_TC__parserC_preserves_marking_configurations: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHFS_marking_configurations G
  \<Longrightarrow> inj_on fq (parser_nonterms G)
  \<Longrightarrow> F_PARSER_TC__parserC fq c \<in> parserHFS_marking_configurations (F_PARSER_TC__parser G fq)"
  apply(simp add: parserHFS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac f w)(*strict*)
   apply(simp add: F_PARSER_TC__parserC_def)
   apply(simp add: F_PARSER_TC__parser_def Let_def)
  apply(rename_tac f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac f w)(*strict*)
   apply(simp add: F_PARSER_TC__parserC_def)
   apply(simp add: F_PARSER_TC__parser_def Let_def)
  apply(rename_tac f w)(*strict*)
  apply(rule F_PARSER_TC__parserC_preserves_configurations)
    apply(rename_tac f w)(*strict*)
    apply(force)
   apply(rename_tac f w)(*strict*)
   apply(force)
  apply(rename_tac f w)(*strict*)
  apply(force)
  done

definition F_PARSER_TC__relation_TSstructureLR :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_TSstructureLR G1 G2 \<equiv>
  valid_parser G1
  \<and> G2 = F_PARSER_TC G1"

definition F_PARSER_TC__relation_configurationLR :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_configurationLR G1 G2 c1 c2 \<equiv>
  F_PARSER_TC__relation_TSstructureLR G1 G2
  \<and> c1 \<in> parserHFS_configurations G1
  \<and> c2 = F_PARSER_TCC G1 c1"

definition F_PARSER_TC__relation_initial_configurationLR :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_initial_configurationLR G1 G2 c1 c2 \<equiv>
  F_PARSER_TC__relation_TSstructureLR G1 G2
  \<and> c1 \<in> parserHFS_initial_configurations G1
  \<and> c2 = F_PARSER_TCC G1 c1"

definition F_PARSER_TC__relation_effectLR :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_effectLR G1 G2 w1 w2 \<equiv>
  F_PARSER_TC__relation_TSstructureLR G1 G2
  \<and> w1 = w2"

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_PARSER_TC__relation_TSstructureLR G1) \<longrightarrow> valid_parser G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> valid_parser G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  apply(rule F_PARSER_TC__preserves_PARSER)
  apply(force)
  done

definition F_PARSER_TCR :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackA, 'event) parser_step_label
  \<Rightarrow> ('stackB DT_symbol, 'event) parser_step_label"
  where
    "F_PARSER_TCR G e \<equiv>
  F_PARSER_TC__rule
    (SOME f. inj_on f (parser_nonterms G))
    e"

definition F_PARSER_TC__relation_step_simulation :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> ('stackA, 'event) parser_step_label
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> (('stackB DT_symbol, 'event) parser_step_label, ('stackB DT_symbol, 'event) parserHFS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_step_simulation G1 G2 c1 e c1' c2 d \<equiv>
  d = der2 (F_PARSER_TCC G1 c1) (F_PARSER_TCR G1 e) (F_PARSER_TCC G1 c1')"

definition F_PARSER_TC__relation_initial_simulation :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> (('stackB DT_symbol, 'event) parser_step_label, ('stackB DT_symbol, 'event) parserHFS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_initial_simulation G1 G2 c1 d \<equiv>
  d = der1 (F_PARSER_TCC G1 c1)"

lemma F_PARSER_TC__C_preserves_configurations: "
  F_PARSER_TC__relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> parserHFS_configurations G1
  \<Longrightarrow> F_PARSER_TCC G1 c1 \<in> parserHFS_configurations G2"
  apply(simp add: F_PARSER_TCC_def F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(simp add: F_PARSER_TC_def)
  apply(rule F_PARSER_TC__parserC_preserves_configurations)
    apply(force)
   apply(force)
  apply(rule SOME_injective_is_injective)
  apply(simp add: valid_parser_def)
  done

lemma F_PARSER_TC__C_preserves_initial_configurations: "
  F_PARSER_TC__relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> parserHFS_initial_configurations G1
  \<Longrightarrow> F_PARSER_TCC G1 c1 \<in> parserHFS_initial_configurations G2"
  apply(simp add: F_PARSER_TCC_def F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(simp add: F_PARSER_TC_def)
  apply(rule F_PARSER_TC__parserC_preserves_initial_configurations)
    apply(force)
   apply(force)
  apply(rule SOME_injective_is_injective)
  apply(simp add: valid_parser_def valid_parser_def)
  done

lemma F_PARSER_TC__C_preserves_marking_configurations: "
  F_PARSER_TC__relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> parserHFS_marking_configurations G1
  \<Longrightarrow> F_PARSER_TCC G1 c1 \<in> parserHFS_marking_configurations G2"
  apply(simp add: F_PARSER_TCC_def F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(simp add: F_PARSER_TC_def)
  apply(rule F_PARSER_TC__parserC_preserves_marking_configurations)
    apply(force)
   apply(force)
  apply(rule SOME_injective_is_injective)
  apply(simp add: valid_parser_def valid_parser_def)
  done

lemma F_PARSER_TC__initial_simulation_preserves_derivation: "
  F_PARSER_TC__relation_TSstructureLR G1 G2
  \<Longrightarrow> c1 \<in> parserHFS_initial_configurations G1
  \<Longrightarrow> parserHFS.derivation_initial G2 (der1 (F_PARSER_TCC G1 c1))"
  apply(rule parserHFS.derivation_initialI)
   apply(rule parserHFS.der1_is_derivation)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rule F_PARSER_TC__C_preserves_initial_configurations)
   apply(force)
  apply(force)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_initial_simulation: "
  \<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> (\<exists>d2. parserHFS.derivation_initial G2 d2 \<and> F_PARSER_TC__relation_initial_configurationLR G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_PARSER_TC__relation_initial_simulation G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_PARSER_TC__relation_configurationLR G1 G2 c1 (the (get_configuration (d2 n))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_PARSER_TC__relation_initial_simulation_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_PARSER_TC__initial_simulation_preserves_derivation)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_PARSER_TC__relation_initial_configurationLR_def)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_PARSER_TC__relation_configurationLR_def)
  apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply(rename_tac G1 c1)
  apply (metis parserHFS_inst_AX_initial_configuration_belongs subset_eq)(*strict*)
  done

lemma F_PARSER_TC__preserves_step_relation: "
  parserHFS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> parserHFS_step_relation (F_PARSER_TC G1) (F_PARSER_TCC G1 c1) (F_PARSER_TCR G1 e1) (F_PARSER_TCC G1 c1')"
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa y)(*strict*)
  apply(rule conjI)
   apply(rename_tac x xa y)(*strict*)
   apply(simp add: F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TCR_def)
  apply(rename_tac x xa y)(*strict*)
  apply(rule conjI)
   apply(rename_tac x xa y)(*strict*)
   apply(simp add: F_PARSER_TCC_def F_PARSER_TCR_def F_PARSER_TC__parserC_def F_PARSER_TC__rule_def)
  apply(rename_tac x xa y)(*strict*)
  apply(rule_tac
      x="xa"
      in exI)
  apply(rule conjI)
   apply(rename_tac x xa y)(*strict*)
   apply(simp add: F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TCC_def F_PARSER_TCR_def F_PARSER_TC__parserC_def F_PARSER_TC__rule_def)
  apply(rename_tac x xa y)(*strict*)
  apply(rule conjI)
   apply(rename_tac x xa y)(*strict*)
   apply(simp add: F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TCC_def F_PARSER_TCR_def F_PARSER_TC__parserC_def F_PARSER_TC__rule_def)
  apply(rename_tac x xa y)(*strict*)
  apply(rule conjI)
   apply(rename_tac x xa y)(*strict*)
   apply(simp add: F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TCC_def F_PARSER_TCR_def F_PARSER_TC__parserC_def F_PARSER_TC__rule_def)
   apply(rule_tac
      x="y"
      in exI)
   apply(force)
  apply(rename_tac x xa y)(*strict*)
  apply(rule conjI)
   apply(rename_tac x xa y)(*strict*)
   apply(simp add: F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TCC_def F_PARSER_TCR_def F_PARSER_TC__parserC_def F_PARSER_TC__rule_def)
  apply(rename_tac x xa y)(*strict*)
  apply(simp add: F_PARSER_TCC_def F_PARSER_TCR_def F_PARSER_TC__parserC_def F_PARSER_TC__rule_def)
  done

lemma F_PARSER_TC__relation_step_simulation_maps_to_derivation: "
  F_PARSER_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_PARSER_TC__relation_configurationLR G1 G2 c1 c2
  \<Longrightarrow> parserHFS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> parserHFS.derivation G2 d2"
  apply(simp add: F_PARSER_TC__relation_step_simulation_def)
  apply(subgoal_tac "c1 \<in> parserHFS_configurations G1")
   prefer 2
   apply(simp add: F_PARSER_TC__relation_configurationLR_def)
  apply(clarsimp)
  apply(simp add: F_PARSER_TC__relation_configurationLR_def)
  apply(clarsimp)
  apply(rule parserHFS.der2_is_derivation)
  apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rule F_PARSER_TC__preserves_step_relation)
  apply(force)
  done

lemma F_PARSER_TC__relation_step_simulation_maps_to_derivation_belongs: "
  F_PARSER_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2
  \<Longrightarrow> F_PARSER_TC__relation_configurationLR G1 G2 c1 c2
  \<Longrightarrow> parserHFS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> parserHFS.belongs G2 d2"
  apply(simp add: F_PARSER_TC__relation_step_simulation_def)
  apply(rule parserHFS.der2_belongs_prime)
    prefer 3
    apply(rule F_PARSER_TC__relation_step_simulation_maps_to_derivation)
      apply(simp add: F_PARSER_TC__relation_step_simulation_def)
     apply(force)
    apply(force)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def F_PARSER_TC__relation_TSstructureLR_def)
   apply(clarsimp)
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(force)
  apply(simp add: F_PARSER_TC__relation_configurationLR_def)
  apply(clarsimp)
  apply(rule F_PARSER_TC__C_preserves_configurations)
   apply(force)
  apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs parserHFS.get_accessible_configurations_are_configurations subsetD)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. parserHFS.derivation G2 d2 \<and> parserHFS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_PARSER_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_PARSER_TC__relation_configurationLR G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_PARSER_TC__relation_step_simulation_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_PARSER_TC__relation_step_simulation_maps_to_derivation)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_PARSER_TC__relation_step_simulation_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule F_PARSER_TC__relation_step_simulation_maps_to_derivation_belongs)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: F_PARSER_TC__relation_step_simulation_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: der2_def get_configuration_def F_PARSER_TC__relation_configurationLR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: der2_def get_configuration_def F_PARSER_TC__relation_configurationLR_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs parserHFS.AX_step_relation_preserves_belongsC)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_parser parserHFS_initial_configurations parser_step_labels parserHFS_step_relation valid_parser parserHFS_configurations parserHFS_initial_configurations parser_step_labels parserHFS_step_relation F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_configurationLR F_PARSER_TC__relation_TSstructureLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_initial_simulation parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_step_simulation parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "parserHFS_parserHFS_F_PARSER_TC__StateSimLR" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserHFS_configurations"
  (* initial_configurations1 *)
  "parserHFS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserHFS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserHFS_marking_condition"
  (* marked_effect1 *)
  "parserHFS_marked_effect"
  (* unmarked_effect1 *)
  "parserHFS_unmarked_effect"
  (* TSstructure2 *)
  "valid_parser"
  (* configurations2 *)
  "parserHFS_configurations"
  (* initial_configurations2 *)
  "parserHFS_initial_configurations"
  (* step_labels2 *)
  "parser_step_labels"
  (* step_relation2 *)
  "parserHFS_step_relation"
  (* effects2 *)
  "parser_markers"
  (* marking_condition2 *)
  "parserHFS_marking_condition"
  (* marked_effect2 *)
  "parserHFS_marked_effect"
  (* unmarked_effect2 *)
  "parserHFS_unmarked_effect"
  (* relation_configuration *)
  "F_PARSER_TC__relation_configurationLR"
  (* relation_initial_configuration *)
  "F_PARSER_TC__relation_initial_configurationLR"
  (* relation_effect *)
  "F_PARSER_TC__relation_effectLR"
  (* relation_TSstructure *)
  "F_PARSER_TC__relation_TSstructureLR"
  (* relation_initial_simulation *)
  "F_PARSER_TC__relation_initial_simulation"
  (* relation_step_simulation *)
  "F_PARSER_TC__relation_step_simulation"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add:  parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_step_simulation_preserves_marking_condition: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> parserHFS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> parserHFS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: parserHFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(rename_tac cX)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(rule F_PARSER_TC__C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="Suc deri1n"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX y)(*strict*)
   apply(rule_tac
      x="deri2n+n"
      in exI)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def derivation_append_def get_configuration_def)
   apply(rule F_PARSER_TC__C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c cX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat nata)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_initial_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> parserHFS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> parserHFS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: parserHFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(rename_tac cX)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX y)(*strict*)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(rule F_PARSER_TC__C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(subgoal_tac "i=deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der1_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms parserHFS_initial_configurations parser_step_labels parserHFS_step_relation parserHFS_marking_condition parserHFS_initial_configurations parserHFS_step_relation parserHFS_marking_condition F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_configurationLR F_PARSER_TC__relation_TSstructureLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TC__relation_effectLR G1 G2) (parserHFS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (parserHFS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_PARSER_TC__relation_effectLR_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserHFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(rename_tac cX)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
    apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
   apply(rule F_PARSER_TC__C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="Suc deri1n"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX y)(*strict*)
   apply(rule_tac
      x="deri2n+n"
      in exI)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def derivation_append_def get_configuration_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
    apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply(rule F_PARSER_TC__C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c cX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat nata)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_initial_simulation_preserves_marked_effect: "
  \<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TC__relation_effectLR G1 G2) (parserHFS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (parserHFS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_PARSER_TC__relation_effectLR_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserHFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(rename_tac cX)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
    apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
   apply(rule F_PARSER_TC__C_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="Suc deri1n"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      x="deri2n+n"
      in exI)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(simp add: F_PARSER_TC__relation_initial_simulation_def)
   apply(subgoal_tac "n=0")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f e c cX)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(simp add: der1_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(case_tac n)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX nat)(*strict*)
   apply(simp add: der1_def maximum_of_domain_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX nat)(*strict*)
  apply(clarsimp)
  apply(simp add: der1_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms parserHFS_initial_configurations parser_step_labels parserHFS_step_relation parserHFS_marked_effect parserHFS_initial_configurations parserHFS_step_relation parserHFS_marked_effect F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_configurationLR F_PARSER_TC__relation_effectLR F_PARSER_TC__relation_TSstructureLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_initial_simulation_preserves_marked_effect)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__relation_configurationLR G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TC__relation_effectLR G1 G2) (parserHFS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (parserHFS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(simp add: F_PARSER_TC__relation_effectLR_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca caa e)(*strict*)
   apply(simp add: F_PARSER_TC__relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in parserHFS.some_position_has_details_at_0)
    apply (metis parserHFS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="F_PARSER_TCC G1 ca"
      in exI)
   apply(clarsimp)
   apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c ca)(*strict*)
  apply(rule_tac
      x="Suc deri2n"
      in exI)
  apply(simp add: derivation_append_def)
  apply(simp add: derivation_append_fit_def)
  apply(simp add: der2_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
  apply(simp add: F_PARSER_TC__relation_step_simulation_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
  apply(simp add: der2_def)
  apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect: "
  \<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationLR G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TC__relation_effectLR G1 G2) (parserHFS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (parserHFS_unmarked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(simp add: F_PARSER_TC__relation_effectLR_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca caa e)(*strict*)
   apply(simp add: F_PARSER_TC__relation_initial_configurationLR_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in parserHFS.some_position_has_details_at_0)
    apply (metis parserHFS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(clarsimp)
   apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms parserHFS_initial_configurations parser_step_labels parserHFS_step_relation parserHFS_unmarked_effect parserHFS_initial_configurations parserHFS_step_relation parserHFS_unmarked_effect F_PARSER_TC__relation_configurationLR F_PARSER_TC__relation_initial_configurationLR F_PARSER_TC__relation_effectLR F_PARSER_TC__relation_TSstructureLR F_PARSER_TC__relation_initial_simulation F_PARSER_TC__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "parserHFS_parserHFS_F_PARSER_TC__StateSimLR" : ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserHFS_configurations"
  (* initial_configurations1 *)
  "parserHFS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserHFS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserHFS_marking_condition"
  (* marked_effect1 *)
  "parserHFS_marked_effect"
  (* unmarked_effect1 *)
  "parserHFS_unmarked_effect"
  (* TSstructure2 *)
  "valid_parser"
  (* configurations2 *)
  "parserHFS_configurations"
  (* initial_configurations2 *)
  "parserHFS_initial_configurations"
  (* step_labels2 *)
  "parser_step_labels"
  (* step_relation2 *)
  "parserHFS_step_relation"
  (* effects2 *)
  "parser_markers"
  (* marking_condition2 *)
  "parserHFS_marking_condition"
  (* marked_effect2 *)
  "parserHFS_marked_effect"
  (* unmarked_effect2 *)
  "parserHFS_unmarked_effect"
  (* relation_configuration *)
  "F_PARSER_TC__relation_configurationLR"
  (* relation_initial_configuration *)
  "F_PARSER_TC__relation_initial_configurationLR"
  (* relation_effect *)
  "F_PARSER_TC__relation_effectLR"
  (* relation_TSstructure *)
  "F_PARSER_TC__relation_TSstructureLR"
  (* relation_initial_simulation *)
  "F_PARSER_TC__relation_initial_simulation"
  (* relation_step_simulation *)
  "F_PARSER_TC__relation_step_simulation"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms )
  done

lemma F_PARSER_TC__preserves_lang1: "
  valid_parser G
  \<Longrightarrow> parserHFS.marked_language G \<subseteq> parserHFS.marked_language (F_PARSER_TC G)"
  apply(rule_tac
      t="parserHFS.marked_language G"
      and s="parserHFS.finite_marked_language G"
      in ssubst)
   apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_PARSER_TC__relation_TSstructureLR_def Suc_n_not_n parserHFS.AX_marked_language_finite)
  apply(rule_tac
      t="parserHFS.marked_language (F_PARSER_TC G)"
      and s="parserHFS.finite_marked_language (F_PARSER_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule parserHFS.AX_marked_language_finite)
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(force)
  apply(subgoal_tac "left_total_on (F_PARSER_TC__relation_effectLR SSG1 SSG2) (parserHFS.finite_marked_language SSG1) (parserHFS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in parserHFS_parserHFS_F_PARSER_TC__StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_PARSER_TC__relation_effectLR_def)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(force)
  done

lemma F_PARSER_TC__preserves_unmarked_language1: "
  valid_parser G
  \<Longrightarrow> parserHFS.unmarked_language G \<subseteq> parserHFS.unmarked_language (F_PARSER_TC G)"
  apply(rule_tac
      t="parserHFS.unmarked_language G"
      and s="parserHFS.finite_unmarked_language G"
      in ssubst)
   apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_PARSER_TC__relation_TSstructureLR_def Suc_n_not_n parserHFS.AX_unmarked_language_finite)
  apply(rule_tac
      t="parserHFS.unmarked_language (F_PARSER_TC G)"
      and s="parserHFS.finite_unmarked_language (F_PARSER_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule parserHFS.AX_unmarked_language_finite)
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(force)
  apply(subgoal_tac "left_total_on (F_PARSER_TC__relation_effectLR SSG1 SSG2) (parserHFS.finite_unmarked_language SSG1) (parserHFS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      in parserHFS_parserHFS_F_PARSER_TC__StateSimLR.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   prefer 2
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_PARSER_TC__relation_effectLR_def)
  apply(force)
  done

definition F_PARSER_TC__relation_TSstructureRL :: "
  ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_TSstructureRL G2 G1 \<equiv>
  valid_parser G1
  \<and> G2 = F_PARSER_TC G1"

definition F_PARSER_TC__relation_configurationRL :: "
  ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_configurationRL G2 G1 c2 c1 \<equiv>
  F_PARSER_TC__relation_TSstructureRL G2 G1
  \<and> c1 \<in> parserHFS_configurations G1
  \<and> c2 = F_PARSER_TCC G1 c1"

definition F_PARSER_TC__relation_initial_configurationRL :: "
  ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_initial_configurationRL G2 G1 c2 c1 \<equiv>
  F_PARSER_TC__relation_TSstructureRL G2 G1
  \<and> c1 \<in> parserHFS_initial_configurations G1
  \<and> c2 = F_PARSER_TCC G1 c1"

definition F_PARSER_TC__relation_effectRL :: "
  ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event, 'marker) parser
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_effectRL G1 G2 w1 w2 \<equiv>
  F_PARSER_TC__relation_TSstructureRL G1 G2
  \<and> w1 = w2"

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_PARSER_TC__relation_TSstructureRL G1) \<longrightarrow> valid_parser G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac G2)(*strict*)
  apply(subgoal_tac "valid_parser (F_PARSER_TC G2)")
   apply(rename_tac G2)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac G2)(*strict*)
  apply(rule F_PARSER_TC__preserves_PARSER)
  apply(force)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> valid_parser G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
  done

definition F_PARSER_TC__relation_step_simulationRL :: "
  ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> ('stackB DT_symbol, 'event) parser_step_label
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> (('stackA, 'event) parser_step_label, ('stackA, 'event) parserHFS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_step_simulationRL G2 G1 c1 e c1' c2 d \<equiv>
  d = der2 (F_PARSER_TCCRev G1 c1) (F_PARSER_TCRRev G1 e) (F_PARSER_TCCRev G1 c1')"

definition F_PARSER_TC__relation_initial_simulationRL :: "
  ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> (('stackA, 'event) parser_step_label, ('stackA, 'event) parserHFS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__relation_initial_simulationRL G1 G2 c1 d \<equiv>
  d = der1 (F_PARSER_TCCRev G2 c1)"

lemma F_PARSER_TC__C_rev_preserves_configurations: "
  F_PARSER_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> parserHFS_configurations G1
  \<Longrightarrow> F_PARSER_TCCRev G2 c1 \<in> parserHFS_configurations G2"
  apply(simp add: parserHFS_configurations_def)
  apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac f h l w)(*strict*)
  apply(simp add: F_PARSER_TC_def F_PARSER_TCCRev_def F_PARSER_TC__parserCRev_def F_PARSER_TC__parser_def)
  apply(clarsimp)
  apply(rename_tac f h l w xa)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. l=w1@[xa]@w2")
   apply(rename_tac f h l w xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h w w1 w2 x)(*strict*)
   apply(rule_tac
      t="inv_into (parser_nonterms G2) (SOME f. inj_on f (parser_nonterms G2)) ((SOME f. inj_on f (parser_nonterms G2)) x)"
      and s="x"
      in ssubst)
    apply(rename_tac f h w w1 w2 x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f h w w1 w2 x)(*strict*)
   apply(rule inv_into_f_eq)
     apply(rename_tac f h w w1 w2 x)(*strict*)
     apply(rule SOME_injective_is_injective)
     apply(simp add: valid_parser_def valid_parser_def)
    apply(rename_tac f h w w1 w2 x)(*strict*)
    apply(force)
   apply(rename_tac f h w w1 w2 x)(*strict*)
   apply(force)
  apply(rename_tac f h l w xa)(*strict*)
  apply (metis ConsApp in_set_conv_decomp_first insert_Nil)
  done

lemma F_PARSER_TC__C_rev_preserves_initial_configurations: "
  F_PARSER_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> parserHFS_initial_configurations G1
  \<Longrightarrow> F_PARSER_TCCRev G2 c1 \<in> parserHFS_initial_configurations G2"
  apply(subgoal_tac "valid_parser (F_PARSER_TC G1)")
   prefer 2
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(force)
  apply(simp add: parserHFS_initial_configurations_def)
  apply(clarsimp)
  apply(rule propSym)
  apply(rule conjI)
   apply(rule propSym)
   apply(rule conjI)
    apply(rule propSym)
    apply(rule conjI)
     apply(rule F_PARSER_TC__C_rev_preserves_configurations)
      apply(force)
     apply(force)
    apply(simp add: F_PARSER_TCCRev_def valid_parser_def F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TC__relation_TSstructureRL_def)
    apply(case_tac c1)
    apply(simp add: F_PARSER_TC__parserCRev_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def inv_into_def)
    apply(clarsimp)
    apply(rule some_equality)
     apply(rule context_conjI)
      apply(force)
     apply(force)
    apply(rule_tac f="(SOME f. inj_on f (parser_nonterms G2))" in inj_onD)
       apply(rule SOME_injective_is_injective)
       apply(simp add: epdaS_epdaS_F_EPDA_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_EPDA_TC__relation_epda__LR_def valid_epda_def SOME_injective_is_injective)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: F_PARSER_TCCRev_def valid_parser_def F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TC__relation_TSstructureRL_def)
   apply(simp add: F_PARSER_TC__parserCRev_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def inv_into_def)
  apply(simp add: F_PARSER_TCCRev_def valid_parser_def F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TC__relation_TSstructureRL_def)
  apply(simp add: F_PARSER_TC__parserCRev_def F_EPDA_TC__epdaS_conf__LRRev_def F_EPDA_TC__epdaS_conf1__LRRev_def inv_into_def)
  done

lemma F_PARSER_TCC_reverse: "
  valid_parser G2
  \<Longrightarrow> c1 \<in> parserHFS_configurations (F_PARSER_TC G2)
  \<Longrightarrow> c1 = F_PARSER_TCC G2 (F_PARSER_TCCRev G2 c1)"
  apply(simp add: F_PARSER_TCC_def F_PARSER_TCCRev_def F_PARSER_TC__parserC_def F_PARSER_TC__parserCRev_def F_PARSER_TC_def F_PARSER_TC__parser_def parserHFS_initial_configurations_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac f h l w)(*strict*)
  apply(rule listEqI)
   apply(rename_tac f h l w)(*strict*)
   apply(clarsimp)
  apply(rename_tac f h l w i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w1 w2. l=w1@[l!i]@w2")
   apply(rename_tac f h l w i)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h l w i w1 w2)(*strict*)
   apply(subgoal_tac "l!i \<in> (SOME f. inj_on f (parser_nonterms G2)) ` parser_nonterms G2")
    apply(rename_tac f h l w i w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac f h w i w1 w2 x)(*strict*)
    apply (metis f_inv_into_f imageI)
   apply(rename_tac f h l w i w1 w2)(*strict*)
   apply(force)
  apply(rename_tac f h l w i)(*strict*)
  apply (metis ConsApp nth_take_drop_split)
  done

lemma F_PARSER_TCC_reverse2: "
  valid_parser G2
  \<Longrightarrow> c1 \<in> parserHFS_configurations G2
  \<Longrightarrow> c1 = F_PARSER_TCCRev G2 (F_PARSER_TCC G2 c1)"
  apply(simp add: F_PARSER_TCC_def F_PARSER_TCCRev_def F_PARSER_TC__parserC_def F_PARSER_TC__parserCRev_def F_PARSER_TC_def F_PARSER_TC__parser_def parserHFS_initial_configurations_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac f h l w)(*strict*)
  apply(rule listEqI)
   apply(rename_tac f h l w)(*strict*)
   apply(clarsimp)
  apply(rename_tac f h l w i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w1 w2. l=w1@[l!i]@w2")
   apply(rename_tac f h l w i)(*strict*)
   prefer 2
   apply (metis ConsApp nth_take_drop_split)
  apply(rename_tac f h l w i)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h l w i w1 w2)(*strict*)
  apply(subgoal_tac "l!i \<in> parser_nonterms G2")
   apply(rename_tac f h l w i w1 w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac f h l w i w1 w2)(*strict*)
  apply(rule sym)
  apply(rule inv_into_f_eq)
    apply(rename_tac f h l w i w1 w2)(*strict*)
    apply(rule SOME_injective_is_injective)
    apply(simp add: valid_parser_def valid_parser_def)
   apply(rename_tac f h l w i w1 w2)(*strict*)
   apply(force)
  apply(rename_tac f h l w i w1 w2)(*strict*)
  apply(force)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> (\<exists>d2. parserHFS.derivation_initial G2 d2 \<and> F_PARSER_TC__relation_initial_configurationRL G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_PARSER_TC__relation_initial_simulationRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_PARSER_TC__relation_configurationRL G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_PARSER_TC__relation_initial_simulationRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule parserHFS.derivation_initialI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule parserHFS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(rule F_PARSER_TC__C_rev_preserves_initial_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: F_PARSER_TC__relation_initial_configurationRL_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule F_PARSER_TC__C_rev_preserves_initial_configurations)
     apply(rename_tac G1 G2 c1)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
   apply(clarsimp)
   apply(rename_tac G2 c1)(*strict*)
   apply(rule F_PARSER_TCC_reverse)
    apply(rename_tac G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G2 c1)(*strict*)
   apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs F_PARSER_TC__relation_TSstructureLR_def parserHFS_inst_AX_initial_configuration_belongs subsetD)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  apply(simp add: F_PARSER_TC__relation_configurationRL_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule F_PARSER_TC__C_rev_preserves_configurations)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs F_PARSER_TC__relation_TSstructureLR_def F_PARSER_TC__relation_TSstructureRL_def parserHFS.AX_initial_configuration_belongs nset_mp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule F_PARSER_TCC_reverse)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
  apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure2_belongs F_PARSER_TC__relation_TSstructureLR_def F_PARSER_TC__relation_TSstructureRL_def parserHFS.AX_initial_configuration_belongs nset_mp)
  done

lemma F_PARSER_TCRev_preserves_step_relation: "
  F_PARSER_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> parserHFS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> parserHFS_step_relation G2 (F_PARSER_TCCRev G2 c1) (F_PARSER_TCRRev G2 e1) (F_PARSER_TCCRev G2 c1')"
  apply(simp add: parserHFS_step_relation_def F_PARSER_TCCRev_def F_PARSER_TC__relation_TSstructureRL_def F_PARSER_TC__parserCRev_def)
  apply(subgoal_tac "F_PARSER_TCRRev G2 e1 \<in> parser_rules G2")
   prefer 2
   apply(rule F_PARSER_TCRRev_preserves_edges)
    apply(simp add: valid_parser_def)
   apply(force)
  apply(subgoal_tac "valid_parser (F_PARSER_TC G2)")
   prefer 2
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(simp add: valid_parser_def)
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_TC G2) e1")
   prefer 2
   apply(simp add: valid_parser_def valid_parser_def)
   apply(force)
  apply(rule conjI)
   apply(simp add: valid_parser_step_label_def F_PARSER_TC_def F_PARSER_TC__parser_def)
  apply(rule conjI)
   prefer 2
   apply(clarsimp)
   apply(rename_tac x xa y)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x xa y)(*strict*)
    apply(simp add: F_PARSER_TCRRev_def F_PARSER_TC__ruleRev_def)
   apply(rename_tac x xa y)(*strict*)
   apply(rule conjI)
    apply(rename_tac x xa y)(*strict*)
    apply(simp add: F_PARSER_TCRRev_def F_PARSER_TC__ruleRev_def)
   apply(rename_tac x xa y)(*strict*)
   apply(rule conjI)
    apply(rename_tac x xa y)(*strict*)
    apply(simp add: F_PARSER_TCRRev_def F_PARSER_TC__ruleRev_def)
    apply(rule_tac
      x="y"
      in exI)
    apply(simp add: valid_parser_step_label_def F_PARSER_TC_def F_PARSER_TC__parser_def)
   apply(rename_tac x xa y)(*strict*)
   apply(rule conjI)
    apply(rename_tac x xa y)(*strict*)
    apply(simp add: valid_parser_step_label_def F_PARSER_TC_def F_PARSER_TC__parser_def)
    apply(simp add: F_PARSER_TCRRev_def F_PARSER_TC__ruleRev_def)
   apply(rename_tac x xa y)(*strict*)
   apply(simp add: valid_parser_step_label_def F_PARSER_TC_def F_PARSER_TC__parser_def)
   apply(simp add: F_PARSER_TCRRev_def F_PARSER_TC__ruleRev_def)
  apply(clarsimp)
  apply(rename_tac x xa y)(*strict*)
  apply(rule_tac
      x="map (inv_into (parser_nonterms G2) (SOME f. inj_on f (parser_nonterms G2))) x"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac x xa y)(*strict*)
   apply(simp add: valid_parser_step_label_def F_PARSER_TC_def F_PARSER_TC__parser_def)
   apply(simp add: F_PARSER_TCRRev_def F_PARSER_TC__ruleRev_def)
  apply(rename_tac x xa y)(*strict*)
  apply(simp add: valid_parser_step_label_def F_PARSER_TC_def F_PARSER_TC__parser_def)
  apply(simp add: F_PARSER_TCRRev_def F_PARSER_TC__ruleRev_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_step_relation_step_simulation: "
  \<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. parserHFS.derivation G2 d2 \<and> parserHFS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_PARSER_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_PARSER_TC__relation_configurationRL G1 G2 c1' (the (get_configuration (d2 n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_PARSER_TC__relation_step_simulationRL_def)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule parserHFS.der2_is_derivation)
   apply(rule F_PARSER_TCRev_preserves_step_relation)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(rule parserHFS.derivation_belongs)
      apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
      apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(rule F_PARSER_TC__C_rev_preserves_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
    apply(simp add: F_PARSER_TC__relation_configurationRL_def)
    apply(clarsimp)
    apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
    apply(rule F_PARSER_TC__C_preserves_configurations)
     apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
     apply(simp add: F_PARSER_TC__relation_TSstructureLR_def F_PARSER_TC__relation_TSstructureRL_def)
    apply(rename_tac G1 G2 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
   apply(simp add: get_configuration_def der2_def F_PARSER_TC__relation_configurationRL_def F_PARSER_TC__relation_TSstructureRL_def)
   apply(clarsimp)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(rule sym)
   apply(rule F_PARSER_TCC_reverse2)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(simp add: maximum_of_domain_def der2_def)
  apply(simp add: get_configuration_def F_PARSER_TC__relation_configurationRL_def F_PARSER_TC__relation_TSstructureRL_def)
  apply(clarsimp)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(subgoal_tac "valid_parser (F_PARSER_TC G2)")
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   prefer 2
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(force)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(rule F_PARSER_TC__C_rev_preserves_configurations)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(rule parserHFS.AX_step_relation_preserves_belongsC)
     apply(rename_tac G2 c2 e1 c1')(*strict*)
     apply(force)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(rule F_PARSER_TC__C_preserves_configurations)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(rule F_PARSER_TCC_reverse)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(rule parserHFS.AX_step_relation_preserves_belongsC)
    apply(rename_tac G2 c2 e1 c1')(*strict*)
    apply(simp add: valid_parser_def)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(rule F_PARSER_TC__C_preserves_configurations)
   apply(rename_tac G2 c2 e1 c1')(*strict*)
   apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  apply(rename_tac G2 c2 e1 c1')(*strict*)
  apply(force)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_parser parserHFS_initial_configurations parser_step_labels parserHFS_step_relation valid_parser parserHFS_configurations parserHFS_initial_configurations parser_step_labels parserHFS_step_relation F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_configurationRL F_PARSER_TC__relation_TSstructureRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_initial_simulation parserHFS_parserHFS_F_PARSER_TC__StateSimRL_step_relation_step_simulation parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs)
  done

interpretation "parserHFS_parserHFS_F_PARSER_TC__StateSimRL" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserHFS_configurations"
  (* initial_configurations1 *)
  "parserHFS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserHFS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserHFS_marking_condition"
  (* marked_effect1 *)
  "parserHFS_marked_effect"
  (* unmarked_effect1 *)
  "parserHFS_unmarked_effect"
  (* TSstructure2 *)
  "valid_parser"
  (* configurations2 *)
  "parserHFS_configurations"
  (* initial_configurations2 *)
  "parserHFS_initial_configurations"
  (* step_labels2 *)
  "parser_step_labels"
  (* step_relation2 *)
  "parserHFS_step_relation"
  (* effects2 *)
  "parser_markers"
  (* marking_condition2 *)
  "parserHFS_marking_condition"
  (* marked_effect2 *)
  "parserHFS_marked_effect"
  (* unmarked_effect2 *)
  "parserHFS_unmarked_effect"
  (* relation_configuration *)
  "F_PARSER_TC__relation_configurationRL"
  (* relation_initial_configuration *)
  "F_PARSER_TC__relation_initial_configurationRL"
  (* relation_effect *)
  "F_PARSER_TC__relation_effectRL"
  (* relation_TSstructure *)
  "F_PARSER_TC__relation_TSstructureRL"
  (* relation_initial_simulation *)
  "F_PARSER_TC__relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_PARSER_TC__relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_PARSER_TC__C_rev_preserves_marking_configurations: "
  F_PARSER_TC__relation_TSstructureRL G1 G2
  \<Longrightarrow> c1 \<in> parserHFS_marking_configurations G1
  \<Longrightarrow> F_PARSER_TCCRev G2 c1 \<in> parserHFS_marking_configurations G2"
  apply(simp add: parserHFS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac f w)(*strict*)
   apply(simp add: F_PARSER_TC__relation_TSstructureRL_def F_PARSER_TC_def F_PARSER_TCCRev_def F_PARSER_TC__parserCRev_def F_PARSER_TC__parser_def)
   apply(clarsimp)
   apply(rename_tac w x)(*strict*)
   apply(rule_tac
      t="inv_into (parser_nonterms G2) (SOME f. inj_on f (parser_nonterms G2)) ((SOME f. inj_on f (parser_nonterms G2)) x)"
      and s="x"
      in ssubst)
    apply(rename_tac w x)(*strict*)
    apply(rule inv_into_f_eq)
      apply(rename_tac w x)(*strict*)
      apply(rule SOME_injective_is_injective)
      apply(simp add: valid_parser_def valid_parser_def)
     apply(rename_tac w x)(*strict*)
     apply(simp add: valid_parser_def valid_parser_def)
     apply(force)
    apply(rename_tac w x)(*strict*)
    apply(force)
   apply(rename_tac w x)(*strict*)
   apply(force)
  apply(rename_tac f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac f w)(*strict*)
   apply(simp add: F_PARSER_TC__relation_TSstructureRL_def F_PARSER_TC_def F_PARSER_TCCRev_def F_PARSER_TC__parserCRev_def F_PARSER_TC__parser_def parserHFS_configurations_def)
  apply(rename_tac f w)(*strict*)
  apply(rule F_PARSER_TC__C_rev_preserves_configurations)
   apply(rename_tac f w)(*strict*)
   apply(force)
  apply(rename_tac f w)(*strict*)
  apply(force)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_step_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> parserHFS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> parserHFS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: parserHFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_PARSER_TC__relation_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_PARSER_TCCRev G2 ca"
      in ssubst)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(rule F_PARSER_TCC_reverse2)
     apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_PARSER_TC__C_rev_preserves_marking_configurations)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e)(*strict*)
    apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
    apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
    apply(clarsimp)
    apply(erule_tac
      x="Suc deri1n"
      in allE)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y)(*strict*)
    apply(rule_tac
      x="deri2n+n"
      in exI)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e option b)(*strict*)
    apply(rename_tac e c)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule_tac
      t="c"
      and s="F_PARSER_TCCRev G2 c1'"
      in ssubst)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(simp add: F_PARSER_TC__relation_configurationRL_def derivation_append_def get_configuration_def)
     apply(rule F_PARSER_TCC_reverse2)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
      apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(rule F_PARSER_TC__C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c)(*strict*)
   apply(simp add: F_PARSER_TC__relation_configurationRL_def derivation_append_def get_configuration_def F_PARSER_TC__relation_initial_configurationRL_def der2_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c nat nata)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_initial_simulation_preserves_marking_condition: "
  \<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> parserHFS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> parserHFS_marking_condition G2 (derivation_append deri2 d2 deri2n))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: parserHFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y)(*strict*)
   apply(simp add: F_PARSER_TC__relation_configurationRL_def)
   apply(clarsimp)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      t="c"
      and s="F_PARSER_TCCRev G2 ca"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(simp add: derivation_append_def get_configuration_def)
    apply(rule F_PARSER_TCC_reverse2)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
     apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(rule F_PARSER_TC__C_rev_preserves_marking_configurations)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "i=deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(case_tac "i>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der1_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms parserHFS_initial_configurations parser_step_labels parserHFS_step_relation parserHFS_marking_condition parserHFS_initial_configurations parserHFS_step_relation parserHFS_marking_condition F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_configurationRL F_PARSER_TC__relation_TSstructureRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TC__relation_effectRL G1 G2) (parserHFS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (parserHFS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_PARSER_TC__relation_effectRL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserHFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(rename_tac cX)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(thin_tac "derivation_append deri1 (der2 c1 e1 c1') deri1n i = Some (pair e c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: F_PARSER_TC__relation_configurationRL_def)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
    apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
   apply(rule_tac
      t="c"
      and s="F_PARSER_TCCRev G2 (F_PARSER_TCC G2 c)"
      in ssubst)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
    prefer 2
    apply(rule F_PARSER_TC__C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
   apply(rule F_PARSER_TCC_reverse2)
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
    apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(subgoal_tac "c=c1'")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="Suc deri1n"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX y)(*strict*)
   apply(rule_tac
      x="deri2n+n"
      in exI)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e cX option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply(simp add: F_PARSER_TC__relation_configurationLR_def derivation_append_def get_configuration_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
    apply(simp add: F_PARSER_TC__relation_configurationRL_def F_PARSER_TCC_def F_PARSER_TC__parserC_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply(rule_tac
      t="c"
      and s="F_PARSER_TCCRev G2 (F_PARSER_TCC G2 c)"
      in ssubst)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
    prefer 2
    apply(rule F_PARSER_TC__C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
    apply(simp add: F_PARSER_TC__relation_configurationRL_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply(rule F_PARSER_TCC_reverse2)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
    apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f ea cX e c)(*strict*)
   apply (metis F_PARSER_TC__relation_configurationRL_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat)(*strict*)
  apply(clarsimp)
  apply(case_tac nat)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i c cX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c cX nat nata)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_initial_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TC__relation_effectRL G1 G2) (parserHFS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (parserHFS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_PARSER_TC__relation_effectRL_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserHFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(rename_tac cX)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: F_PARSER_TC__relation_configurationRL_def)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca cX e c)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
    apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
   apply(rule_tac
      t="c"
      and s="F_PARSER_TCCRev G2 (F_PARSER_TCC G2 c)"
      in ssubst)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
    prefer 2
    apply(rule F_PARSER_TC__C_rev_preserves_marking_configurations)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
   apply(rule F_PARSER_TCC_reverse2)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
    apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea cX e c)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(erule_tac
      x="Suc deri1n"
      in allE)
   apply(clarsimp)
   apply(rule_tac
      x="deri2n+n"
      in exI)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(simp add: F_PARSER_TC__relation_initial_simulationRL_def)
   apply(subgoal_tac "n=0")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f e c cX)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(simp add: der1_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
   apply(case_tac n)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f e c cX nat)(*strict*)
   apply(simp add: der1_def maximum_of_domain_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(case_tac "i>Suc deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def der2_def)
  apply(case_tac "i-deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c cX nat)(*strict*)
  apply(clarsimp)
  apply(simp add: der1_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms parserHFS_initial_configurations parser_step_labels parserHFS_step_relation parserHFS_marked_effect parserHFS_initial_configurations parserHFS_step_relation parserHFS_marked_effect F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_configurationRL F_PARSER_TC__relation_effectRL F_PARSER_TC__relation_TSstructureRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_initial_simulation_preserves_marked_effect)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__relation_configurationRL G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TC__relation_effectRL G1 G2) (parserHFS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (parserHFS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(simp add: F_PARSER_TC__relation_effectRL_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_TC__relation_configurationRL_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea ca caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea caa e c)(*strict*)
   apply(simp add: F_PARSER_TC__relation_initial_configurationRL_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea caa e c)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in parserHFS.some_position_has_details_at_0)
    apply (metis parserHFS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ea caa e c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="f i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(subgoal_tac "i=Suc deri1n")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   prefer 2
   apply(case_tac "i>Suc deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f e c ca)(*strict*)
  apply(rule_tac
      x="Suc deri2n"
      in exI)
  apply(simp add: derivation_append_def)
  apply(simp add: derivation_append_fit_def)
  apply(simp add: der2_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 d2 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
  apply(simp add: F_PARSER_TC__relation_step_simulationRL_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 n deri1 deri1n deri2 deri2n f c ca)(*strict*)
  apply(simp add: der2_def)
  apply(simp add: F_PARSER_TCCRev_def F_PARSER_TC__parserCRev_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureRL G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TC__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserHFS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserHFS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TC__relation_initial_configurationRL G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TC__relation_effectRL G1 G2) (parserHFS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (parserHFS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(simp add: F_PARSER_TC__relation_effectRL_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
   prefer 2
   apply(rule_tac
      M="G2"
      in parserHFS.some_position_has_details_at_0)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(case_tac "i\<le>deri1n")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(subgoal_tac "deri1 i = Some (pair e c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
    prefer 2
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_def)
   apply(clarsimp)
   apply(simp add: parserHFS_parserHFS_F_PARSER_TC__StateSimRL.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_TC__relation_configurationRL_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca option b)(*strict*)
   apply(rename_tac e c)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea ca caa e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea caa e c)(*strict*)
   apply(simp add: F_PARSER_TC__relation_initial_configurationRL_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea caa e c)(*strict*)
    prefer 2
    apply(rule_tac
      M="G1"
      in parserHFS.some_position_has_details_at_0)
    apply (metis parserHFS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i ea caa e c)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="f i"
      in exI)
   apply(clarsimp)
   apply(simp add: F_PARSER_TCC_def F_PARSER_TC__parserC_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f i e c ca)(*strict*)
  apply(simp add: derivation_append_def der1_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms parserHFS_initial_configurations parser_step_labels parserHFS_step_relation parserHFS_unmarked_effect parserHFS_initial_configurations parserHFS_step_relation parserHFS_unmarked_effect F_PARSER_TC__relation_configurationRL F_PARSER_TC__relation_initial_configurationRL F_PARSER_TC__relation_effectRL F_PARSER_TC__relation_TSstructureRL F_PARSER_TC__relation_initial_simulationRL F_PARSER_TC__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserHFS_parserHFS_F_PARSER_TC__StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

interpretation "parserHFS_parserHFS_F_PARSER_TC__StateSimRL" : ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserHFS_configurations"
  (* initial_configurations1 *)
  "parserHFS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserHFS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserHFS_marking_condition"
  (* marked_effect1 *)
  "parserHFS_marked_effect"
  (* unmarked_effect1 *)
  "parserHFS_unmarked_effect"
  (* TSstructure2 *)
  "valid_parser"
  (* configurations2 *)
  "parserHFS_configurations"
  (* initial_configurations2 *)
  "parserHFS_initial_configurations"
  (* step_labels2 *)
  "parser_step_labels"
  (* step_relation2 *)
  "parserHFS_step_relation"
  (* effects2 *)
  "parser_markers"
  (* marking_condition2 *)
  "parserHFS_marking_condition"
  (* marked_effect2 *)
  "parserHFS_marked_effect"
  (* unmarked_effect2 *)
  "parserHFS_unmarked_effect"
  (* relation_configuration *)
  "F_PARSER_TC__relation_configurationRL"
  (* relation_initial_configuration *)
  "F_PARSER_TC__relation_initial_configurationRL"
  (* relation_effect *)
  "F_PARSER_TC__relation_effectRL"
  (* relation_TSstructure *)
  "F_PARSER_TC__relation_TSstructureRL"
  (* relation_initial_simulation *)
  "F_PARSER_TC__relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_PARSER_TC__relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add:  parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ANY_axioms parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_COND_axioms parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_ATS_Simulation_Configuration_WeakRL_ACCEPT_axioms  parserHFS_parserHFS_F_PARSER_TC__StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma F_PARSER_TC__preserves_lang2: "
  valid_parser G
  \<Longrightarrow> parserHFS.marked_language G \<supseteq> parserHFS.marked_language (F_PARSER_TC G)"
  apply(rule_tac
      t="parserHFS.marked_language G"
      and s="parserHFS.finite_marked_language G"
      in ssubst)
   apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_PARSER_TC__relation_TSstructureLR_def parserHFS_inst_lang_finite)
  apply(rule_tac
      t="parserHFS.marked_language (F_PARSER_TC G)"
      and s="parserHFS.finite_marked_language (F_PARSER_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule parserHFS.AX_marked_language_finite)
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(force)
  apply(subgoal_tac "left_total_on (F_PARSER_TC__relation_effectRL SSG1 SSG2) (parserHFS.finite_marked_language SSG1) (parserHFS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in parserHFS_parserHFS_F_PARSER_TC__StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_PARSER_TC__relation_effectRL_def)
  done

lemma F_PARSER_TC__preserves_unmarked_language2: "
  valid_parser G
  \<Longrightarrow> parserHFS.unmarked_language G \<supseteq> parserHFS.unmarked_language (F_PARSER_TC G)"
  apply(rule_tac
      t="parserHFS.unmarked_language G"
      and s="parserHFS.finite_unmarked_language G"
      in ssubst)
   apply (metis parserHFS_parserHFS_F_PARSER_TC__StateSimLR_inst_AX_TSstructure_relation_TSstructure1_belongs F_PARSER_TC__relation_TSstructureLR_def parserHFS_inst_AX_unmarked_language_finite n_not_Suc_n)
  apply(rule_tac
      t="parserHFS.unmarked_language (F_PARSER_TC G)"
      and s="parserHFS.finite_unmarked_language (F_PARSER_TC G)"
      in ssubst)
   apply(rule sym)
   apply(rule parserHFS.AX_unmarked_language_finite)
   apply(rule F_PARSER_TC__preserves_PARSER)
   apply(force)
  apply(subgoal_tac "left_total_on (F_PARSER_TC__relation_effectRL SSG1 SSG2) (parserHFS.finite_unmarked_language SSG1) (parserHFS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule_tac
      ?G2.0="G"
      in parserHFS_parserHFS_F_PARSER_TC__StateSimRL.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x b)(*strict*)
  apply(simp add: F_PARSER_TC__relation_effectRL_def)
  done

theorem F_PARSER_TC__preserves_lang: "
  valid_parser G
  \<Longrightarrow> parserHFS.marked_language G = parserHFS.marked_language (F_PARSER_TC G)"
  apply(rule order_antisym)
   apply (metis F_PARSER_TC__preserves_lang1)
  apply (metis F_PARSER_TC__preserves_lang2)
  done

theorem F_PARSER_TC__preserves_unmarked_language: "
  valid_parser G
  \<Longrightarrow> parserHFS.unmarked_language G = parserHFS.unmarked_language (F_PARSER_TC G)"
  apply(rule order_antisym)
   apply (metis F_PARSER_TC__preserves_unmarked_language1)
  apply (metis F_PARSER_TC__preserves_unmarked_language2)
  done

lemma F_PARSER_TC__preserves_parser_no_empty_steps_from_marking_states: "
  valid_parser M
  \<Longrightarrow> parser_no_empty_steps_from_marking_states M
  \<Longrightarrow> R = F_PARSER_TC M
  \<Longrightarrow> parser_no_empty_steps_from_marking_states R"
  apply(simp add: parser_no_empty_steps_from_marking_states_def F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TC__rule_def)
  apply(clarsimp)
  apply(simp add: F_PARSER_TC__rule_def)
  apply(rename_tac x xa)(*strict*)
  apply(erule_tac
      x="x"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      xs="rule_lpop x"
      in rev_cases)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa ys y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "y=xa")
   apply(rename_tac x xa ys y)(*strict*)
   apply(force)
  apply(rename_tac x xa ys y)(*strict*)
  apply(subgoal_tac "\<exists>f. inj_on f (parser_nonterms M) \<and> f = (SOME f::'a\<Rightarrow>'d DT_symbol. inj_on f (parser_nonterms M))")
   apply(rename_tac x xa ys y)(*strict*)
   prefer 2
   apply(rule exists_SOME_injective_is_injective)
   apply(simp add: valid_parser_def)
  apply(rename_tac x xa ys y)(*strict*)
  apply(rule Fun.inj_onD)
     apply(rename_tac x xa ys y)(*strict*)
     apply(force)
    apply(rename_tac x xa ys y)(*strict*)
    apply(force)
   apply(rename_tac x xa ys y)(*strict*)
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac x xa ys y)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac x xa ys y)(*strict*)
   apply(force)
  apply(rename_tac x xa ys y)(*strict*)
  apply(clarsimp)
  apply(simp add: valid_parser_def)
  apply(force)
  done

definition F_PARSER_TC__ISOM_relation_label :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event) parser_step_label
  \<Rightarrow> ('stackB DT_symbol, 'event) parser_step_label
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__ISOM_relation_label G1 G2 p1 p2 \<equiv>
  p1 \<in> parser_rules G1
  \<and> p2 \<in> parser_rules G2
  \<and> F_PARSER_TC__rule
      (SOME f. inj_on f (parser_nonterms G1))
      p1
    = p2"

definition F_PARSER_TC__ISOM_relation_conf :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__ISOM_relation_conf G1 G2 c1 c2 \<equiv>
  c1 \<in> parserHFS_configurations G1
  \<and> c2 \<in> parserHFS_configurations G2
  \<and> c2 = F_PARSER_TCC G1 c1"

definition F_PARSER_TC__ISOM_relation_initial_conf :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB DT_symbol, 'event, nat option) parser
  \<Rightarrow> ('stackA, 'event) parserHFS_conf
  \<Rightarrow> ('stackB DT_symbol, 'event) parserHFS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__ISOM_relation_initial_conf G1 G2 c1 c2 \<equiv>
  c1 \<in> parserHFS_initial_configurations G1
  \<and> c2 \<in> parserHFS_initial_configurations G2
  \<and> c2 = F_PARSER_TCC G1 c1"

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_TSstructure_closed1: "
  (\<forall>G1. Ex (F_PARSER_TC__relation_TSstructureLR G1) \<longrightarrow> valid_parser G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_TSstructure_closed2: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> valid_parser G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1)(*strict*)
  apply (metis F_PARSER_TC__preserves_PARSER)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_closed1: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1. Ex (F_PARSER_TC__ISOM_relation_conf G1 G2 c1) \<longrightarrow> c1 \<in> parserHFS_configurations G1))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 x)(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_conf_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_closed2: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> c2 \<in> parserHFS_configurations G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_for_initial_closed1: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> c1 \<in> parserHFS_initial_configurations G1 \<longrightarrow> c2 \<in> parserHFS_initial_configurations G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_conf_def F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply(metis F_PARSER_TC__C_preserves_initial_configurations F_PARSER_TC__relation_TSstructureLR_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_for_initial_closed2: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> c2 \<in> parserHFS_initial_configurations G2 \<longrightarrow> c1 \<in> parserHFS_initial_configurations G1))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_conf_def F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply (metis (poly_guards_query) F_PARSER_TCC_reverse2 F_PARSER_TC__C_rev_preserves_initial_configurations F_PARSER_TC__relation_TSstructureRL_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_label_closed1: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>e1. Ex (F_PARSER_TC__ISOM_relation_label G1 G2 e1) \<longrightarrow> e1 \<in> parser_step_labels G1))"
  apply(clarsimp)
  apply(rename_tac G1 G2 e1 x)(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_label_def parser_step_labels_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_label_closed2: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>e1 e2. F_PARSER_TC__ISOM_relation_label G1 G2 e1 e2 \<longrightarrow> e2 \<in> parser_step_labels G2))"
  apply(clarsimp)
  apply(rename_tac G1 G2 e1 e2)(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_label_def parser_step_labels_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_bijection_on: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> bijection_on (F_PARSER_TC__ISOM_relation_conf G1 G2) (parserHFS_configurations G1) (parserHFS_configurations G2) )"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(rule bijection_on_intro)
     apply(rename_tac G1 G2)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 a)(*strict*)
     apply(simp add: F_PARSER_TC__ISOM_relation_conf_def F_PARSER_TC__relation_TSstructureLR_def)
     apply(clarsimp)
     apply(rename_tac G1 a)(*strict*)
     apply (metis (mono_tags, hide_lams) F_PARSER_TC__C_preserves_configurations F_PARSER_TC__relation_TSstructureLR_def)
    apply(rename_tac G1 G2)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 b)(*strict*)
    apply(simp add: F_PARSER_TC__relation_TSstructureLR_def F_PARSER_TC__ISOM_relation_conf_def)
    apply(clarsimp)
    apply(rename_tac G1 b)(*strict*)
    apply(rule_tac
      x="F_PARSER_TCCRev G1 b"
      in bexI)
     apply(rename_tac G1 b)(*strict*)
     apply (metis F_PARSER_TCC_reverse)
    apply(rename_tac G1 b)(*strict*)
    apply (metis F_PARSER_TC__C_rev_preserves_configurations F_PARSER_TC__relation_TSstructureRL_def)
   apply(rename_tac G1 G2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 a b1 b2)(*strict*)
   apply(simp add: F_PARSER_TC__ISOM_relation_conf_def)
  apply(rename_tac G1 G2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 b a1 a2)(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 a1 a2)(*strict*)
  apply (metis F_PARSER_TCC_reverse2 F_PARSER_TC__relation_TSstructureLR_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_label_bijection_on: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> bijection_on (F_PARSER_TC__ISOM_relation_label G1 G2) (parser_step_labels G1) (parser_step_labels G2) )"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(rule bijection_on_intro)
     apply(rename_tac G1 G2)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 a)(*strict*)
     apply(simp add: F_PARSER_TC__ISOM_relation_label_def F_PARSER_TC__relation_TSstructureLR_def parser_step_labels_def F_PARSER_TC_def F_PARSER_TC__parser_def)
    apply(rename_tac G1 G2)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 b)(*strict*)
    apply(simp add: F_PARSER_TC__ISOM_relation_label_def F_PARSER_TC__relation_TSstructureLR_def parser_step_labels_def)
    apply(clarsimp)
    apply(rename_tac G1 b)(*strict*)
    apply(rule_tac
      x="F_PARSER_TC__ruleRev ((inv_into (parser_nonterms G1) (SOME f. inj_on f (parser_nonterms G1)))) b"
      in bexI)
     apply(rename_tac G1 b)(*strict*)
     prefer 2
     apply (metis F_PARSER_TCRRev_def F_PARSER_TCRRev_preserves_edges)
    apply(rename_tac G1 b)(*strict*)
    apply(simp add: F_PARSER_TC_def F_PARSER_TC__parser_def)
    apply(clarsimp)
    apply(rename_tac G1 x)(*strict*)
    apply(rule_tac
      t="F_PARSER_TC__ruleRev (inv_into (parser_nonterms G1) (SOME f. inj_on f (parser_nonterms G1))) (F_PARSER_TC__rule (SOME f. inj_on f (parser_nonterms G1)) x)"
      and s="x"
      in ssubst)
     apply(rename_tac G1 x)(*strict*)
     apply(rule rule_reversal)
      apply(rename_tac G1 x)(*strict*)
      apply(simp add: valid_pda_def)
     apply(rename_tac G1 x)(*strict*)
     apply(force)
    apply(rename_tac G1 x)(*strict*)
    apply(simp add: F_PARSER_TC__rule_def)
   apply(rename_tac G1 G2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 a b1 b2)(*strict*)
   apply(simp add: F_PARSER_TC__ISOM_relation_label_def)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_label_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 a1 a2)(*strict*)
  apply (metis F_PARSER_TC__relation_TSstructureLR_def rule_reversal)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_marking_configuration1_equivalent: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>d1. parserHFS.derivation_initial G1 d1 \<longrightarrow> parserHFS_marking_condition G1 d1 = (\<exists>i c1. get_configuration (d1 i) = Some c1 \<and> c1 \<in> parserHFS_marking_configurations G1)))"
  apply(clarsimp)
  apply(rename_tac G1 d1)(*strict*)
  apply(simp add: parserHFS_marking_condition_def)
  apply(rule antisym)
   apply(rename_tac G1 d1)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d1 i e c)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 d1)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d1 i c1)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(simp add: get_configuration_def)
  apply(case_tac "d1 i")
   apply(rename_tac G1 d1 i c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d1 i c1 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G1 d1 i c1 a option conf)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_preserves_marking_configuration: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> (c1 \<in> parserHFS_marking_configurations G1) = (c2 \<in> parserHFS_marking_configurations G2)))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(rule antisym)
   apply(rename_tac G1 G2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: F_PARSER_TC__ISOM_relation_conf_def)
   apply (metis F_PARSER_TC__C_preserves_marking_configurations)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: F_PARSER_TC__ISOM_relation_conf_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply (metis F_PARSER_TCC_reverse2 F_PARSER_TC__C_rev_preserves_marking_configurations F_PARSER_TC__relation_TSstructureLR_def F_PARSER_TC__relation_TSstructureRL_def)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_step_preservation1: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> (\<forall>e1 c1'. parserHFS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>e2. F_PARSER_TC__ISOM_relation_label G1 G2 e1 e2 \<longrightarrow> (\<forall>c2'. F_PARSER_TC__ISOM_relation_conf G1 G2 c1' c2' \<longrightarrow> parserHFS_step_relation G2 c2 e2 c2')))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' e2 c2')(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_label_def F_PARSER_TC__ISOM_relation_conf_def F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply (metis F_PARSER_TCR_def F_PARSER_TC__preserves_step_relation)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_step_preservation2: "
  (\<forall>G1 G2. F_PARSER_TC__relation_TSstructureLR G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TC__ISOM_relation_conf G1 G2 c1 c2 \<longrightarrow> (\<forall>e2 c2'. parserHFS_step_relation G2 c2 e2 c2' \<longrightarrow> (\<forall>e1. F_PARSER_TC__ISOM_relation_label G1 G2 e1 e2 \<longrightarrow> (\<forall>c1'. F_PARSER_TC__ISOM_relation_conf G1 G2 c1' c2' \<longrightarrow> parserHFS_step_relation G1 c1 e1 c1')))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e2 c2' e1 c1')(*strict*)
  apply(simp add: F_PARSER_TC__ISOM_relation_label_def F_PARSER_TC__ISOM_relation_conf_def F_PARSER_TC__relation_TSstructureLR_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   prefer 2
   apply(rule F_PARSER_TCRev_preserves_step_relation)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(simp add: F_PARSER_TC__relation_TSstructureRL_def)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule_tac
      t="c1"
      and s="(F_PARSER_TCCRev G1 (F_PARSER_TCC G1 c1))"
      in ssubst)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply (simp add: F_PARSER_TCC_reverse2)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule_tac
      t="c1'"
      and s="(F_PARSER_TCCRev G1 (F_PARSER_TCC G1 c1'))"
      in ssubst)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply (simp add: F_PARSER_TCC_reverse2)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(rule_tac
      t="e1"
      and s=" (F_PARSER_TCRRev G1 (F_PARSER_TC__rule (SOME f. inj_on f (parser_nonterms G1)) e1))"
      in ssubst)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(simp add: F_PARSER_TC__ISOM_relation_label_def F_PARSER_TC__relation_TSstructureLR_def parser_step_labels_def F_PARSER_TC_def F_PARSER_TC__parser_def F_PARSER_TCRRev_def)
   apply(rule sym)
   apply(rule rule_reversal)
    apply(rename_tac G1 c1 e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 c1 e1 c1')(*strict*)
  apply(force)
  done

lemma parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_ATS_Isomorphism_axioms: "
  ATS_Isomorphism_axioms valid_parser parserHFS_configurations parserHFS_initial_configurations parser_step_labels parserHFS_step_relation parserHFS_marking_condition valid_parser parserHFS_configurations parserHFS_initial_configurations parser_step_labels parserHFS_step_relation parserHFS_marking_condition (\<lambda>G c. c \<in> parserHFS_marking_configurations G) (\<lambda>G c. c \<in> parserHFS_marking_configurations G) F_PARSER_TC__relation_TSstructureLR F_PARSER_TC__ISOM_relation_conf F_PARSER_TC__ISOM_relation_label"
  apply(simp add: ATS_Isomorphism_axioms_def)
  apply(simp add: parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_TSstructure_closed1 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_TSstructure_closed2 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_closed1 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_closed2 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_for_initial_closed1 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_for_initial_closed2 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_label_closed1 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_label_closed2 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_bijection_on parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_label_bijection_on parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_marking_configuration1_equivalent parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_relation_configuration_preserves_marking_configuration parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_step_preservation1 parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_AX_step_preservation2 )
  done

interpretation "parserHFS_parserHFS_F_PARSER_TC__ISOM" : ATS_Isomorphism
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserHFS_configurations"
  (* initial_configurations1 *)
  "parserHFS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserHFS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserHFS_marking_condition"
  (* marked_effect1 *)
  "parserHFS_marked_effect"
  (* unmarked_effect1 *)
  "parserHFS_unmarked_effect"
  (* TSstructure2 *)
  "valid_parser"
  (* configurations2 *)
  "parserHFS_configurations"
  (* initial_configurations2 *)
  "parserHFS_initial_configurations"
  (* step_labels2 *)
  "parser_step_labels"
  (* step_relation2 *)
  "parserHFS_step_relation"
  (* effects2 *)
  "parser_markers"
  (* marking_condition2 *)
  "parserHFS_marking_condition"
  (* marked_effect2 *)
  "parserHFS_marked_effect"
  (* unmarked_effect2 *)
  "parserHFS_unmarked_effect"
  (* marking_configuration1 *)
  "(\<lambda>G c. c \<in> parserHFS_marking_configurations G)"
  (* marking_configuration2 *)
  "(\<lambda>G c. c \<in> parserHFS_marking_configurations G)"
  (* relation_TSstructure *)
  "F_PARSER_TC__relation_TSstructureLR"
  (* relation_configuration *)
  "F_PARSER_TC__ISOM_relation_conf"
  (* relation_label *)
  "F_PARSER_TC__ISOM_relation_label"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_parserHFS_F_PARSER_TC__ISOM_inst_ATS_Isomorphism_axioms)
  done

theorem F_PARSER_TC__preserves_is_forward_edge_deterministic_accessible: "
  valid_parser G
  \<Longrightarrow> parserHFS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> parserHFS.is_forward_edge_deterministic_accessible (F_PARSER_TC G)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?G1.0="G"
      and ?G2.0="F_PARSER_TC G"
      in parserHFS_parserHFS_F_PARSER_TC__ISOM.is_forward_edge_deterministic_accessible_preservation)
    apply(simp add: F_PARSER_TC__relation_TSstructureLR_def)
   apply(force)
  apply(force)
  done

definition F_PARSER_TC__SpecInput :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__SpecInput G \<equiv>
  valid_bounded_parser G (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible G
  \<and> parser_not_observes_input_terminator G
  \<and> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<and> parser_no_top_rules G
  \<and> parser_no_empty_steps_from_marking_states G"

definition F_PARSER_TC__SpecOutput :: "
  ('stackA, 'event, 'marker) parser
  \<Rightarrow> ('stackB, 'event, nat option) parser
  \<Rightarrow> bool"
  where
    "F_PARSER_TC__SpecOutput Gi Go \<equiv>
  valid_bounded_parser Go (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible Go
  \<and> parser_not_observes_input_terminator Go
  \<and> parser_no_top_rules Go
  \<and> parserS.marked_language Gi = parserS.marked_language Go
  \<and> nonblockingness_language (parserS.unmarked_language Go) (parserS.marked_language Go)
  \<and> parser_no_empty_steps_from_marking_states Go"

theorem F_PARSER_TC__SOUND: "
  F_PARSER_TC__SpecInput G
  \<Longrightarrow> F_PARSER_TC__SpecOutput G (F_PARSER_TC G)"
  apply(simp add: F_PARSER_TC__SpecInput_def F_PARSER_TC__SpecOutput_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rule F_PARSER_TC__preserves_PARSERk)
   apply(force)
  apply(rule context_conjI)
   apply(rule_tac
      ?G1.0="F_PARSER_TC G"
      in parserS_vs_parserFS.preserve_FEdetermR1)
    apply(simp add: valid_bounded_parser_def)
   apply(rule_tac
      ?G1.0="F_PARSER_TC G"
      in parserS_vs_parserHFS.preserve_FEdetermR2)
    apply(simp add: valid_bounded_parser_def)
   apply(rule F_PARSER_TC__preserves_is_forward_edge_deterministic_accessible)
    apply(simp add: valid_bounded_parser_def)
   apply(rule_tac
      ?G2.0="G"
      in parserS_vs_parserHFS.preserve_FEdetermR1)
    apply(simp add: valid_bounded_parser_def)
    apply(force)
   apply(rule_tac
      ?G2.0="G"
      in parserS_vs_parserFS.preserve_FEdetermR2)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(rule context_conjI)
   apply(rule_tac
      G="G"
      in F_PARSER_TC__preserves_parser_not_observes_input_terminator)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(rule context_conjI)
   apply(rule_tac
      G="G"
      in F_PARSER_TC__preserves_parser_no_top_rules)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(subgoal_tac "(parserHFS.Nonblockingness_linear_DB SSG \<longleftrightarrow> parserS.Nonblockingness_linear_DB SSG) \<and> parserHFS.unmarked_language SSG = parserS.unmarked_language SSG \<and> parserHFS.marked_language SSG = parserS.marked_language SSG" for SSG)
   prefer 2
   apply(rule_tac
      G="G"
      in parserS_vs_parserHFS_Nonblockingness_and_lang_transfer)
   apply(simp add: valid_bounded_parser_def)
  apply(subgoal_tac "(parserHFS.Nonblockingness_linear_DB SSG \<longleftrightarrow> parserS.Nonblockingness_linear_DB SSG) \<and> parserHFS.unmarked_language SSG = parserS.unmarked_language SSG \<and> parserHFS.marked_language SSG = parserS.marked_language SSG" for SSG)
   prefer 2
   apply(rule_tac
      G="F_PARSER_TC G"
      in parserS_vs_parserHFS_Nonblockingness_and_lang_transfer)
   apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(rule context_conjI)
   apply(rule_tac
      t="parserS.marked_language G"
      and s="parserHFS.marked_language G"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="parserS.marked_language (F_PARSER_TC G)"
      and s="parserHFS.marked_language (F_PARSER_TC G)"
      in subst)
    apply(force)
   apply(rule_tac
      G="G"
      in F_PARSER_TC__preserves_lang)
   apply(simp add: valid_bounded_parser_def)
  apply(subgoal_tac "parserS.unmarked_language G = parserS.unmarked_language (F_PARSER_TC G)")
   prefer 2
   apply(rule_tac
      t="parserS.unmarked_language G"
      and s="parserHFS.unmarked_language G"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="parserS.unmarked_language (F_PARSER_TC G)"
      and s="parserHFS.unmarked_language (F_PARSER_TC G)"
      in subst)
    apply(force)
   apply(rule_tac
      G="G"
      in F_PARSER_TC__preserves_unmarked_language)
   apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(rule_tac
      M="G"
      in F_PARSER_TC__preserves_parser_no_empty_steps_from_marking_states)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(force)
  done

end
