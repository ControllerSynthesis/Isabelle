section {*FUNCTION\_\_PARSER\_TO\_EDPDA*}
theory
  FUNCTION__PARSER_TO_EDPDA

imports
  PRJ_12_07_01__ENTRY

begin

definition F_PARSER_TO_EDPDA__rules_rev :: "
  ('stack, 'event, 'stack) epda_step_label
  \<Rightarrow> ('stack, 'event) parser_step_label"
  where
    "F_PARSER_TO_EDPDA__rules_rev e \<equiv>
  \<lparr>rule_lpop = rev (edge_pop e) @ [edge_src e],
  rule_rpop = option_to_list (edge_event e),
  rule_lpush = rev (edge_push e) @ [edge_trg e],
  rule_rpush = []\<rparr>"

definition F_PARSER_TO_EDPDA__configuration :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> 'stack
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf"
  where
    "F_PARSER_TO_EDPDA__configuration G c BOX \<equiv>
  \<lparr>epdaS_conf_state = last (parserS_conf_stack c),
  epdaS_conf_scheduler = butlast_if_match (parserS_conf_scheduler c) (parser_bottom G),
  epdaS_conf_stack = rev (butlast (parserS_conf_stack c)) @ [BOX]\<rparr>"

definition F_PARSER_TO_EDPDA__configuration_rev :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event) parserS_conf"
  where
    "F_PARSER_TO_EDPDA__configuration_rev G c \<equiv>
  \<lparr>parserS_conf_stack =
      (if epdaS_conf_stack c = []
      then []
      else rev (butlast (epdaS_conf_stack c)))
    @ [epdaS_conf_state c],
  parserS_conf_scheduler = epdaS_conf_scheduler c @ [parser_bottom G]\<rparr>"

lemma F_PARSER_TO_EDPDA__configuration_rev_F_PARSER_TO_EDPDA__configuration: "
  parserS_conf_stack c \<noteq> []
  \<Longrightarrow> \<exists>w. parserS_conf_scheduler c = w @ [parser_bottom G]
  \<Longrightarrow> F_PARSER_TO_EDPDA__configuration_rev G (F_PARSER_TO_EDPDA__configuration G c BOX) = c"
  apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def F_PARSER_TO_EDPDA__configuration_def)
  apply(case_tac c)
  apply(rename_tac parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac parserS_conf_stack w)(*strict*)
  apply (metis butlast_if_match_direct)
  done

lemma F_PARSER_TO_EDPDA__configuration_F_PARSER_TO_EDPDA__configuration_rev: "
  epdaS_conf_stack c \<noteq> []
  \<Longrightarrow> last (epdaS_conf_stack c) = BOX
  \<Longrightarrow> F_PARSER_TO_EDPDA__configuration G (F_PARSER_TO_EDPDA__configuration_rev G c) BOX = c"
  apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def F_PARSER_TO_EDPDA__configuration_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
  apply (metis butlast_if_match_direct)
  done

definition F_PARSER_TO_EDPDA__SpecInput1 :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'stack
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__SpecInput1 G BOX \<equiv>
  valid_parser G
  \<and> (\<forall>r \<in> parser_rules G.
      rule_rpush r = []
      \<and> length (rule_rpop r) \<le> Suc 0
      \<and> rule_lpop r \<noteq> []
      \<and> rule_lpush r \<noteq> [])
  \<and> BOX \<notin> parser_nonterms G"

lemma F_PARSER_TO_EDPDA__rules_rev_F_PARSER_TO_EDPDA__rules: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> e \<in> parser_rules G
  \<Longrightarrow> F_PARSER_TO_EDPDA__rules_rev (F_PARSER_TO_EDPDA__rules e) = e"
  apply(simp add: F_PARSER_TO_EDPDA__rules_rev_def F_PARSER_TO_EDPDA__rules_def)
  apply(case_tac e)
  apply(rename_tac rule_lpopa rule_rpopa rule_lpusha rule_rpush)(*strict*)
  apply(clarsimp)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(rename_tac rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>rule_lpop = rule_lpopa, rule_rpop = rule_rpopa, rule_lpush = rule_lpusha, rule_rpush = rule_rpusha\<rparr>"
      in ballE)
   apply(rename_tac rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   prefer 2
   apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
   apply(force)
  apply(rename_tac rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
  apply(simp add: option_to_list_def list_to_option_def)
  apply(case_tac "rule_rpop")
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(clarsimp)
  apply(rename_tac rule_lpop rule_rpop rule_lpush a list)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_TO_EDPDA__rules_F_PARSER_TO_EDPDA__rules_rev: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> e \<in> epda_delta (F_PARSER_TO_EDPDA G BOX)
  \<Longrightarrow> F_PARSER_TO_EDPDA__rules (F_PARSER_TO_EDPDA__rules_rev e) = e"
  apply(simp add: F_PARSER_TO_EDPDA__rules_rev_def F_PARSER_TO_EDPDA__rules_def)
  apply(case_tac e)
  apply(rename_tac edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(clarsimp)
  apply(rename_tac edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(simp add: option_to_list_def list_to_option_def)
  apply(case_tac "edge_event")
   apply(rename_tac edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
   apply(clarsimp)
  apply(rename_tac edge_src edge_event edge_pop edge_push edge_trg a)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_TO_EDPDA__SpecInput1_implies_never_fixed: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parserS.derivation_initial G d
  \<Longrightarrow> parser_fixed_input_length_recN d n = 0"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc n)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
   apply(rename_tac n a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac n a)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: parserS_step_relation_def)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_TO_EDPDA__SpecInput1_implies_parser_not_observes_input_terminator: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parser_not_observes_input_terminator G"
  apply(simp add: parser_not_observes_input_terminator_def F_PARSER_TO_EDPDA__SpecInput1_def)
  done

lemma F_PARSER_TO_EDPDA_generates_epda: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> valid_epda (F_PARSER_TO_EDPDA G BOX)"
  apply(subgoal_tac "parser_not_observes_input_terminator G")
   prefer 2
   apply(rule F_PARSER_TO_EDPDA__SpecInput1_implies_parser_not_observes_input_terminator)
   apply(force)
  apply(simp add: valid_epda_def F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(rule conjI)
   apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rule conjI)
   apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rule conjI)
   apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rule conjI)
   apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rule conjI)
   apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rule conjI)
   apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rule conjI)
   apply(simp add: valid_parser_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__rules_def F_PARSER_TO_EDPDA_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__rules_def F_PARSER_TO_EDPDA_def)
  apply(simp add: valid_epda_step_label_def)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x k w)(*strict*)
   apply (metis last_in_set_X)
  apply(rename_tac x)(*strict*)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x k w)(*strict*)
   apply(simp add: option_to_set_def list_to_option_def kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x k w)(*strict*)
    apply(clarsimp)
    apply(case_tac "take k w")
     apply(rename_tac x k w)(*strict*)
     apply(force)
    apply(rename_tac x k w a list)(*strict*)
    apply(clarsimp)
    apply (metis last_in_set_X)
   apply(rename_tac x k w nat)(*strict*)
   apply(clarsimp)
  apply(simp add: parser_not_observes_input_terminator_def)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(simp add: valid_parser_step_label_def option_to_set_def list_to_option_def)
   apply(clarsimp)
   apply(rename_tac x xa k w)(*strict*)
   apply(case_tac "kPrefix k (w @ [parser_bottom G])")
    apply(rename_tac x xa k w)(*strict*)
    apply(force)
   apply(rename_tac x xa k w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x k w a)(*strict*)
   apply(simp add: kPrefix_def)
   apply(simp add: valid_parser_def)
   apply(case_tac "k-length w")
    apply(rename_tac x k w a)(*strict*)
    apply(clarsimp)
    apply (metis DiffE List.set_simps(2) kPrefix_def set_kPrefix_subset set_subset_in)
   apply(rename_tac x k w a nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac x k w)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x k w)(*strict*)
    prefer 2
    apply(rename_tac x k w nat)(*strict*)
    apply(force)
   apply(rename_tac x k w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="rev (butlast (rule_lpop x))"
      in exI)
   apply(clarsimp)
   apply(rename_tac x k w xa)(*strict*)
   apply (metis in_set_butlastD subsetE)
  apply(rename_tac x)(*strict*)
  apply(rule conjI)
   apply(rename_tac x)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(simp add: may_terminated_by_def kleene_star_def append_language_def)
   apply(clarsimp)
   apply(rename_tac x k w)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x k w)(*strict*)
    prefer 2
    apply(rename_tac x k w nat)(*strict*)
    apply(force)
   apply(rename_tac x k w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="rev (butlast (rule_lpush x))"
      in exI)
   apply(clarsimp)
   apply(rename_tac x k w xa)(*strict*)
   apply (metis in_set_butlastD subsetE)
  apply(rename_tac x)(*strict*)
  apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x a)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x a k w)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x a k w)(*strict*)
    prefer 2
    apply(rename_tac x a k w nat)(*strict*)
    apply(force)
   apply(rename_tac x a k w)(*strict*)
   apply(clarsimp)
   apply (metis in_set_butlastD set_append2 set_rev set_subset_in subsetE)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x a)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x a k w)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac x a k w)(*strict*)
   prefer 2
   apply(rename_tac x a k w nat)(*strict*)
   apply(force)
  apply(rename_tac x a k w)(*strict*)
  apply(clarsimp)
  apply (metis in_set_butlastD set_append2 set_rev set_subset_in subsetE)
  done

lemma F_PARSER_TO_EDPDA__configuration_reflects_steps: "
  e1 \<in> parser_rules G1
  \<Longrightarrow> parserS_step_relation G1 c1 e1 c1'
  \<Longrightarrow> c1 \<in> parserS.get_accessible_configurations G1
  \<Longrightarrow> F_PARSER_TO_EDPDA__SpecInput1 G1 BOX
  \<Longrightarrow> epdaS_step_relation (F_PARSER_TO_EDPDA G1 BOX) (F_PARSER_TO_EDPDA__configuration G1 c1 BOX) (F_PARSER_TO_EDPDA__rules e1) (F_PARSER_TO_EDPDA__configuration G1 c1' BOX)"
  apply(subgoal_tac "c1 \<in> parserS_configurations G1")
   prefer 2
   apply(simp add: parserS.get_accessible_configurations_def)
   apply(clarsimp)
   apply(rename_tac d i)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d i")
    apply(rename_tac d i)(*strict*)
    apply(clarsimp)
   apply(rename_tac d i a)(*strict*)
   apply(case_tac a)
   apply(rename_tac d i a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i option)(*strict*)
   apply(rule parserS.belongs_configurations)
    apply(rename_tac d i option)(*strict*)
    apply(rule parserS.derivation_initial_belongs)
     apply(rename_tac d i option)(*strict*)
     apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
    apply(rename_tac d i option)(*strict*)
    apply(force)
   apply(rename_tac d i option)(*strict*)
   apply(force)
  apply(subgoal_tac "valid_parser_step_label G1 e1")
   prefer 2
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def valid_parser_def)
  apply(simp add: epdaS_step_relation_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
   apply(simp add: F_PARSER_TO_EDPDA__rules_def)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
   apply(simp add: F_PARSER_TO_EDPDA__rules_def)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
   apply(simp add: F_PARSER_TO_EDPDA__rules_def)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
   apply(rename_tac x xa k w wa xc)(*strict*)
   apply(case_tac xa)
    apply(rename_tac x xa k w wa xc)(*strict*)
    apply(clarsimp)
    apply(rename_tac x k w wa xc)(*strict*)
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(case_tac "k-length w")
     apply(rename_tac x k w wa xc)(*strict*)
     apply(clarsimp)
     apply (metis F_PARSER_TO_EDPDA__SpecInput1_def Suc_length Zero_not_Suc append_Nil2 list.size(3))
    apply(rename_tac x k w wa xc nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac x k w xc nat xa)(*strict*)
    apply(rule_tac
      t="butlast_if_match (w @ [parser_bottom G1]) (parser_bottom G1)"
      and s="w"
      in ssubst)
     apply(rename_tac x k w xc nat xa)(*strict*)
     apply (metis butlast_if_match_direct)
    apply(rename_tac x k w xc nat xa)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(rename_tac x xa k w wa xc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac x xa k w wa xc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x xa k w wa xc a list)(*strict*)
   apply(thin_tac "xa=a#list")
   apply(clarsimp)
   apply(rename_tac x k w xc w')(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(clarsimp)
   apply(rename_tac x k w w')(*strict*)
   apply(rule_tac
      t="butlast_if_match (kPrefix k (w @ [parser_bottom G1]) @ w' @ [parser_bottom G1]) (parser_bottom G1)"
      and s="kPrefix k (w @ [parser_bottom G1]) @ w'"
      in ssubst)
    apply(rename_tac x k w w')(*strict*)
    apply (metis butlast_if_match_direct butlast_if_match_pull_out_prime)
   apply(rename_tac x k w w')(*strict*)
   apply(rule_tac
      t="butlast_if_match (w' @ [parser_bottom G1]) (parser_bottom G1)"
      and s="w'"
      in ssubst)
    apply(rename_tac x k w w')(*strict*)
    apply (metis butlast_if_match_direct)
   apply(rename_tac x k w w')(*strict*)
   apply(clarsimp)
   apply(simp add: kPrefix_def)
   apply(clarsimp)
   apply(case_tac "k-length w")
    apply(rename_tac x k w w')(*strict*)
    prefer 2
    apply(rename_tac x k w w' nat)(*strict*)
    apply(force)
   apply(rename_tac x k w w')(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="e1"
      in ballE)
    apply(rename_tac x k w w')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x k w w')(*strict*)
   apply(clarsimp)
   apply(case_tac "w")
    apply(rename_tac x k w w')(*strict*)
    apply(simp add: option_to_list_def list_to_option_def)
   apply(rename_tac x k w w' a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x k w' a list)(*strict*)
   apply(case_tac k)
    apply(rename_tac x k w' a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x w' a list)(*strict*)
    apply(simp add: option_to_list_def list_to_option_def)
   apply(rename_tac x k w' a list nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x w' a list nat)(*strict*)
   apply(simp add: option_to_list_def list_to_option_def)
   apply(clarsimp)
   apply (metis List.length_take length_0_conv list.size(3) take_all_length)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
  apply(simp add: F_PARSER_TO_EDPDA__rules_def)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x xa k w xc)(*strict*)
  apply(case_tac "rule_lpush e1")
   apply(rename_tac x xa k w xc)(*strict*)
   apply(force)
  apply(rename_tac x xa k w xc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. rule_lpush e1 = w' @ [x']")
   apply(rename_tac x xa k w xc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xa k w xc a list)(*strict*)
  apply(thin_tac "rule_lpush e1=a#list")
  apply(clarsimp)
  apply(rename_tac x xa k w xc w' x')(*strict*)
  apply(case_tac "rule_lpop e1")
   apply(rename_tac x xa k w xc w' x')(*strict*)
   apply(force)
  apply(rename_tac x xa k w xc w' x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. rule_lpop e1 = w' @ [x']")
   apply(rename_tac x xa k w xc w' x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xa k w xc w' x' a list)(*strict*)
  apply(thin_tac "rule_lpop e1=a#list")
  apply(clarsimp)
  apply(rename_tac x xa k w xc w' x' w'a x'a)(*strict*)
  apply(rule_tac
      t="butlast (x @ w'a @ [x'a])"
      and s="x @ w'a"
      in ssubst)
   apply(rename_tac x xa k w xc w' x' w'a x'a)(*strict*)
   apply (metis butlast_snoc_2)
  apply(rename_tac x xa k w xc w' x' w'a x'a)(*strict*)
  apply(rule_tac
      t="butlast (x @ w' @ [x'])"
      and s="x @ w'"
      in ssubst)
   apply(rename_tac x xa k w xc w' x' w'a x'a)(*strict*)
   apply (metis butlast_snoc_2)
  apply(rename_tac x xa k w xc w' x' w'a x'a)(*strict*)
  apply(rule_tac
      x="rev x@[BOX]"
      in exI)
  apply (metis NoteAboutRev append_Cons rev_append)
  done

lemma F_PARSER_TO_EDPDA__SpecInput1_never_empty_lhs: "
  e1 \<in> parser_rules G1
  \<Longrightarrow> F_PARSER_TO_EDPDA__SpecInput1 G1 BOX
  \<Longrightarrow> parserS.derivation_initial G1 d
  \<Longrightarrow> d i = Some (pair option c1)
  \<Longrightarrow> parserS_conf_stack c1 \<noteq> []"
  apply(induct i arbitrary: option c1)
   apply(rename_tac option c1)(*strict*)
   apply(simp add: parserS.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac c1)(*strict*)
   apply(simp add: parserS_initial_configurations_def)
  apply(rename_tac i option c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option c1)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserS_step_relation G1 c1 e2 c2")
   apply(rename_tac i option c1)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserS.step_detail_before_some_position)
     apply(rename_tac i option c1)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i option c1)(*strict*)
    apply(force)
   apply(rename_tac i option c1)(*strict*)
   apply(force)
  apply(rename_tac i option c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c1 e1a e2 c1a)(*strict*)
  apply(erule_tac
      x="e1a"
      in meta_allE)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c1 e1a e2 c1a x)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
  done

lemma F_PARSER_TO_EDPDA_preserves_steps: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> c \<in> epdaS.get_accessible_configurations (F_PARSER_TO_EDPDA G BOX)
  \<Longrightarrow> epdaS_step_relation (F_PARSER_TO_EDPDA G BOX) c (F_PARSER_TO_EDPDA__rules x) c1
  \<Longrightarrow> x \<in> parser_rules G
  \<Longrightarrow> parserS_step_relation G (F_PARSER_TO_EDPDA__configuration_rev G c) x (F_PARSER_TO_EDPDA__configuration_rev G c1)"
  apply(subgoal_tac "\<exists>w. BOX \<notin> set w \<and> epdaS_conf_stack c = w @ [BOX]")
   prefer 2
   apply(rule_tac
      t="BOX"
      and s="epda_box (F_PARSER_TO_EDPDA G BOX)"
      in ssubst)
    apply(simp add: F_PARSER_TO_EDPDA_def)
   apply(simp add: epdaS.get_accessible_configurations_def)
   apply(clarsimp)
   apply(rename_tac d i)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d i")
    apply(rename_tac d i)(*strict*)
    apply(force)
   apply(rename_tac d i a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac d i a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i option)(*strict*)
   apply(rule epda_no_use_epda_box_implies_stack_content)
      apply(rename_tac d i option)(*strict*)
      apply (metis F_PARSER_TO_EDPDA_generates_epda)
     apply(rename_tac d i option)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d i option)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d i option)(*strict*)
   apply(clarsimp)
   apply(rename_tac d i option r)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
   apply(clarsimp)
   apply(rename_tac d i option xa)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__rules_def)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(clarsimp)
   apply(subgoal_tac "valid_parser_step_label G xa")
    apply(rename_tac d i option xa)(*strict*)
    prefer 2
    apply(simp add: valid_parser_def)
   apply(rename_tac d i option xa)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac d i option xa k w)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i option xa k w)(*strict*)
    apply (metis in_set_butlastD insert_absorb insert_subset)
   apply(rename_tac d i option xa k w)(*strict*)
   apply (metis in_set_butlastD insert_absorb insert_subset)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def parserS_step_relation_def epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w wa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G x")
   apply(rename_tac w wa)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac w wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac w wa)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def F_PARSER_TO_EDPDA__rules_def)
   apply(case_tac wa)
    apply(rename_tac w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(subgoal_tac "BOX \<in> set (rule_lpop x)")
     apply(rename_tac w)(*strict*)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac w k wa)(*strict*)
     apply (metis set_mp_prime)
    apply(rename_tac w)(*strict*)
    apply (metis last_in_set_X set_rev snoc_eq_iff_butlast trivButLast)
   apply(rename_tac w wa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. wa = w' @ [x']")
    apply(rename_tac w wa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac w wa a list)(*strict*)
   apply(thin_tac "wa=a#list")
   apply(clarsimp)
   apply(rename_tac w')(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac w' k w)(*strict*)
   apply(case_tac "rule_lpush x")
    apply(rename_tac w' k w)(*strict*)
    apply(force)
   apply(rename_tac w' k w a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpush x = w' @ [x']")
    apply(rename_tac w' k w a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac w' k w a list)(*strict*)
   apply(thin_tac "rule_lpush x=a#list")
   apply(clarsimp)
   apply(rename_tac w' k w w'a)(*strict*)
   apply(rule_tac
      t="butlast (rev w'a @ w' @ [BOX])"
      and s="rev w'a @ w'"
      in ssubst)
    apply(rename_tac w' k w w'a)(*strict*)
    apply (metis append_eq_appendI snoc_eq_iff_butlast)
   apply(rename_tac w' k w w'a)(*strict*)
   apply (metis rev_append rev_rev_ident)
  apply(rename_tac w wa)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
  apply(simp add: F_PARSER_TO_EDPDA__rules_def)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac w wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w wa)(*strict*)
  apply(simp add: option_to_list_def list_to_option_def)
  apply(case_tac "rule_rpop x")
   apply(rename_tac w wa)(*strict*)
   apply(force)
  apply(rename_tac w wa a list)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_TO_EDPDA_preserves_steps_prime: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> \<exists>w. BOX \<notin> set w \<and> epdaS_conf_stack c = w @ [BOX]
  \<Longrightarrow> epdaS_step_relation (F_PARSER_TO_EDPDA G BOX) c (F_PARSER_TO_EDPDA__rules x) c1
  \<Longrightarrow> x \<in> parser_rules G
  \<Longrightarrow> parserS_step_relation G (F_PARSER_TO_EDPDA__configuration_rev G c) x (F_PARSER_TO_EDPDA__configuration_rev G c1)"
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def parserS_step_relation_def epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac w wa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G x")
   apply(rename_tac w wa)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac w wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac w wa)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def F_PARSER_TO_EDPDA__rules_def)
   apply(case_tac wa)
    apply(rename_tac w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac w)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(subgoal_tac "BOX \<in> set (rule_lpop x)")
     apply(rename_tac w)(*strict*)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac w k wa)(*strict*)
     apply (metis set_mp_prime)
    apply(rename_tac w)(*strict*)
    apply (metis last_in_set_X set_rev snoc_eq_iff_butlast trivButLast)
   apply(rename_tac w wa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. wa = w' @ [x']")
    apply(rename_tac w wa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac w wa a list)(*strict*)
   apply(thin_tac "wa=a#list")
   apply(clarsimp)
   apply(rename_tac w')(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac w' k w)(*strict*)
   apply(case_tac "rule_lpush x")
    apply(rename_tac w' k w)(*strict*)
    apply(force)
   apply(rename_tac w' k w a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpush x = w' @ [x']")
    apply(rename_tac w' k w a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac w' k w a list)(*strict*)
   apply(thin_tac "rule_lpush x=a#list")
   apply(clarsimp)
   apply(rename_tac w' k w w'a)(*strict*)
   apply(rule_tac
      t="butlast (rev w'a @ w' @ [BOX])"
      and s="rev w'a @ w'"
      in ssubst)
    apply(rename_tac w' k w w'a)(*strict*)
    apply (metis append_eq_appendI snoc_eq_iff_butlast)
   apply(rename_tac w' k w w'a)(*strict*)
   apply (metis rev_append rev_rev_ident)
  apply(rename_tac w wa)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
  apply(simp add: F_PARSER_TO_EDPDA__rules_def)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac w wa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w wa)(*strict*)
  apply(simp add: option_to_list_def list_to_option_def)
  apply(case_tac "rule_rpop x")
   apply(rename_tac w wa)(*strict*)
   apply(force)
  apply(rename_tac w wa a list)(*strict*)
  apply(clarsimp)
  done

definition F_PARSER_TO_EDPDA__LR__relation_TSstructure :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epda
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<equiv>
  \<exists>BOX.
    F_PARSER_TO_EDPDA__SpecInput1 G1 BOX
    \<and> G2 = F_PARSER_TO_EDPDA G1 BOX"

definition F_PARSER_TO_EDPDA__LR__relation_configuration :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_configuration G1 G2 c1 c2 \<equiv>
  F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2
  \<and> c1 \<in> parserS.get_accessible_configurations G1
  \<and> F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2) = c2"

definition F_PARSER_TO_EDPDA__LR__relation_initial_configuration :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_initial_configuration G1 G2 c1 c2 \<equiv>
  F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2
  \<and> c1 \<in> parserS_initial_configurations G1
  \<and> F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2) = c2"

definition F_PARSER_TO_EDPDA__LR__relation_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epda
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_effect G1 G2 w1 w2 \<equiv>
  F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2
  \<and> w1 = w2"

definition F_PARSER_TO_EDPDA__LR__relation_step_labels :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event, 'stack) epda_step_label
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_step_labels G1 G2 e1 e2 \<equiv>
  F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2
  \<and> e1 \<in> parser_rules G1
  \<and> F_PARSER_TO_EDPDA__rules e1 = e2"

lemma parserS_epdaS_P2A_StateSimLR_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_PARSER_TO_EDPDA__LR__relation_TSstructure G1) \<longrightarrow> valid_parser G1)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1 BOX)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
  done

lemma parserS_epdaS_P2A_StateSimLR_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> valid_epda G2)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1 BOX)(*strict*)
  apply (metis F_PARSER_TO_EDPDA_generates_epda)
  done

definition F_PARSER_TO_EDPDA__LR__relation_initial_simulation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> (('stack, 'event, 'stack) epda_step_label, ('stack, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_initial_simulation G1 G2 c1 d \<equiv>
  d = der1 (F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2))"

definition F_PARSER_TO_EDPDA__LR__relation_step_simulation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('stack, 'event, 'stack) epda_step_label, ('stack, 'event, 'stack) epdaS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 c1 e1 c1' c2 d \<equiv>
  d = der2 (F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2)) (F_PARSER_TO_EDPDA__rules e1) (F_PARSER_TO_EDPDA__configuration G1 c1' (epda_box G2))"

lemma F_PARSER_TO_EDPDA__configuration_preserves_configurations: "
  F_PARSER_TO_EDPDA__SpecInput1 G1 BOX
  \<Longrightarrow> G2 = F_PARSER_TO_EDPDA G1 BOX
  \<Longrightarrow> c1 \<in> parserS_configurations G1
  \<Longrightarrow> parserS_conf_stack c1 \<noteq> []
  \<Longrightarrow> F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2) \<in> epdaS_configurations G2"
  apply(simp add: epdaS_configurations_def F_PARSER_TO_EDPDA__configuration_def parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac l w)(*strict*)
  apply(rule conjI)
   apply(rename_tac l w)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
   apply (metis last_in_set_X)
  apply(rename_tac l w)(*strict*)
  apply(rule conjI)
   apply(rename_tac l w)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
   apply (metis butlast_if_match_direct insert_Diff_single subset_insertI2 subset_insert_iff)
  apply(rename_tac l w)(*strict*)
  apply(rule conjI)
   apply(rename_tac l w)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac l w)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA_def)
  apply (metis subset_insertI2 subset_trans trivButLast)
  done

lemma F_PARSER_TO_EDPDA__configuration_preserves_initial_configurations: "
  F_PARSER_TO_EDPDA__SpecInput1 G1 BOX
  \<Longrightarrow> G2 = F_PARSER_TO_EDPDA G1 BOX
  \<Longrightarrow> c1 \<in> parserS_initial_configurations G1
  \<Longrightarrow> F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2) \<in> epdaS_initial_configurations G2"
  apply(simp add: epdaS_initial_configurations_def)
  apply(rule conjI)
   apply(simp only: F_PARSER_TO_EDPDA__configuration_def)
   apply(clarsimp)
   apply(simp only: parserS_initial_configurations_def)
   apply(clarsimp)
  apply(rule conjI)
   apply(simp only: F_PARSER_TO_EDPDA__configuration_def)
   apply(clarsimp)
   apply(simp only: parserS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rule F_PARSER_TO_EDPDA__configuration_preserves_configurations)
     apply(force)
    apply(force)
   apply (metis parserS_inst_AX_initial_configuration_belongs subsetE)
  apply(simp add: parserS_initial_configurations_def)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserS_initial_configurations G1 \<longrightarrow> (\<exists>d2. epdaS.derivation_initial G2 d2 \<and> F_PARSER_TO_EDPDA__LR__relation_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_PARSER_TO_EDPDA__LR__relation_initial_simulation G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_PARSER_TO_EDPDA__LR__relation_configuration G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_initial_simulation_def)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_initial_configuration_def)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: epdaS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: der1_def)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
   apply(clarsimp)
   apply(rename_tac G1 c1 BOX)(*strict*)
   apply(rule F_PARSER_TO_EDPDA__configuration_preserves_initial_configurations)
     apply(rename_tac G1 c1 BOX)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 BOX)(*strict*)
    apply(force)
   apply(rename_tac G1 c1 BOX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 BOX)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 BOX)(*strict*)
   apply(simp add: parserS.get_accessible_configurations_def)
   apply(rule_tac
      x="der1 c1"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 c1 BOX)(*strict*)
    apply(simp add: parserS.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac G1 c1 BOX)(*strict*)
     apply(rule parserS.der1_is_derivation)
    apply(rename_tac G1 c1 BOX)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac G1 c1 BOX)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(simp add: get_configuration_def)
   apply(simp add: der1_def)
  apply(rename_tac G1 c1 BOX)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_def get_configuration_def der1_def)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__LR__relation_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. epdaS.derivation G2 d2 \<and> epdaS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_PARSER_TO_EDPDA__LR__relation_configuration G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(rule_tac
      x="der2 (F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2)) (F_PARSER_TO_EDPDA__rules e1) (F_PARSER_TO_EDPDA__configuration G1 c1' (epda_box G2))"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(rule epdaS.der2_is_derivation)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
   apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
   apply(rule_tac
      t="epda_box (F_PARSER_TO_EDPDA G1 BOX)"
      and s="BOX"
      in ssubst)
    apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA_def parser_step_labels_def)
   apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
   apply(simp add: parser_step_labels_def)
   apply(rule F_PARSER_TO_EDPDA__configuration_reflects_steps)
      apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(subgoal_tac "c1 \<in> parserS_configurations G1")
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   prefer 2
   apply(simp add: parserS.get_accessible_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "d i")
    apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d i a)(*strict*)
   apply(case_tac a)
   apply(rename_tac G1 G2 c1 e1 c1' d i a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d i option)(*strict*)
   apply(rule parserS.belongs_configurations)
    apply(rename_tac G1 G2 c1 e1 c1' d i option)(*strict*)
    apply(rule parserS.derivation_initial_belongs)
     apply(rename_tac G1 G2 c1 e1 c1' d i option)(*strict*)
     apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def F_PARSER_TO_EDPDA__SpecInput1_def)
    apply(rename_tac G1 G2 c1 e1 c1' d i option)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 e1 c1' d i option)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
   apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
   apply(rule epdaS.der2_belongs_prime)
     apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
     apply (metis F_PARSER_TO_EDPDA_generates_epda)
    apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
    apply(rule F_PARSER_TO_EDPDA__configuration_preserves_configurations)
       apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
       apply(force)
      apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
    apply(simp add: parserS.get_accessible_configurations_def parser_step_labels_def)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' BOX d i)(*strict*)
    apply(simp add: get_configuration_def)
    apply(case_tac "d i")
     apply(rename_tac G1 c1 e1 c1' BOX d i)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' BOX d i a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac G1 c1 e1 c1' BOX d i a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' BOX d i option)(*strict*)
    apply(subgoal_tac "parserS_conf_stack c1 \<noteq> []")
     apply(rename_tac G1 c1 e1 c1' BOX d i option)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1' BOX d i option)(*strict*)
    apply(rule F_PARSER_TO_EDPDA__SpecInput1_never_empty_lhs)
       apply(rename_tac G1 c1 e1 c1' BOX d i option)(*strict*)
       apply(force)
      apply(rename_tac G1 c1 e1 c1' BOX d i option)(*strict*)
      apply(force)
     apply(rename_tac G1 c1 e1 c1' BOX d i option)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 e1 c1' BOX d i option)(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1' BOX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(simp add: der2_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_step_simulation_def)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(simp add: der2_maximum_of_domain)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
   apply(simp add: parserS.get_accessible_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
   apply(rule_tac
      x="derivation_append d (der2 c1 e1 c1') i"
      in exI)
   apply(rule conjI)
    apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
    apply(simp add: parserS.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
     apply(rule parserS.derivation_append_preserves_derivation)
       apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
      apply(rule parserS.der2_is_derivation)
      apply(force)
     apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
     apply(clarsimp)
     apply(case_tac "d i")
      apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
     apply(rename_tac G1 G2 c1 e1 c1' d i a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac G1 G2 c1 e1 c1' d i a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1' d i option b)(*strict*)
     apply(simp add: der2_def)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 G2 c1 e1 c1' d i)(*strict*)
   apply(rule_tac
      x="Suc i"
      in exI)
   apply(simp add: get_configuration_def)
   apply(simp add: derivation_append_def)
   apply(simp add: der2_def)
  apply(rename_tac G1 G2 c1 e1 c1')(*strict*)
  apply(simp add: der2_def)
  apply(simp add: get_configuration_def)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_parser parserS_initial_configurations parser_step_labels parserS_step_relation valid_epda epdaS_configurations epdaS_initial_configurations epda_step_labels epdaS_step_relation F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_configuration F_PARSER_TO_EDPDA__LR__relation_TSstructure F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: parserS_epdaS_P2A_StateSimLR_inst_relation_initial_simulation parserS_epdaS_P2A_StateSimLR_inst_relation_step_simulation parserS_epdaS_P2A_StateSimLR_AX_TSstructure_relation_TSstructure1_belongs parserS_epdaS_P2A_StateSimLR_AX_TSstructure_relation_TSstructure2_belongs )
  done

interpretation "parserS_epdaS_P2A_StateSimLR" : ATS_Simulation_Configuration_Weak
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserS_configurations"
  (* initial_configurations1 *)
  "parserS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserS_marking_condition"
  (* marked_effect1 *)
  "parserS_marked_effect"
  (* unmarked_effect1 *)
  "parserS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_PARSER_TO_EDPDA__LR__relation_configuration"
  (* relation_initial_configuration *)
  "F_PARSER_TO_EDPDA__LR__relation_initial_configuration"
  (* relation_effect *)
  "F_PARSER_TO_EDPDA__LR__relation_effect"
  (* relation_TSstructure *)
  "F_PARSER_TO_EDPDA__LR__relation_TSstructure"
  (* relation_initial_simulation *)
  "F_PARSER_TO_EDPDA__LR__relation_initial_simulation"
  (* relation_step_simulation *)
  "F_PARSER_TO_EDPDA__LR__relation_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations parser_interpretations)
  apply(simp add: parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__LR__relation_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__LR__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TO_EDPDA__LR__relation_effect G1 G2) (parserS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_effect_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: epdaS_unmarked_effect_def parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
  apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca)(*strict*)
   apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb)(*strict*)
    apply(rule_tac
      x="cb"
      in exI)
    apply(rule conjI)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb)(*strict*)
     apply(simp add: derivation_append_def)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN (derivation_append deri1 (der2 c1 e1 c1') deri1n) i=0")
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb)(*strict*)
     apply(clarsimp)
     apply(thin_tac "parser_fixed_input_length_recN (derivation_append deri1 (der2 c1 e1 c1') deri1n) i=0")
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb)(*strict*)
     apply(simp add: get_configuration_def)
     apply(simp add: F_PARSER_TO_EDPDA__LR__relation_initial_configuration_def)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca)(*strict*)
     apply(subgoal_tac "c=ca")
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca)(*strict*)
      prefer 2
      apply(simp add: derivation_append_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' i e v ca)(*strict*)
     apply(case_tac i)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' i e v ca)(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c')(*strict*)
      apply(rule_tac
      x="F_PARSER_TO_EDPDA__configuration G1 c' (epda_box G2)"
      in exI)
      apply(clarsimp)
      apply(rule_tac
      x="0"
      in exI)
      apply(rule_tac
      x="None"
      in exI)
      apply(simp add: derivation_append_def)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' i e v ca nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca nat)(*strict*)
     apply(rename_tac i)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i)(*strict*)
     apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_def)
     apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_DEF_def)
     apply(clarsimp)
     apply(subgoal_tac "i < Suc deri1n")
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i)(*strict*)
      prefer 2
      apply(case_tac "i<Suc deri1n")
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i)(*strict*)
      apply(clarsimp)
      apply(simp add: derivation_append_def der2_def)
      apply(case_tac "Suc i-deri1n")
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i)(*strict*)
       apply(clarsimp)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i nat)(*strict*)
      apply(clarsimp)
      apply(case_tac nat)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i nat)(*strict*)
       apply(clarsimp)
       apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' v ca i)(*strict*)
       apply(force)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i nat nata)(*strict*)
      apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i)(*strict*)
     apply(erule_tac
      x="Suc i"
      in allE)
     apply(erule impE)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i y)(*strict*)
     apply(case_tac y)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i y option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option b)(*strict*)
     apply(rule_tac
      x="b"
      in exI)
     apply(rule conjI)
      apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option b)(*strict*)
      apply(rule_tac
      x="f (Suc i)"
      in exI)
      apply(rule_tac
      x="option"
      in exI)
      apply(force)
     apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option b)(*strict*)
     apply(simp add: F_PARSER_TO_EDPDA__LR__relation_configuration_def)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option b)(*strict*)
     apply(rule_tac
      v="[parser_bottom G1]"
      in append_injr)
     apply(rule_tac
      t="epdaS_conf_scheduler (F_PARSER_TO_EDPDA__configuration G1 ca (epda_box G2)) @ [parser_bottom G1]"
      and s="parserS_conf_scheduler ca"
      in ssubst)
      apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option b)(*strict*)
      apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
      apply(simp add: derivation_append_def parserS.derivation_initial_def parserS_initial_configurations_def parserS_configurations_def)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v i option b w)(*strict*)
      apply (metis butlast_if_match_direct)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option b)(*strict*)
     apply(subgoal_tac "epdaS_conf_scheduler b @ [parser_bottom G1] = parserS_conf_scheduler c'")
      apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option b)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option b)(*strict*)
     apply(simp add: get_configuration_def)
     apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option)(*strict*)
     apply(subgoal_tac "c' \<in> parserS_configurations G1")
      apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option)(*strict*)
      apply(simp add: parserS_configurations_def)
      apply(clarsimp)
      apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f e v ca i option l w)(*strict*)
      apply (metis butlast_if_match_direct)
     apply(rename_tac G1 G2 c1 e1 c1' d2 n deri1 deri1n deri2 deri2n f c' e v ca i option)(*strict*)
     apply (metis parserS_epdaS_P2A_StateSimLR.AX_TSstructure_relation_TSstructure1_belongs parserS.belongs_configurations parserS.der2_is_derivation parserS.derivation_append_preserves_derivation_initial_prime parserS.derivation_initial_belongs)
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca)(*strict*)
    apply(rule epdaS.some_position_has_details_at_0)
    apply(rule epdaS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
  apply(rule F_PARSER_TO_EDPDA__SpecInput1_implies_never_fixed)
   apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
   apply(force)
  apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
  apply(rule parserS.derivation_append_preserves_derivation_initial)
    apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
   apply(force)
  apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
  apply(rule parserS.derivation_append_preserves_derivation)
    apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
    apply(rule parserS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
   apply(rule parserS.der2_is_derivation)
   apply(force)
  apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
  apply(simp add: derivation_append_fit_def)
  apply(case_tac "deri1 deri1n")
   apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX)(*strict*)
   apply(force)
  apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c c' i e v ca cb BOX option b)(*strict*)
  apply(simp add: der2_def)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__LR__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TO_EDPDA__LR__relation_effect G1 G2) (parserS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(rule_tac
      t="derivation_append deri1 (der1 c1) deri1n"
      and s="deri1"
      in ssubst)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(rule ext)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f x)(*strict*)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
   apply(simp add: der1_def)
   apply(rule sym)
   apply(rule parserS.none_position_after_max_dom)
     apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f x)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f x)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f x)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_effect_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_initial_simulation_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_initial_configuration_def)
  apply(clarsimp)
  apply(rule_tac
      t="derivation_append deri2 (der1 (F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2))) deri2n"
      and s="deri2"
      in ssubst)
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a)(*strict*)
   apply(rule ext)
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a x)(*strict*)
   apply(simp add: derivation_append_def)
   apply(clarsimp)
   apply(simp add: der1_def)
   apply(rule sym)
   apply(rule epdaS.none_position_after_max_dom)
     apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a x)(*strict*)
     apply(rule epdaS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a x)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a x)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f a c ca)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN deri1 i"
      and s="0"
      in ssubst)
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
   apply(clarsimp)
   apply(rename_tac G1 c1 n deri1 deri1n deri2 deri2n f c c' i e v BOX)(*strict*)
   apply(rule F_PARSER_TO_EDPDA__SpecInput1_implies_never_fixed)
    apply(rename_tac G1 c1 n deri1 deri1n deri2 deri2n f c c' i e v BOX)(*strict*)
    apply(force)
   apply(rename_tac G1 c1 n deri1 deri1n deri2 deri2n f c c' i e v BOX)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
  apply(clarsimp)
  apply(simp add: epdaS_unmarked_effect_def)
  apply(rule_tac
      x="F_PARSER_TO_EDPDA__configuration G1 c' (epda_box G2)"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
   apply(subgoal_tac "c' \<in> parserS_configurations G1")
    apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
    apply(subgoal_tac "c \<in> parserS_configurations G1")
     apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
     apply(simp add: parserS_configurations_def)
     apply(clarsimp)
     apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f i e v l la w)(*strict*)
     apply(rule_tac
      t="butlast_if_match (w @ [parser_bottom G1]) (parser_bottom G1)"
      and s="w"
      in ssubst)
      apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f i e v l la w)(*strict*)
      apply (metis butlast_if_match_direct)
     apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f i e v l la w)(*strict*)
     apply(rule_tac
      t="v @ w @ [parser_bottom G1]"
      and s="(v @ w) @ [parser_bottom G1]"
      in ssubst)
      apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f i e v l la w)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f i e v l la w)(*strict*)
     apply (metis butlast_if_match_direct)
    apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
    apply(simp add: parserS_initial_configurations_def)
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   apply(rule parserS.belongs_configurations)
    apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
    apply(rule parserS.derivation_initial_belongs)
     apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
     apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def F_PARSER_TO_EDPDA__SpecInput1_def)
    apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   apply(force)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
  apply(subgoal_tac "n=0")
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   apply(subgoal_tac "f i \<le> f deri1n")
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
    prefer 2
    apply(rule_tac
      f="f"
      in parserS_epdaS_P2A_StateSimLR.mono_all)
        apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
       apply(rule parserS.derivation_append_preserves_derivation_initial)
         apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
         apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def F_PARSER_TO_EDPDA__SpecInput1_def)
        apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
       apply(rule parserS.derivation_append_preserves_derivation)
         apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
         apply(rule parserS.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
        apply(rule parserS.der1_is_derivation)
       apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
       apply(simp add: derivation_append_fit_def)
       apply(case_tac "deri1 deri1n")
        apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
        apply(force)
       apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v a)(*strict*)
       apply(clarsimp)
       apply(case_tac a)
       apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v a option b)(*strict*)
       apply(clarsimp)
       apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v option b)(*strict*)
       apply(simp add: der1_def)
      apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
      apply(simp add: derivation_append_def)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
     apply(rule_tac
      d="deri1"
      in parserS.allPreMaxDomSome_prime)
       apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
      apply(force)
     apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   apply(rule_tac
      x="f i"
      in exI)
   apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_def)
   apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_DEF_def)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v)(*strict*)
   apply(erule_tac
      x="i"
      in allE)
   apply(erule impE)
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v)(*strict*)
    apply (metis not_None_eq parserS.allPreMaxDomSome_prime parserS.derivation_initial_is_derivation)
   apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v y)(*strict*)
   apply(subgoal_tac "f i \<le> f deri1n")
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v y)(*strict*)
    apply(simp add: derivation_append_def)
    apply(case_tac y)
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v y option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v option b)(*strict*)
    apply(subgoal_tac "i\<le> deri1n")
     apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v option b)(*strict*)
     apply(simp add: derivation_append_def)
     apply(simp add: F_PARSER_TO_EDPDA__LR__relation_configuration_def)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v option b)(*strict*)
    apply(rule parserS.allPreMaxDomSome_prime)
      apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v option b)(*strict*)
      apply(rule parserS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v option b)(*strict*)
     apply(force)
    apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v option b)(*strict*)
    apply(force)
   apply(rename_tac G1 G2 c1 deri1 deri1n deri2 f c c' i e v y)(*strict*)
   apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_S_def)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
  apply(rule_tac
      d="der1 (F_PARSER_TO_EDPDA__configuration G1 c1 (epda_box G2))"
      in epdaS.maximum_of_domainUnique)
    apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G1 G2 c1 n deri1 deri1n deri2 deri2n f c c' i e v)(*strict*)
  apply(simp add: maximum_of_domain_def der1_def)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms parserS_initial_configurations parser_step_labels parserS_step_relation parserS_unmarked_effect epdaS_initial_configurations epdaS_step_relation epdaS_unmarked_effect F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_configuration F_PARSER_TO_EDPDA__LR__relation_effect F_PARSER_TO_EDPDA__LR__relation_TSstructure F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserS_epdaS_P2A_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserS_epdaS_P2A_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserS_epdaS_P2A_StateSimLR_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserS_epdaS_P2A_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserS_epdaS_P2A_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserS_epdaS_P2A_StateSimLR_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_relation_step_simulation_preserves_marking_condition: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__LR__relation_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__LR__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> parserS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def F_PARSER_TO_EDPDA__LR__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulation_def F_PARSER_TO_EDPDA__LR__relation_initial_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX)(*strict*)
  apply(simp add: parserS_marking_condition_def epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
  apply(rule_tac
      x="f i"
      in exI)
  apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_def)
  apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
   apply(case_tac "i\<le>Suc deri1n")
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def der2_def)
   apply(case_tac "i-deri1n")
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca nat)(*strict*)
   apply(clarsimp)
   apply(case_tac nat)
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i ca)(*strict*)
    apply(force)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca nat nata)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca option b)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_configuration_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
  apply(simp add: parserS_marking_configurations_def epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
   apply (metis append_Nil butlast_if_match_direct)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
  apply(simp add: epdaS_configurations_def parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
   apply(rule_tac
      t="butlast_if_match [parser_bottom G1] (parser_bottom G1)"
      and s="[]"
      in ssubst)
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
    apply (metis append_Nil butlast_if_match_direct)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
   apply(force)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa x)(*strict*)
  apply (metis set_mp_prime)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_relation_initial_simulation_preserves_marking_condition: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow>F_PARSER_TO_EDPDA__LR__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow>derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow>derivation_append_fit deri2 d2 deri2n \<longrightarrow>parserS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow>Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow>epdaS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def F_PARSER_TO_EDPDA__LR__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulation_def F_PARSER_TO_EDPDA__LR__relation_initial_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX)(*strict*)
  apply(simp add: parserS_marking_condition_def epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
  apply(rule_tac
      x="f i"
      in exI)
  apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_def)
  apply(simp add: parserS_epdaS_P2A_StateSimLR.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
   apply(subgoal_tac "derivation_append deri1 (der1 c1) deri1n = deri1")
    apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
    prefer 2
    apply(rule ext)
    apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca x)(*strict*)
    apply(simp add: derivation_append_def)
    apply(clarsimp)
    apply(simp add: der1_def)
    apply(rule sym)
    apply(rule parserS.none_position_after_max_dom)
      apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca x)(*strict*)
      apply(rule parserS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca x)(*strict*)
     apply(force)
    apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca x)(*strict*)
    apply(force)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
   apply(clarsimp)
   apply (metis not_None_eq parserS.allPreMaxDomSome_prime parserS.derivation_initial_is_derivation)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca option b)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_configuration_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_def)
  apply(simp add: parserS_marking_configurations_def epdaS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
   apply (metis append_Nil butlast_if_match_direct)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c i e ca option fa w)(*strict*)
  apply(simp add: epdaS_configurations_def parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
   apply(rule_tac
      t="butlast_if_match [parser_bottom G1] (parser_bottom G1)"
      and s="[]"
      in ssubst)
    apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
    apply (metis append_Nil butlast_if_match_direct)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
   apply(force)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX i e option fa w l wa x)(*strict*)
  apply (metis set_mp_prime)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms parserS_initial_configurations parser_step_labels parserS_step_relation parserS_marking_condition epdaS_initial_configurations epdaS_step_relation epdaS_marking_condition F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_configuration F_PARSER_TO_EDPDA__LR__relation_TSstructure F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserS_epdaS_P2A_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserS_epdaS_P2A_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserS_epdaS_P2A_StateSimLR_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserS_epdaS_P2A_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserS_epdaS_P2A_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserS_epdaS_P2A_StateSimLR_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__LR__relation_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> parser_step_labels G1 \<longrightarrow> (\<forall>c1'. parserS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__LR__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TO_EDPDA__LR__relation_effect G1 G2) (parserS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def F_PARSER_TO_EDPDA__LR__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulation_def F_PARSER_TO_EDPDA__LR__relation_initial_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX a)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_effect_def F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
   apply(force)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX a)(*strict*)
  apply(simp add: parserS_marked_effect_def epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
  apply(simp add: derivation_append_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c ca)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__configuration_def get_configuration_def)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
    apply(simp add: parserS_initial_configurations_def parserS_configurations_def)
    apply(clarsimp)
    apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX w)(*strict*)
    apply (metis butlast_if_match_direct)
   apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
  apply(rule epdaS.some_position_has_details_at_0)
  apply(rule epdaS.derivation_initial_is_derivation)
  apply(force)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_relation_initial_simulation_preserves_marked_effect: "
  \<forall>G1 G2. F_PARSER_TO_EDPDA__LR__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> parserS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_initial_simulation G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. parserS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. epdaS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__LR__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TO_EDPDA__LR__relation_effect G1 G2) (parserS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (epdaS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def F_PARSER_TO_EDPDA__LR__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulation_def F_PARSER_TO_EDPDA__LR__relation_initial_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX)(*strict*)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX a)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX a)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_effect_def F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
   apply(force)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX a)(*strict*)
  apply(simp add: parserS_marked_effect_def epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
  apply(simp add: derivation_append_def)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
   apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
    apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c ca)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__configuration_def get_configuration_def)
    apply(clarsimp)
    apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
    apply(simp add: parserS_initial_configurations_def parserS_configurations_def)
    apply(clarsimp)
    apply(rename_tac G1 d2 n deri1 deri1n deri2 deri2n f BOX w wa)(*strict*)
    apply (metis butlast_if_match_direct)
   apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 c1 d2 n deri1 deri1n deri2 deri2n f BOX c)(*strict*)
  apply(rule epdaS.some_position_has_details_at_0)
  apply(rule epdaS.derivation_initial_is_derivation)
  apply(force)
  done

lemma parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms parserS_initial_configurations parser_step_labels parserS_step_relation parserS_marked_effect epdaS_initial_configurations epdaS_step_relation epdaS_marked_effect F_PARSER_TO_EDPDA__LR__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_configuration F_PARSER_TO_EDPDA__LR__relation_effect F_PARSER_TO_EDPDA__LR__relation_TSstructure F_PARSER_TO_EDPDA__LR__relation_initial_simulation F_PARSER_TO_EDPDA__LR__relation_step_simulation"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule parserS_epdaS_P2A_StateSimLR.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "parserS_epdaS_P2A_StateSimLR.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis parserS_epdaS_P2A_StateSimLR_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule parserS_epdaS_P2A_StateSimLR.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "parserS_epdaS_P2A_StateSimLR.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis parserS_epdaS_P2A_StateSimLR_inst_relation_initial_simulation_preserves_marked_effect)
  done

interpretation "parserS_epdaS_P2A_StateSimLR" : ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserS_configurations"
  (* initial_configurations1 *)
  "parserS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserS_marking_condition"
  (* marked_effect1 *)
  "parserS_marked_effect"
  (* unmarked_effect1 *)
  "parserS_unmarked_effect"
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* relation_configuration *)
  "F_PARSER_TO_EDPDA__LR__relation_configuration"
  (* relation_initial_configuration *)
  "F_PARSER_TO_EDPDA__LR__relation_initial_configuration"
  (* relation_effect *)
  "F_PARSER_TO_EDPDA__LR__relation_effect"
  (* relation_TSstructure *)
  "F_PARSER_TO_EDPDA__LR__relation_TSstructure"
  (* relation_initial_simulation *)
  "F_PARSER_TO_EDPDA__LR__relation_initial_simulation"
  (* relation_step_simulation *)
  "F_PARSER_TO_EDPDA__LR__relation_step_simulation"
  apply(simp add: LOCALE_DEFS epda_interpretations parser_interpretations)
  apply(simp add:
      parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_Weak_axioms parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition parserS_epdaS_P2A_StateSimLR_inst_ATS_Simulation_Configuration_Weak_Marked_Effect )
  done

definition F_PARSER_TO_EDPDA__RL__relation_TSstructure :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<equiv>
  \<exists>BOX.
    F_PARSER_TO_EDPDA__SpecInput1 G2 BOX
    \<and> G1 = F_PARSER_TO_EDPDA G2 BOX"

definition F_PARSER_TO_EDPDA__RL__relation_configuration :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__RL__relation_configuration G1 G2 c1 c2 \<equiv>
  F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2
  \<and> c1 \<in> epdaS.get_accessible_configurations G1
  \<and> F_PARSER_TO_EDPDA__configuration_rev G2 c1 = c2"

definition F_PARSER_TO_EDPDA__RL__relation_initial_configuration :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 c1 c2 \<equiv>
  F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2
  \<and> c1 \<in> epdaS_initial_configurations G1
  \<and> F_PARSER_TO_EDPDA__configuration_rev G2 c1 = c2"

definition F_PARSER_TO_EDPDA__RL__relation_effect :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> 'event list
  \<Rightarrow> 'event list
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__RL__relation_effect G1 G2 w1 w2 \<equiv>
  F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2
  \<and> w1 = w2"

definition F_PARSER_TO_EDPDA__RL__relation_step_labels :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epda_step_label
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__RL__relation_step_labels G1 G2 e1 e2 \<equiv>
  F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2
  \<and> e1 \<in> epda_delta G1
  \<and> F_PARSER_TO_EDPDA__rules_rev e1 = e2"

lemma epdaS_parserS_P2A_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs: "
  (\<forall>G1. Ex (F_PARSER_TO_EDPDA__RL__relation_TSstructure G1) \<longrightarrow> valid_epda G1)"
  apply(clarsimp)
  apply(rename_tac G1 G2)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1 BOX)(*strict*)
  apply (metis F_PARSER_TO_EDPDA_generates_epda)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> valid_parser G2)"
  apply(clarsimp)
  apply(rename_tac G1 x)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G1 BOX)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
  done

definition F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL G1 G2 c1 d \<equiv>
  d = der1 (F_PARSER_TO_EDPDA__configuration_rev G2 c1)"

definition F_PARSER_TO_EDPDA__LR__relation_step_simulationRL :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event, 'stack) epda_step_label
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d \<equiv>
  d = der2 (F_PARSER_TO_EDPDA__configuration_rev G2 c1) (F_PARSER_TO_EDPDA__rules_rev e1) (F_PARSER_TO_EDPDA__configuration_rev G2 c1')"

lemma epdaS_parserS_P2A_StateSimRL_inst_relation_initial_simulation: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<exists>d2. parserS.derivation_initial G2 d2 \<and> F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL G1 G2 c1 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_PARSER_TO_EDPDA__RL__relation_configuration G1 G2 c1 (the (get_configuration (d2 n)))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_configuration_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 BOX)(*strict*)
  apply(subgoal_tac "the (get_configuration (der1 (F_PARSER_TO_EDPDA__configuration_rev G2 c1) 0)) \<in> parserS_initial_configurations G2")
   apply(rename_tac G2 c1 BOX)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def der1_def)
   apply(simp add: epdaS_initial_configurations_def parserS_initial_configurations_def)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G2 c1 BOX)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
    apply(simp add: F_PARSER_TO_EDPDA_def)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(simp add: parserS_configurations_def epdaS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G2 BOX i)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def valid_parser_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac G2 c1 BOX)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(rule parserS.derivation_initialI)
    apply(rename_tac G2 c1 BOX)(*strict*)
    apply(rule parserS.der1_is_derivation)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(simp add: der1_def get_configuration_def)
  apply(rename_tac G2 c1 BOX)(*strict*)
  apply(simp add: der1_def get_configuration_def)
  apply(rule_tac
      x="0"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(fold der1_def)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G2 c1 BOX)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(rule_tac
      x="der1 c1"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(rule epdaS.derivation_initialI)
    apply(rename_tac G2 c1 BOX)(*strict*)
    apply(rule epdaS.der1_is_derivation)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 BOX c)(*strict*)
   apply(simp add: der1_def get_configuration_def)
  apply(rename_tac G2 c1 BOX)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(simp add: der1_def get_configuration_def)
  done

lemma F_PARSER_TO_EDPDA__rules_rev_preserves_rules: "
  F_PARSER_TO_EDPDA__SpecInput1 G2 BOX
  \<Longrightarrow> e1 \<in> epda_step_labels (F_PARSER_TO_EDPDA G2 BOX)
  \<Longrightarrow> F_PARSER_TO_EDPDA__rules_rev e1 \<in> parser_rules G2"
  apply(simp add: epda_step_labels_def)
  apply(simp add: F_PARSER_TO_EDPDA__rules_rev_def F_PARSER_TO_EDPDA_def F_PARSER_TO_EDPDA__rules_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule_tac
      t="\<lparr>rule_lpop = rev (edge_pop (F_PARSER_TO_EDPDA__rules x)) @ [edge_src (F_PARSER_TO_EDPDA__rules x)], rule_rpop = option_to_list (edge_event (F_PARSER_TO_EDPDA__rules x)), rule_lpush = rev (edge_push (F_PARSER_TO_EDPDA__rules x)) @ [edge_trg (F_PARSER_TO_EDPDA__rules x)], rule_rpush = []\<rparr>"
      and s="x"
      in ssubst)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(clarsimp)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(case_tac x)
  apply(rename_tac x rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__rules_rev_def F_PARSER_TO_EDPDA_def F_PARSER_TO_EDPDA__rules_def)
  apply(simp add: option_to_list_def list_to_option_def)
  apply(case_tac "rule_rpop")
   apply(rename_tac rule_lpop rule_rpop rule_lpush)(*strict*)
   apply(force)
  apply(rename_tac rule_lpop rule_rpop rule_lpush a list)(*strict*)
  apply(force)
  done

lemma F_PARSER_TO_EDPDA__configuration_rev_preserves_configurations: "
  c1 \<in> epdaS_configurations (F_PARSER_TO_EDPDA G2 BOX)
  \<Longrightarrow> \<exists>w. epda_box (F_PARSER_TO_EDPDA G2 BOX) \<notin> set w \<and> epdaS_conf_stack c1 = w @ [epda_box G]
  \<Longrightarrow> F_PARSER_TO_EDPDA__SpecInput1 G2 BOX
  \<Longrightarrow> F_PARSER_TO_EDPDA__configuration_rev G2 c1 \<in> parserS_configurations G2"
  apply(simp add: parserS_configurations_def epdaS_configurations_def F_PARSER_TO_EDPDA__configuration_rev_def)
  apply(clarsimp)
  apply(rename_tac q w i)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(clarsimp)
  apply(simp add: valid_parser_def)
  apply(rule conjI)
   apply(rename_tac q w i)(*strict*)
   apply(clarsimp)
   apply(rename_tac q w i x)(*strict*)
   apply(force)
  apply(rename_tac q w i)(*strict*)
  apply(force)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_relation_step_simulation: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__RL__relation_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<exists>d2. parserS.derivation G2 d2 \<and> parserS.belongs G2 d2 \<and> the (get_configuration (d2 0)) = c2 \<and> F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> F_PARSER_TO_EDPDA__RL__relation_configuration G1 G2 c1' (the (get_configuration (d2 n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulationRL_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
   apply(rule parserS.der2_is_derivation)
   apply(rule F_PARSER_TO_EDPDA_preserves_steps)
      apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
    apply(rule_tac
      t="F_PARSER_TO_EDPDA__rules (F_PARSER_TO_EDPDA__rules_rev e1)"
      and s="e1"
      in ssubst)
     apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
     apply (metis F_PARSER_TO_EDPDA__rules_F_PARSER_TO_EDPDA__rules_rev epda_step_labels_def)
    apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
   apply(rule F_PARSER_TO_EDPDA__rules_rev_preserves_rules)
    apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
   apply(rule parserS.derivation_belongs)
      apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
      apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
     apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
    apply(rule_tac
      BOX="BOX"
      in F_PARSER_TO_EDPDA__configuration_rev_preserves_configurations)
      apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
      apply (metis (full_types) F_PARSER_TO_EDPDA_generates_epda epdaS.get_accessible_configurations_are_configurations subsetD)
     apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
     apply(simp add: epdaS.get_accessible_configurations_def)
     apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' BOX d i)(*strict*)
     apply(case_tac "d i")
      apply(rename_tac G2 c1 e1 c1' BOX d i)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac G2 c1 e1 c1' BOX d i a)(*strict*)
     apply(simp add: get_configuration_def)
     apply(case_tac a)
     apply(rename_tac G2 c1 e1 c1' BOX d i a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
     apply(rule epda_no_use_epda_box_implies_stack_content)
        apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
        apply (metis F_PARSER_TO_EDPDA_generates_epda)
       apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
       apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
       apply(simp add: F_PARSER_TO_EDPDA_def)
       apply(clarsimp)
       apply(rename_tac G2 c1 e1 c1' BOX d i option r)(*strict*)
       apply(simp add: F_PARSER_TO_EDPDA__rules_def)
       apply(erule_tac
      x="r"
      in ballE)
        apply(rename_tac G2 c1 e1 c1' BOX d i option r)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac G2 c1 e1 c1' BOX d i option r)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "valid_parser_step_label G2 r")
        apply(rename_tac G2 c1 e1 c1' BOX d i option r)(*strict*)
        prefer 2
        apply(simp add: valid_parser_def)
       apply(rename_tac G2 c1 e1 c1' BOX d i option r)(*strict*)
       apply(simp add: valid_parser_step_label_def)
       apply(clarsimp)
       apply(rename_tac G2 c1 e1 c1' BOX d i option r k w)(*strict*)
       apply(rule conjI)
        apply(rename_tac G2 c1 e1 c1' BOX d i option r k w)(*strict*)
        apply (metis in_set_butlastD insert_absorb insert_subset)
       apply(rename_tac G2 c1 e1 c1' BOX d i option r k w)(*strict*)
       apply (metis in_set_butlastD insert_absorb insert_subset)
      apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
   apply(simp add: der2_def get_configuration_def)
  apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
   apply(simp add: epdaS.get_accessible_configurations_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' BOX d i)(*strict*)
   apply(case_tac "d i")
    apply(rename_tac G2 c1 e1 c1' BOX d i)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac G2 c1 e1 c1' BOX d i a)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac G2 c1 e1 c1' BOX d i a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
   apply(rule_tac
      x="derivation_append d (der2 c1 e1 c1') i"
      in exI)
   apply(rule conjI)
    apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation_initial)
      apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
      apply (metis F_PARSER_TO_EDPDA_generates_epda)
     apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
    apply(rule epdaS.derivation_append_preserves_derivation)
      apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
      apply (metis epdaS.derivation_initial_is_derivation)
     apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac G2 c1 e1 c1' BOX d i option)(*strict*)
   apply(rule_tac
      x="Suc i"
      in exI)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac G2 c1 e1 c1' BOX)(*strict*)
  apply(simp add: der2_def)
  apply(simp add: get_configuration_def)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms: "
  ATS_Simulation_Configuration_Weak_axioms valid_epda epdaS_initial_configurations epda_step_labels epdaS_step_relation valid_parser parserS_configurations parserS_initial_configurations parser_step_labels parserS_step_relation F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__RL__relation_initial_configuration F_PARSER_TO_EDPDA__RL__relation_TSstructure F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_axioms_def)
  apply(simp add: epdaS_parserS_P2A_StateSimRL_inst_relation_initial_simulation epdaS_parserS_P2A_StateSimRL_inst_relation_step_simulation epdaS_parserS_P2A_StateSimRL_inst_AX_TSstructure_relation_TSstructure1_belongs epdaS_parserS_P2A_StateSimRL_inst_AX_TSstructure_relation_TSstructure2_belongs )
  done

interpretation "epdaS_parserS_P2A_StateSimRL" : ATS_Simulation_Configuration_Weak
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserS_configurations"
  (* initial_configurations1 *)
  "parserS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserS_marking_condition"
  (* marked_effect1 *)
  "parserS_marked_effect"
  (* unmarked_effect1 *)
  "parserS_unmarked_effect"
  (* relation_configuration *)
  "F_PARSER_TO_EDPDA__RL__relation_configuration"
  (* relation_initial_configuration *)
  "F_PARSER_TO_EDPDA__RL__relation_initial_configuration"
  (* relation_effect *)
  "F_PARSER_TO_EDPDA__RL__relation_effect"
  (* relation_TSstructure *)
  "F_PARSER_TO_EDPDA__RL__relation_TSstructure"
  (* relation_initial_simulation *)
  "F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_PARSER_TO_EDPDA__LR__relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS epda_interpretations parser_interpretations)
  apply(simp add: epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__RL__relation_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TO_EDPDA__RL__relation_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (parserS_unmarked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_effect_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_effect_def)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
  apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c ca)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaS_unmarked_effect_def parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
  apply(simp add: epdaS_parserS_P2A_StateSimRL.simulating_derivation_def)
  apply(simp add: epdaS_parserS_P2A_StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(rule_tac
      x="F_PARSER_TO_EDPDA__configuration_rev G2 c"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
   apply(rule_tac
      d="derivation_append deri1 (der2 c1 e1 c1') deri1n"
      in epdaS.allPreMaxDomSome_prime)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation)
       apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
      apply(simp add: epdaS.der2_is_derivation)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
     apply(simp add: derivation_append_fit_def)
     apply(case_tac "deri1 deri1n")
      apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e aa)(*strict*)
     apply(clarsimp)
     apply(case_tac aa)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e aa option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
   apply(rule_tac
      t="Suc deri1n"
      and s="deri1n + Suc 0"
      in ssubst)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
   apply (metis concat_has_max_dom der2_maximum_of_domain)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(rule_tac
      x="b"
      in exI)
  apply(rule_tac
      x="f i"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_append deri2 (der2 (F_PARSER_TO_EDPDA__configuration_rev G2 c1) (F_PARSER_TO_EDPDA__rules_rev e1) (F_PARSER_TO_EDPDA__configuration_rev G2 c1')) deri2n) (f i)"
      and s="0"
      in ssubst)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(rule F_PARSER_TO_EDPDA__SpecInput1_implies_never_fixed)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(rule parserS.derivation_append_preserves_derivation_initial)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(rule parserS.derivation_append_preserves_derivation)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(rule parserS.der2_is_derivation)
    apply(rule F_PARSER_TO_EDPDA_preserves_steps)
       apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
       apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
       apply(force)
      apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(rule_tac
      t="F_PARSER_TO_EDPDA__rules (F_PARSER_TO_EDPDA__rules_rev e1)"
      and s="e1"
      in ssubst)
      apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(rule F_PARSER_TO_EDPDA__rules_F_PARSER_TO_EDPDA__rules_rev)
      apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
      apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(simp add: epdaS_step_relation_def)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(simp add: epda_step_labels_def)
    apply(rule F_PARSER_TO_EDPDA__rules_rev_preserves_rules)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(simp add: epda_step_labels_def)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(case_tac "deri2 deri2n")
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b aa)(*strict*)
   apply(clarsimp)
   apply(case_tac aa)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b aa optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b optiona ba)(*strict*)
   apply(simp add: der2_def)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="parserS_conf_scheduler b"
      and s="epdaS_conf_scheduler c'@[parser_bottom G2]"
      in ssubst)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_PARSER_TO_EDPDA__configuration_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler (F_PARSER_TO_EDPDA__configuration_rev G2 c)"
      and s="epdaS_conf_scheduler cb@[parser_bottom G2]"
      in ssubst)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(simp add: derivation_append_def)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect: "
  \<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TO_EDPDA__RL__relation_effect G1 G2) (epdaS_unmarked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (parserS_unmarked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_effect_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
  apply(rule_tac
      x="a"
      in bexI)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_effect_def)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
  apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c ca)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaS_unmarked_effect_def parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
  apply(simp add: epdaS_parserS_P2A_StateSimRL.simulating_derivation_def)
  apply(simp add: epdaS_parserS_P2A_StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(rule_tac
      x="F_PARSER_TO_EDPDA__configuration_rev G2 c"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
   apply(rule_tac
      d="derivation_append deri1 (der1 c1) deri1n"
      in epdaS.allPreMaxDomSome_prime)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation)
       apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
      apply(simp add: epdaS.der1_is_derivation)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
     apply(simp add: derivation_append_fit_def)
     apply(case_tac "deri1 deri1n")
      apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e aa)(*strict*)
     apply(clarsimp)
     apply(case_tac aa)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e aa option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
   apply(rule maximum_of_domain_derivation_append_der1)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(rule_tac
      x="b"
      in exI)
  apply(rule_tac
      x="f i"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_append deri2 (der1 (F_PARSER_TO_EDPDA__configuration_rev G2 c1)) deri2n) (f i)"
      and s="0"
      in ssubst)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(rule F_PARSER_TO_EDPDA__SpecInput1_implies_never_fixed)
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(rule parserS.derivation_append_preserves_derivation_initial)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(rule parserS.derivation_append_preserves_derivation)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(rule parserS.der1_is_derivation)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(simp add: derivation_append_fit_def)
   apply(case_tac "deri2 deri2n")
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b aa)(*strict*)
   apply(clarsimp)
   apply(case_tac aa)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b aa optiona ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b optiona ba)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="parserS_conf_scheduler b"
      and s="epdaS_conf_scheduler c'@[parser_bottom G2]"
      in ssubst)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_configuration_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def F_PARSER_TO_EDPDA__configuration_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler (F_PARSER_TO_EDPDA__configuration_rev G2 c)"
      and s="epdaS_conf_scheduler cb@[parser_bottom G2]"
      in ssubst)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f a BOX c cb c' i e option b)(*strict*)
  apply(simp add: derivation_append_def)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_unmarked_effect parserS_initial_configurations parserS_step_relation parserS_unmarked_effect F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__RL__relation_initial_configuration F_PARSER_TO_EDPDA__RL__relation_effect F_PARSER_TO_EDPDA__RL__relation_TSstructure F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_parserS_P2A_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_parserS_P2A_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_parserS_P2A_StateSimRL_inst_relation_step_simulation_preserves_unmarked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_parserS_P2A_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_parserS_P2A_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_parserS_P2A_StateSimRL_inst_relation_initial_simulation_preserves_unmarked_effect)
  done

lemma F_PARSER_TO_EDPDA__SpecInput1_no_pop_of_box: "
  F_PARSER_TO_EDPDA__SpecInput1 G2 BOX
  \<Longrightarrow> \<forall>r \<in> epda_delta (F_PARSER_TO_EDPDA G2 BOX) . epda_box (F_PARSER_TO_EDPDA G2 BOX) \<notin> set (edge_pop r) \<and> epda_box (F_PARSER_TO_EDPDA G2 BOX) \<notin> set (edge_push r)"
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__rules_def)
  apply(subgoal_tac "valid_parser_step_label G2 x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x k w)(*strict*)
  apply (metis in_set_butlastD subsetD)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_relation_step_simulation_preserves_marking_condition: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__RL__relation_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> epdaS_marking_condition G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n) \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> parserS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_effect_def)
  apply(simp add: parserS_marking_condition_def epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
   apply(rule_tac
      x="cb"
      in exI)
   apply(simp add: derivation_append_def)
   apply(simp add: parserS.derivation_initial_def)
   apply(simp add: parserS_initial_configurations_def)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
  apply(simp add: epdaS_parserS_P2A_StateSimRL.simulating_derivation_def)
  apply(simp add: epdaS_parserS_P2A_StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      x="f i"
      in exI)
  apply(subgoal_tac "i\<le>Suc deri1n")
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
   prefer 2
   apply(rule_tac
      d="derivation_append deri1 (der2 c1 e1 c1') deri1n"
      in epdaS.allPreMaxDomSome_prime)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation)
       apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
      apply(simp add: epdaS.der2_is_derivation)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
     apply(simp add: derivation_append_fit_def)
     apply(case_tac "deri1 deri1n")
      apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb option b)(*strict*)
     apply(simp add: der2_def)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
   apply(rule maximum_of_domain_derivation_append_der2)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
  apply(erule impE)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca cb option b)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_configuration_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def F_PARSER_TO_EDPDA__configuration_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
  apply(simp add: epdaS_marking_configurations_def parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
   apply(rule_tac
      x="epdaS_conf_state c"
      in bexI)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def F_PARSER_TO_EDPDA__configuration_rev_def)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
  apply(rule_tac
      G="F_PARSER_TO_EDPDA G2 BOX"
      in F_PARSER_TO_EDPDA__configuration_rev_preserves_configurations)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib)(*strict*)
  apply(case_tac "da ib")
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib a optiona b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib optiona b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib optiona)(*strict*)
  apply(rule_tac
      d="da"
      in epda_no_use_epda_box_implies_stack_content)
     apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib optiona)(*strict*)
     apply (metis epdaS_parserS_P2A_StateSimRL.AX_TSstructure_relation_TSstructure1_belongs)
    apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib optiona)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib optiona)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G2 c1 e1 c1' n deri1 deri1n deri2 deri2n f BOX i e c ca option d da ia ib optiona)(*strict*)
  apply(rule F_PARSER_TO_EDPDA__SpecInput1_no_pop_of_box)
  apply(force)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_relation_initial_simulation_preserves_marking_condition: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow>F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow>derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow>derivation_append_fit deri2 d2 deri2n \<longrightarrow>epdaS_marking_condition G1 (derivation_append deri1 (der1 c1) deri1n) \<longrightarrow>Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow>parserS_marking_condition G2 (derivation_append deri2 d2 deri2n)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n x)(*strict*)
  apply(rename_tac f)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_configuration_def F_PARSER_TO_EDPDA__LR__relation_step_simulationRL_def F_PARSER_TO_EDPDA__RL__relation_effect_def)
  apply(simp add: parserS_marking_condition_def epdaS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
   apply(rule_tac
      x="cb"
      in exI)
   apply(simp add: derivation_append_def)
   apply(simp add: parserS.derivation_initial_def)
   apply(simp add: parserS_initial_configurations_def)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
  apply(simp add: epdaS_parserS_P2A_StateSimRL.simulating_derivation_def)
  apply(simp add: epdaS_parserS_P2A_StateSimRL.simulating_derivation_DEF_def)
  apply(clarsimp)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      x="f i"
      in exI)
  apply(subgoal_tac "i\<le>deri1n")
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
   prefer 2
   apply(rule_tac
      d="derivation_append deri1 (der1 c1) deri1n"
      in epdaS.allPreMaxDomSome_prime)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
     apply(rule epdaS.derivation_append_preserves_derivation)
       apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
       apply(rule epdaS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
      apply(simp add: epdaS.der1_is_derivation)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
     apply(simp add: derivation_append_fit_def)
     apply(case_tac "deri1 deri1n")
      apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb option b)(*strict*)
     apply(simp add: der1_def)
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
   apply(rule maximum_of_domain_derivation_append_der1)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
  apply(erule impE)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb y)(*strict*)
  apply(case_tac y)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca cb option b)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_configuration_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def F_PARSER_TO_EDPDA__configuration_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
  apply(simp add: epdaS_marking_configurations_def parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
   apply(rule_tac
      x="epdaS_conf_state c"
      in bexI)
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def F_PARSER_TO_EDPDA__configuration_rev_def)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
  apply(rule_tac
      G="F_PARSER_TO_EDPDA G2 BOX"
      in F_PARSER_TO_EDPDA__configuration_rev_preserves_configurations)
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia)(*strict*)
  apply(case_tac "d ia")
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia a optiona b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia optiona b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia optiona)(*strict*)
  apply(rule_tac
      d="d"
      in epda_no_use_epda_box_implies_stack_content)
     apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia optiona)(*strict*)
     apply (metis epdaS_parserS_P2A_StateSimRL.AX_TSstructure_relation_TSstructure1_belongs)
    apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia optiona)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia optiona)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G2 c1 n deri1 deri1n deri2 deri2n f BOX i e c ca option d ia optiona)(*strict*)
  apply(rule F_PARSER_TO_EDPDA__SpecInput1_no_pop_of_box)
  apply(force)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms: "
  ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marking_condition parserS_initial_configurations parserS_step_relation parserS_marking_condition F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__RL__relation_initial_configuration F_PARSER_TO_EDPDA__RL__relation_TSstructure F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_parserS_P2A_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_parserS_P2A_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_parserS_P2A_StateSimRL_inst_relation_step_simulation_preserves_marking_condition)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_parserS_P2A_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_parserS_P2A_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_parserS_P2A_StateSimRL_inst_relation_initial_simulation_preserves_marking_condition)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_relation_step_simulation_preserves_marked_effect: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__RL__relation_configuration G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. epdaS_step_relation G1 c1 e1 c1' \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 c1 e1 c1' c2 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der2 c1 e1 c1') deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 (derivation_append deri1 (der2 c1 e1 c1') deri1n) (Suc deri1n) (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TO_EDPDA__RL__relation_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der2 c1 e1 c1') deri1n)) (parserS_marked_effect G2 (derivation_append deri2 d2 deri2n))))))))))))"
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
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_effect_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserS_marked_effect_def epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca cb)(*strict*)
  apply(rule_tac
      x="cb"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca cb)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c ca cb)(*strict*)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c cb)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_relation_initial_simulation_preserves_marked_effect: "
  \<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>d2. F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL G1 G2 c1 d2 \<longrightarrow> (\<forall>n. maximum_of_domain d2 n \<longrightarrow> (\<forall>deri1. epdaS.derivation_initial G1 deri1 \<longrightarrow> (\<forall>deri1n. maximum_of_domain deri1 deri1n \<longrightarrow> (\<forall>deri2. parserS.derivation_initial G2 deri2 \<longrightarrow> (\<forall>deri2n. maximum_of_domain deri2 deri2n \<longrightarrow> F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 (the (get_configuration (deri1 0))) (the (get_configuration (deri2 0))) \<longrightarrow> derivation_append_fit deri1 (der1 c1) deri1n \<longrightarrow> derivation_append_fit deri2 d2 deri2n \<longrightarrow> Ex (ATS_Simulation_Configuration_Weak.simulating_derivation F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL G1 G2 (derivation_append deri1 (der1 c1) deri1n) deri1n (derivation_append deri2 d2 deri2n) (deri2n + n)) \<longrightarrow> left_total_on (F_PARSER_TO_EDPDA__RL__relation_effect G1 G2) (epdaS_marked_effect G1 (derivation_append deri1 (der1 c1) deri1n)) (parserS_marked_effect G2 (derivation_append deri2 d2 deri2n)))))))))"
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
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_effect_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f a)(*strict*)
  apply(simp add: parserS_marked_effect_def epdaS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri1 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_at_0)
   apply(rule epdaS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(subgoal_tac "\<exists>c. deri2 0 = Some (pair None c)")
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca cb)(*strict*)
  apply(rule_tac
      x="cb"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca cb)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c ca cb)(*strict*)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c cb)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def get_configuration_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f c)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
  done

lemma epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms: "
  ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_initial_configurations epda_step_labels epdaS_step_relation epdaS_marked_effect parserS_initial_configurations parserS_step_relation parserS_marked_effect F_PARSER_TO_EDPDA__RL__relation_configuration F_PARSER_TO_EDPDA__RL__relation_initial_configuration F_PARSER_TO_EDPDA__RL__relation_effect F_PARSER_TO_EDPDA__RL__relation_TSstructure F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL F_PARSER_TO_EDPDA__LR__relation_step_simulationRL"
  apply(simp add: ATS_Simulation_Configuration_Weak_Marked_Effect_axioms_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(rule epdaS_parserS_P2A_StateSimRL.relation_step_simulation_preservation_PROVE2)
    apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
    prefer 2
    apply(rename_tac G1 G2 d1' d2')(*strict*)
    apply(force)
   apply(rename_tac G1 G2 d1' d2' c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(thin_tac "epdaS_parserS_P2A_StateSimRL.relation_step_simulation_preservation G1 G2 d1' d2'")
   apply(clarsimp)
   apply(rename_tac G1 G2 c1 c2 e1 c1' d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   apply(metis epdaS_parserS_P2A_StateSimRL_inst_relation_step_simulation_preserves_marked_effect)
  apply(clarsimp)
  apply(rename_tac G1 G2 d1' d2')(*strict*)
  apply(rule epdaS_parserS_P2A_StateSimRL.relation_initial_simulation_preservation_PROVE2)
   apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
   prefer 2
   apply(rename_tac G1 G2 d1' d2')(*strict*)
   apply(force)
  apply(rename_tac G1 G2 d1' d2' c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(thin_tac "epdaS_parserS_P2A_StateSimRL.relation_initial_simulation_preservation G1 G2 d1' d2'")
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 d2 n deri1 deri1n deri2 deri2n f)(*strict*)
  apply(metis epdaS_parserS_P2A_StateSimRL_inst_relation_initial_simulation_preserves_marked_effect)
  done

interpretation "epdaS_parserS_P2A_StateSimRL" : ATS_Simulation_Configuration_WeakLR_FULL
  (* TSstructure2 *)
  "valid_epda"
  (* configurations2 *)
  "epdaS_configurations"
  (* initial_configurations2 *)
  "epdaS_initial_configurations"
  (* step_labels2 *)
  "epda_step_labels"
  (* step_relation2 *)
  "epdaS_step_relation"
  (* effects2 *)
  "epda_effects"
  (* marking_condition2 *)
  "epdaS_marking_condition"
  (* marked_effect2 *)
  "epdaS_marked_effect"
  (* unmarked_effect2 *)
  "epdaS_unmarked_effect"
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserS_configurations"
  (* initial_configurations1 *)
  "parserS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserS_marking_condition"
  (* marked_effect1 *)
  "parserS_marked_effect"
  (* unmarked_effect1 *)
  "parserS_unmarked_effect"
  (* relation_configuration *)
  "F_PARSER_TO_EDPDA__RL__relation_configuration"
  (* relation_initial_configuration *)
  "F_PARSER_TO_EDPDA__RL__relation_initial_configuration"
  (* relation_effect *)
  "F_PARSER_TO_EDPDA__RL__relation_effect"
  (* relation_TSstructure *)
  "F_PARSER_TO_EDPDA__RL__relation_TSstructure"
  (* relation_initial_simulation *)
  "F_PARSER_TO_EDPDA__LR__relation_initial_simulationRL"
  (* relation_step_simulation *)
  "F_PARSER_TO_EDPDA__LR__relation_step_simulationRL"
  apply(simp add: LOCALE_DEFS epda_interpretations parser_interpretations)
  apply(simp add: epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_Weak_axioms  epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_Weak_Unmarked_Effect_axioms epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_Weak_Marked_Effect_axioms epdaS_parserS_P2A_StateSimRL_inst_ATS_Simulation_Configuration_WeakLR_Marking_Condition_axioms )
  done

lemma F_PARSER_TO_EDPDA_preserves_lang1: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parserS.marked_language G \<subseteq> epdaS.marked_language (F_PARSER_TO_EDPDA G BOX)"
  apply(subgoal_tac "left_total_on (F_PARSER_TO_EDPDA__LR__relation_effect SSG1 SSG2) (parserS.finite_marked_language SSG1) (epdaS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule parserS_epdaS_P2A_StateSimLR.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
   apply(force)
  apply(rule_tac
      t="parserS.marked_language G"
      and s="parserS.finite_marked_language G"
      in ssubst)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply (metis parserS.AX_marked_language_finite)
  apply(rule_tac
      t="epdaS.marked_language (F_PARSER_TO_EDPDA G BOX)"
      and s="epdaS.finite_marked_language (F_PARSER_TO_EDPDA G BOX)"
      in ssubst)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(rule sym)
   apply (rule epdaS.AX_marked_language_finite)
   apply (metis F_PARSER_TO_EDPDA_generates_epda F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_effect_def)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma F_PARSER_TO_EDPDA_preserves_lang2: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parserS.marked_language G \<supseteq> epdaS.marked_language (F_PARSER_TO_EDPDA G BOX)"
  apply(subgoal_tac "left_total_on (F_PARSER_TO_EDPDA__RL__relation_effect SSG1 SSG2) (epdaS.finite_marked_language SSG1) (parserS.finite_marked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule epdaS_parserS_P2A_StateSimRL.ATS_Simulation_Configuration_Weak_Marked_Effect_sound)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
   apply(force)
  apply(rule_tac
      t="parserS.marked_language G"
      and s="parserS.finite_marked_language G"
      in ssubst)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply (metis parserS.AX_marked_language_finite)
  apply(rule_tac
      t="epdaS.marked_language (F_PARSER_TO_EDPDA G BOX)"
      and s="epdaS.finite_marked_language (F_PARSER_TO_EDPDA G BOX)"
      in ssubst)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(rule sym)
   apply (rule epdaS.AX_marked_language_finite)
   apply (metis F_PARSER_TO_EDPDA_generates_epda F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_effect_def)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

theorem F_PARSER_TO_EDPDA_preserves_lang: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parserS.marked_language G = epdaS.marked_language (F_PARSER_TO_EDPDA G BOX)"
  apply(rule order_antisym)
   apply(metis F_PARSER_TO_EDPDA_preserves_lang1)
  apply(metis F_PARSER_TO_EDPDA_preserves_lang2)
  done

lemma F_PARSER_TO_EDPDA_preserves_unmarked_language1: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parserS.unmarked_language G \<subseteq> epdaS.unmarked_language (F_PARSER_TO_EDPDA G BOX)"
  apply(subgoal_tac "left_total_on (F_PARSER_TO_EDPDA__LR__relation_effect SSG1 SSG2) (parserS.finite_unmarked_language SSG1) (epdaS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule parserS_epdaS_P2A_StateSimLR.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_TSstructure_def)
   apply(force)
  apply(rule_tac
      t="parserS.unmarked_language G"
      and s="parserS.finite_unmarked_language G"
      in ssubst)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply (metis parserS.AX_unmarked_language_finite)
  apply(rule_tac
      t="epdaS.unmarked_language (F_PARSER_TO_EDPDA G BOX)"
      and s="epdaS.finite_unmarked_language (F_PARSER_TO_EDPDA G BOX)"
      in ssubst)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(rule sym)
   apply (rule epdaS.AX_unmarked_language_finite)
   apply (metis F_PARSER_TO_EDPDA_generates_epda F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__LR__relation_effect_def)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma F_PARSER_TO_EDPDA_preserves_unmarked_language2: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parserS.unmarked_language G \<supseteq> epdaS.unmarked_language (F_PARSER_TO_EDPDA G BOX)"
  apply(subgoal_tac "left_total_on (F_PARSER_TO_EDPDA__RL__relation_effect SSG1 SSG2) (epdaS.finite_unmarked_language SSG1) (parserS.finite_unmarked_language SSG2)" for SSG1 SSG2)
   prefer 2
   apply(rule epdaS_parserS_P2A_StateSimRL.ATS_Simulation_Configuration_Weak_Unmarked_Effect_sound)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
   apply(force)
  apply(rule_tac
      t="parserS.unmarked_language G"
      and s="parserS.finite_unmarked_language G"
      in ssubst)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply (metis parserS.AX_unmarked_language_finite)
  apply(rule_tac
      t="epdaS.unmarked_language (F_PARSER_TO_EDPDA G BOX)"
      and s="epdaS.finite_unmarked_language (F_PARSER_TO_EDPDA G BOX)"
      in ssubst)
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(rule sym)
   apply (rule epdaS.AX_unmarked_language_finite)
   apply (metis F_PARSER_TO_EDPDA_generates_epda F_PARSER_TO_EDPDA__SpecInput1_def)
  apply(simp add: left_total_on_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x b)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_effect_def)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

theorem F_PARSER_TO_EDPDA_preserves_unmarked_language: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parserS.unmarked_language G = epdaS.unmarked_language (F_PARSER_TO_EDPDA G BOX)"
  apply(rule order_antisym)
   apply(metis F_PARSER_TO_EDPDA_preserves_unmarked_language1)
  apply(metis F_PARSER_TO_EDPDA_preserves_unmarked_language2)
  done

definition F_PARSER_TO_EDPDA__LR__relation_initial_simulationRLB :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_initial_simulationRLB G1 G2 c1 c2 d \<equiv>
  d = der1 (F_PARSER_TO_EDPDA__configuration_rev G2 c1)"

definition F_PARSER_TO_EDPDA__LR__relation_step_simulationRLB :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event, 'stack) epda_step_label
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__LR__relation_step_simulationRLB G1 G2 c1 e1 c1' c2 d \<equiv>
  d = der2 (F_PARSER_TO_EDPDA__configuration_rev G2 c1) (F_PARSER_TO_EDPDA__rules_rev e1) (F_PARSER_TO_EDPDA__configuration_rev G2 c1')"

definition F_PARSER_TO_EDPDA__RL__relation_configurationB :: "
  ('stack, 'event, 'stack) epda
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'stack) epdaS_conf
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__RL__relation_configurationB G1 G2 c1 c2 \<equiv>
  \<exists>BOX.
    F_PARSER_TO_EDPDA__SpecInput1 G2 BOX
    \<and> G1 = F_PARSER_TO_EDPDA G2 BOX
    \<and> (\<exists>w.
        BOX \<notin> set w
        \<and> epdaS_conf_stack c1 = w @ [BOX])
    \<and> (F_PARSER_TO_EDPDA__configuration_rev G2 c1 = c2)"

lemma epdaS_parserS_P2A_StateSimRLB_inst_AX_relation_initial_simulationB: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1. c1 \<in> epdaS_initial_configurations G1 \<longrightarrow> (\<forall>c2. F_PARSER_TO_EDPDA__RL__relation_configurationB G1 G2 c1 c2 \<longrightarrow> (\<exists>d2. parserS.derivation_initial G2 d2 \<and> F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 c1 (the (get_configuration (d2 0))) \<and> F_PARSER_TO_EDPDA__LR__relation_initial_simulationRLB G1 G2 c1 c2 d2 \<and> (\<exists>n. maximum_of_domain d2 n \<and> get_configuration (d2 n) = Some c2)))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_configurationB_def F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_initial_simulationRLB_def)
  apply(rule conjI)
   apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
   apply(rule parserS.derivation_initialI)
    apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
    apply(rule parserS.der1_is_derivation)
   apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
   apply(simp add: der1_def get_configuration_def)
   apply(simp add: parserS_initial_configurations_def epdaS_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 BOX BOXa)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 c1 BOX BOXa)(*strict*)
    prefer 2
    apply(rule F_PARSER_TO_EDPDA__configuration_rev_preserves_configurations)
      apply(rename_tac G2 c1 BOX BOXa)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 BOX BOXa)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 BOX BOXa)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 BOX BOXa)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__configuration_rev_def)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def)
   apply(rule conjI)
    apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
    apply(force)
   apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
   apply(simp add: get_configuration_def der1_def)
  apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
   apply(rule der1_maximum_of_domain)
  apply(rename_tac G2 c1 BOX BOXa w)(*strict*)
  apply(simp add: get_configuration_def der1_def)
  done

lemma epdaS_parserS_P2A_StateSimRLB_inst_AX_relation_step_simulationB: "
  (\<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__RL__relation_configurationB G1 G2 c1 c2 \<longrightarrow> (\<forall>e1. e1 \<in> epda_step_labels G1 \<longrightarrow> (\<forall>c1'. c1' \<in> epdaS_configurations G1 \<longrightarrow> epdaS_step_relation G1 c1' e1 c1 \<longrightarrow> (\<exists>d2. parserS.derivation G2 d2 \<and> parserS.belongs G2 d2 \<and> (\<exists>n. the (get_configuration (d2 n)) = c2 \<and> F_PARSER_TO_EDPDA__LR__relation_step_simulationRLB G1 G2 c1' e1 c1 c2 d2 \<and> maximum_of_domain d2 n \<and> F_PARSER_TO_EDPDA__RL__relation_configurationB G1 G2 c1' (the (get_configuration (d2 0)))))))))"
  apply(clarsimp)
  apply(rename_tac G1 G2 c1 c2 e1 c1')(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_configurationB_def F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' BOX BOXa w)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__LR__relation_step_simulationRLB_def)
  apply(rule_tac
      x="der2 (F_PARSER_TO_EDPDA__configuration_rev G2 c1') (F_PARSER_TO_EDPDA__rules_rev e1) (F_PARSER_TO_EDPDA__configuration_rev G2 c1)"
      in exI)
  apply(rename_tac G2 c1 e1 c1' BOX BOXa w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "BOX=BOXa")
   apply(rename_tac G2 c1 e1 c1' BOX BOXa w)(*strict*)
   prefer 2
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G2 c1 e1 c1' BOX BOXa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' BOXa w)(*strict*)
  apply(rename_tac BOX w)
  apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
  apply(subgoal_tac "\<exists>w. BOX \<notin> set w \<and> epdaS_conf_stack c1' = w @ [BOX]")
   apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
   apply(subgoal_tac "\<forall>r \<in> epda_delta (F_PARSER_TO_EDPDA G2 BOX). epda_box (F_PARSER_TO_EDPDA G2 BOX) \<notin> set (edge_pop r) \<and> epda_box (F_PARSER_TO_EDPDA G2 BOX) \<notin> set (edge_push r)")
    apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
    prefer 2
    apply(rule F_PARSER_TO_EDPDA__SpecInput1_no_pop_of_box)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
   apply(erule_tac
      x="e1"
      in ballE)
    apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
   apply(case_tac wa)
    apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA_def)
    apply(subgoal_tac "BOX \<in> set (edge_push e1)")
     apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply (metis elem_set_app head_in_set)
   apply(rename_tac G2 c1 e1 c1' BOX w wa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. wa = w' @ [x']")
    apply(rename_tac G2 c1 e1 c1' BOX w wa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' BOX w wa a list)(*strict*)
   apply(thin_tac "wa=a#list")
   apply(clarsimp)
   apply(rename_tac G2 c1 e1 c1' w' x')(*strict*)
   apply(rename_tac BOX)
   apply(rename_tac G2 c1 e1 c1' w' BOX)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
   apply(rule parserS.der2_is_derivation)
   apply(rule F_PARSER_TO_EDPDA_preserves_steps_prime)
      apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
      apply(force)
     apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA_def)
    apply(rule_tac
      t="F_PARSER_TO_EDPDA__rules (F_PARSER_TO_EDPDA__rules_rev e1)"
      and s="e1"
      in ssubst)
     apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply(rule F_PARSER_TO_EDPDA__rules_F_PARSER_TO_EDPDA__rules_rev)
     apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
     apply(blast)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply(simp add: epda_step_labels_def)
    apply(simp add: F_PARSER_TO_EDPDA_def)
   apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
   apply(rule F_PARSER_TO_EDPDA__rules_rev_preserves_rules)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
   apply(rule parserS.der2_belongs)
     apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
     apply(rule_tac
      G="F_PARSER_TO_EDPDA G2 BOX"
      in F_PARSER_TO_EDPDA__configuration_rev_preserves_configurations)
       apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
       apply(force)
      apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
      apply(clarsimp)
      apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
      apply(simp add: F_PARSER_TO_EDPDA_def F_PARSER_TO_EDPDA__SpecInput1_def)
     apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply(simp add: parser_step_labels_def)
    apply(rule F_PARSER_TO_EDPDA__rules_rev_preserves_rules)
     apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
     apply(force)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply(force)
   apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
   apply(rule_tac
      G="F_PARSER_TO_EDPDA G2 BOX"
      and BOX="BOX"
      in F_PARSER_TO_EDPDA__configuration_rev_preserves_configurations)
     apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
     prefer 2
     apply(clarsimp)
     apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
     apply(simp add: F_PARSER_TO_EDPDA_def F_PARSER_TO_EDPDA__SpecInput1_def)
    apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
    apply (metis F_PARSER_TO_EDPDA_generates_epda epdaS.AX_step_relation_preserves_belongsC)
   apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 e1 c1' BOX w)(*strict*)
  apply(rule_tac
      x="Suc 0"
      in exI)
  apply(clarsimp)
  apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
   apply(simp add: der2_def get_configuration_def)
  apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
   apply(rule der2_maximum_of_domain)
  apply(rename_tac G2 c1 e1 c1' BOX w wa)(*strict*)
  apply(simp add: der2_def get_configuration_def)
  done

lemma epdaS_parserS_P2A_StateSimRLB_inst_AX_initial_contained: "
  \<forall>G1 G2. F_PARSER_TO_EDPDA__RL__relation_TSstructure G1 G2 \<longrightarrow> (\<forall>c1 c2. F_PARSER_TO_EDPDA__RL__relation_initial_configuration G1 G2 c1 c2 \<longrightarrow> F_PARSER_TO_EDPDA__RL__relation_configurationB G1 G2 c1 c2)"
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_initial_configuration_def F_PARSER_TO_EDPDA__RL__relation_configurationB_def)
  apply(clarsimp)
  apply(rename_tac G1 G2 c1)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
  apply(clarsimp)
  apply(rename_tac G2 c1 BOX)(*strict*)
  apply(rule_tac
      x="BOX"
      in exI)
  apply(rule conjI)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 BOX)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 c1 BOX)(*strict*)
   apply(force)
  apply(rename_tac G2 c1 BOX)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def epdaS_initial_configurations_def)
  apply(clarsimp)
  apply(simp add: F_PARSER_TO_EDPDA_def)
  done

lemma F_PARSER_TO_EDPDA_preserves_is_forward_edge_deterministic: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> valid_epda (F_PARSER_TO_EDPDA G BOX)
  \<Longrightarrow> parserS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.is_forward_edge_deterministic_accessible (F_PARSER_TO_EDPDA G BOX)"
  apply(subgoal_tac "parser_not_observes_input_terminator G")
   prefer 2
   apply(rule F_PARSER_TO_EDPDA__SpecInput1_implies_parser_not_observes_input_terminator)
   apply(force)
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e1 = epdaS_conf_state c")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "edge_src e2 = epdaS_conf_state c")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e1)) (epdaS_conf_scheduler c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e1 e2 w wa)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (option_to_list (edge_event e2)) (epdaS_conf_scheduler c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e1) (epdaS_conf_stack c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "prefix (edge_pop e2) (epdaS_conf_stack c)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e1 \<in> epda_delta (F_PARSER_TO_EDPDA G BOX)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "e2 \<in> epda_delta (F_PARSER_TO_EDPDA G BOX)")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: parserS.is_forward_edge_deterministic_accessible_def)
  apply(erule_tac
      x="F_PARSER_TO_EDPDA__configuration_rev G c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x="F_PARSER_TO_EDPDA__configuration_rev G c1"
      in allE)
   apply(erule_tac
      x="F_PARSER_TO_EDPDA__configuration_rev G c2"
      in allE)
   apply(subgoal_tac "e1 \<in> F_PARSER_TO_EDPDA__rules ` parser_rules G")
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_TO_EDPDA_def)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(thin_tac "e1 \<in> epda_delta (F_PARSER_TO_EDPDA G BOX)")
   apply(clarsimp)
   apply(rename_tac c c1 c2 e2 x)(*strict*)
   apply(subgoal_tac "e2 \<in> F_PARSER_TO_EDPDA__rules ` parser_rules G")
    apply(rename_tac c c1 c2 e2 x)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_TO_EDPDA_def)
   apply(rename_tac c c1 c2 e2 x)(*strict*)
   apply(thin_tac "e2 \<in> epda_delta (F_PARSER_TO_EDPDA G BOX)")
   apply(clarsimp)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G x")
    apply(rename_tac c c1 c2 x xa)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def valid_parser_def)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G xa")
    apply(rename_tac c c1 c2 x xa)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def valid_parser_def)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(erule_tac
      x="x"
      in allE)
   apply(erule_tac
      x="xa"
      in allE)
   apply(erule impE)
    apply(rename_tac c c1 c2 x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac c c1 c2 x xa)(*strict*)
    apply(rule F_PARSER_TO_EDPDA_preserves_steps)
       apply(rename_tac c c1 c2 x xa)(*strict*)
       apply(force)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(rule F_PARSER_TO_EDPDA_preserves_steps)
      apply(rename_tac c c1 c2 x xa)(*strict*)
      apply(force)
     apply(rename_tac c c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "F_PARSER_TO_EDPDA__configuration_rev G c \<in> parserS.get_accessible_configurations G")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(thin_tac "F_PARSER_TO_EDPDA__configuration_rev G c \<notin> parserS.get_accessible_configurations G")
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(rule_tac
      ?c1.0="c"
      and ?G1.0="F_PARSER_TO_EDPDA G BOX"
      in epdaS_parserS_P2A_StateSimRL.get_accessible_configurations_transfer)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
      apply(force)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     apply(rule_tac ?G.0="F_PARSER_TO_EDPDA G BOX" and BOX="BOX" in F_PARSER_TO_EDPDA__configuration_rev_preserves_configurations)
       apply(rename_tac c c1 c2 e1 e2)(*strict*)
       apply (metis epdaS.get_accessible_configurations_are_configurations2)
      apply(rename_tac c c1 c2 e1 e2)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac c c1 c2 e1 e2)(*strict*)
     prefer 2
     apply(simp add: F_PARSER_TO_EDPDA__RL__relation_configuration_def)
     apply(simp add: F_PARSER_TO_EDPDA__RL__relation_TSstructure_def)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2)(*strict*)
    prefer 2
    apply(rename_tac c c1 c2 e1 e2 cA cB)(*strict*)
    apply(simp add: F_PARSER_TO_EDPDA__RL__relation_configuration_def)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: epdaS.get_accessible_configurations_def get_configuration_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac c c1 c2 e1 e2 d i a option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
  apply(rule epda_no_use_epda_box_implies_stack_content)
     apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
     apply(force)
    apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d i option)(*strict*)
  apply(simp (no_asm) add: F_PARSER_TO_EDPDA__SpecInput1_def parser_not_observes_input_terminator_def F_PARSER_TO_EDPDA_def)
  apply(simp add: valid_epda_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i option r)(*strict*)
  apply(erule_tac x="F_PARSER_TO_EDPDA__rules r" in ballE)
   apply(rename_tac c c1 c2 e1 e2 d i option r)(*strict*)
   prefer 2
   apply(subgoal_tac "F_PARSER_TO_EDPDA__rules r \<in> epda_delta (F_PARSER_TO_EDPDA G BOX)")
    apply(rename_tac c c1 c2 e1 e2 d i option r)(*strict*)
    apply(force)
   apply(rename_tac c c1 c2 e1 e2 d i option r)(*strict*)
   apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(rename_tac c c1 c2 e1 e2 d i option r)(*strict*)
  apply(thin_tac "epdaS_step_relation (F_PARSER_TO_EDPDA G BOX) c e1 c1")
  apply(thin_tac "epdaS_step_relation (F_PARSER_TO_EDPDA G BOX) c e2 c2")
  apply(thin_tac "edge_src e1 = epdaS_conf_state c")
  apply(thin_tac "edge_src e2 = epdaS_conf_state c")
  apply(thin_tac "option_to_list (edge_event e1) \<sqsubseteq> epdaS_conf_scheduler c")
  apply(thin_tac "option_to_list (edge_event e2) \<sqsubseteq> epdaS_conf_scheduler c")
  apply(thin_tac "edge_pop e1 \<sqsubseteq> epdaS_conf_stack c")
  apply(thin_tac "edge_pop e2 \<sqsubseteq> epdaS_conf_stack c")
  apply(thin_tac "e1 \<in> epda_delta (F_PARSER_TO_EDPDA G BOX)")
  apply(thin_tac "e2 \<in> epda_delta (F_PARSER_TO_EDPDA G BOX)")
  apply(thin_tac "epdaS.derivation_initial (F_PARSER_TO_EDPDA G BOX) d")
  apply(thin_tac "d i = Some (pair option c) ")
  apply(thin_tac "epda_initial (F_PARSER_TO_EDPDA G BOX) \<in> epda_states (F_PARSER_TO_EDPDA G BOX)")
  apply(thin_tac "epda_box (F_PARSER_TO_EDPDA G BOX) \<in> epda_gamma (F_PARSER_TO_EDPDA G BOX)")
  apply(thin_tac "epda_marking (F_PARSER_TO_EDPDA G BOX) \<subseteq> epda_states (F_PARSER_TO_EDPDA G BOX)")
  apply(simp add: valid_epda_step_label_def)
  apply(rename_tac r)(*strict*)
  apply(simp (no_asm_use) add: F_PARSER_TO_EDPDA__SpecInput1_def parser_not_observes_input_terminator_def F_PARSER_TO_EDPDA_def F_PARSER_TO_EDPDA__rules_def valid_parser_def)
  apply(erule_tac x="r" in ballE)
   apply(rename_tac r)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(clarsimp)
  apply(erule_tac x="r" in ballE)
   apply(rename_tac r)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(erule_tac x="r" in ballE)
   apply(rename_tac r)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(simp add: must_terminated_by_def kleene_star_def append_language_def)
  apply(clarsimp)
  apply(case_tac r)
  apply(rename_tac r rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac a b c d)
  apply(rename_tac r a b c d)(*strict*)
  apply(clarsimp)
  apply(rename_tac a b c)(*strict*)
  apply(rule_tac xs="a" in rev_cases)
   apply(rename_tac a b c)(*strict*)
   apply(force)
  apply(rename_tac a b c ys y)(*strict*)
  apply(rule_tac xs="c" in rev_cases)
   apply(rename_tac a b c ys y)(*strict*)
   apply(force)
  apply(rename_tac a b c ys y ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac b ys y ysa ya)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac ys y ysa ya k w)(*strict*)
  apply(rule conjI)
   apply(rename_tac ys y ysa ya k w)(*strict*)
   apply(rule_tac B="parser_nonterms G" in nset_mp)
    apply(rename_tac ys y ysa ya k w)(*strict*)
    apply(force)
   apply(rename_tac ys y ysa ya k w)(*strict*)
   apply(force)
  apply(rename_tac ys y ysa ya k w)(*strict*)
  apply(rule_tac B="parser_nonterms G" in nset_mp)
   apply(rename_tac ys y ysa ya k w)(*strict*)
   apply(force)
  apply(rename_tac ys y ysa ya k w)(*strict*)
  apply(force)
  done

lemma F_PARSER_TO_EDPDA_determ_sound: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parserS.Nonblockingness_linear_DB G
  \<Longrightarrow> parserS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> epdaS.Nonblockingness_linear_DB (F_PARSER_TO_EDPDA G BOX)"
  apply(subgoal_tac "valid_epda (F_PARSER_TO_EDPDA G BOX)")
   prefer 2
   apply (metis F_PARSER_TO_EDPDA_generates_epda)
  apply(subgoal_tac "epdaS.Nonblockingness_linear_restricted_DB SSM" for SSM)
   prefer 2
   apply(rule epdaS.AX_BF_LinDBRest_DetR_LaOp)
     apply(force)
    apply(simp add: epdaS.is_forward_deterministic_accessible_def)
    apply(rule conjI)
     apply (metis epda_is_is_forward_target_deterministic_accessible)
    apply(rule F_PARSER_TO_EDPDA_preserves_is_forward_edge_deterministic)
      apply(force)
     apply(force)
    apply(simp add: parserS.is_forward_deterministic_accessible_def)
   apply(rule_tac
      t="epdaS.unmarked_language (F_PARSER_TO_EDPDA G BOX)"
      and s="parserS.unmarked_language G"
      in ssubst)
    apply (metis F_PARSER_TO_EDPDA_preserves_unmarked_language)
   apply(rule_tac
      t="epdaS.marked_language (F_PARSER_TO_EDPDA G BOX)"
      and s="parserS.marked_language G"
      in ssubst)
    apply (metis F_PARSER_TO_EDPDA_preserves_lang)
   apply(rule parserS.AX_BF_LinDB_OpLa)
    apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(force)
  apply(simp add: epdaS.Nonblockingness_linear_restricted_DB_def epdaS.Nonblockingness_linear_DB_def)
  done

lemma P2A_epda_no_empty_steps_from_marking_states: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> (\<forall>e. e \<in> parser_rules G \<longrightarrow> last (rule_lpop e) \<in> parser_marking G \<longrightarrow> rule_rpop e \<noteq> [])
  \<Longrightarrow> R = F_PARSER_TO_EDPDA G BOX
  \<Longrightarrow> q \<in> epda_marking R
  \<Longrightarrow> e \<in> epda_delta R
  \<Longrightarrow> edge_src e \<in> epda_marking R
  \<Longrightarrow> edge_event e \<noteq> None"
  apply(simp add: F_PARSER_TO_EDPDA_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_PARSER_TO_EDPDA__rules_def)
  apply(simp add: list_to_option_def)
  apply(case_tac "rule_rpop x")
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x a list)(*strict*)
  apply(force)
  done

lemma F_PARSER_TO_EDPDA_enforces_epda_no_empty_steps_from_marking_states: "
  F_PARSER_TO_EDPDA__SpecInput1 G BOX
  \<Longrightarrow> parser_no_empty_steps_from_marking_states G
  \<Longrightarrow> epda_no_empty_steps_from_marking_states (F_PARSER_TO_EDPDA G BOX)"
  apply(simp add: epda_no_empty_steps_from_marking_states_def parser_no_empty_steps_from_marking_states_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rule P2A_epda_no_empty_steps_from_marking_states)
        apply(rename_tac e)(*strict*)
        apply(force)
       apply(rename_tac e)(*strict*)
       apply(force)
      apply(rename_tac e)(*strict*)
      apply(force)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(force)
  done

definition F_PARSER_TO_EDPDA__SpecInput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> 'stack
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__SpecInput G BOX \<equiv>
  valid_bounded_parser G (Suc 0)
  \<and> BOX \<notin> parser_nonterms G
  \<and> parserFS.is_forward_edge_deterministic_accessible G
  \<and> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<and> parser_not_observes_input_terminator G
  \<and> parser_no_top_rules G
  \<and> parser_no_empty_steps_from_marking_states G"

definition F_PARSER_TO_EDPDA__SpecOutput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('state, 'event, 'stackx) epda
  \<Rightarrow> bool"
  where
    "F_PARSER_TO_EDPDA__SpecOutput Gi Go \<equiv>
  valid_epda Go
  \<and> epdaS.is_forward_edge_deterministic_accessible Go
  \<and> parserS.marked_language Gi = epdaS.marked_language Go
  \<and> nonblockingness_language (epdaS.unmarked_language Go) (epdaS.marked_language Go)
  \<and> epda_no_empty_steps_from_marking_states Go"

theorem F_PARSER_TO_EDPDA__SOUND: "
  F_PARSER_TO_EDPDA__SpecInput G BOX
  \<Longrightarrow> F_PARSER_TO_EDPDA__SpecOutput G (F_PARSER_TO_EDPDA G BOX)"
  apply(simp add: F_PARSER_TO_EDPDA__SpecInput_def F_PARSER_TO_EDPDA__SpecOutput_def)
  apply(clarsimp)
  apply(subgoal_tac "F_PARSER_TO_EDPDA__SpecInput1 G BOX")
   prefer 2
   apply(simp add: F_PARSER_TO_EDPDA__SpecInput1_def)
   apply(simp add: valid_bounded_parser_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(simp add: parser_no_top_rules_def)
   apply(subgoal_tac "valid_parser_step_label G r")
    apply(rename_tac r)(*strict*)
    prefer 2
    apply(simp add: valid_parser_def)
   apply(rename_tac r)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rule context_conjI)
   apply(rule F_PARSER_TO_EDPDA_generates_epda)
   apply(force)
  apply(rule conjI)
   apply(rule F_PARSER_TO_EDPDA_preserves_is_forward_edge_deterministic)
     apply(force)
    apply(force)
   apply(rule_tac parserS_vs_parserFS.preserve_FEdetermR2)
    prefer 2
    apply(force)
   apply(simp add: valid_bounded_parser_def)
  apply(rule context_conjI)
   apply(rule F_PARSER_TO_EDPDA_preserves_lang)
   apply(force)
  apply(rule conjI)
   apply(subgoal_tac "parserS.unmarked_language G = epdaS.unmarked_language (F_PARSER_TO_EDPDA G BOX)")
    apply(force)
   apply(rule F_PARSER_TO_EDPDA_preserves_unmarked_language)
   apply(force)
  apply(rule F_PARSER_TO_EDPDA_enforces_epda_no_empty_steps_from_marking_states)
   apply(force)
  apply(force)
  done

end

