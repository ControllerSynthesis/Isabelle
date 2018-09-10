section {*FUNCTION\_\_PARSERRITU\_\_PARSER\_REMOVE\_INPUT\_TERMIANTOR\_USAGE*}
theory
  FUNCTION__PARSERRITU__PARSER_REMOVE_INPUT_TERMIANTOR_USAGE

imports
  PRJ_12_06_06__ENTRY

begin

lemma F_PARSER_RITU_valid_bounded_parser: "
  valid_bounded_parser P k
  \<Longrightarrow> valid_bounded_parser (F_PARSER_RITU P) k"
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(rule conjI)
   prefer 2
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(simp add: F_PARSER_RITU_def)
  apply(thin_tac "\<forall>e\<in> parser_rules P. length (rule_rpop e) \<le> k")
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: F_PARSER_RITU_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_RITU_def)
  apply(rule conjI)
   apply(simp add: F_PARSER_RITU_def)
  apply(rule conjI)
   prefer 2
   apply(rule conjI)
    apply(simp add: F_PARSER_RITU_def)
   apply(rule conjI)
    prefer 2
    apply(simp add: F_PARSER_RITU_def)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac e)(*strict*)
    prefer 2
    apply(simp add: F_PARSER_RITU_def)
   apply(rename_tac e)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac e k w xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac e k w xa)(*strict*)
    apply(rule_tac
      x="k"
      in exI)
    apply(rule inMap)
    apply(rule_tac
      x="(w @ [parser_bottom P])"
      in bexI)
     apply(rename_tac e k w xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac e k w xa)(*strict*)
    apply(clarsimp)
    apply(simp add: F_PARSER_RITU_def)
   apply(rename_tac e k w xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac e k w xa)(*strict*)
    apply(simp add: F_PARSER_RITU_def)
   apply(rename_tac e k w xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac e k w xa)(*strict*)
    apply(simp add: F_PARSER_RITU_def)
   apply(rename_tac e k w xa)(*strict*)
   apply(rule conjI)
    apply(rename_tac e k w xa)(*strict*)
    apply(simp add: F_PARSER_RITU_def)
   apply(rename_tac e k w xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e k w xa x)(*strict*)
   apply(erule impE)
    apply(rename_tac e k w xa x)(*strict*)
    apply(rule_tac
      x="x"
      in exI)
    apply(simp add: F_PARSER_RITU_def)
   apply(rename_tac e k w xa x)(*strict*)
   apply(clarsimp)
   apply(rename_tac e k w xa x xb)(*strict*)
   apply(rule_tac
      x="xb"
      in exI)
   apply(simp add: F_PARSER_RITU_def)
  apply(simp add: F_PARSER_RITU_def)
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(erule_tac
      x="r"
      in ballE)
   apply(rename_tac r)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac r k w xa xb)(*strict*)
  apply(rule last_in_set_X)
   apply(rename_tac r k w xa xb)(*strict*)
   apply(force)
  apply(rename_tac r k w xa xb)(*strict*)
  apply(force)
  done

lemma F_PARSER_RITU_makes_parser_not_observes_input_terminator: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> P' = F_PARSER_RITU P
  \<Longrightarrow> parser_not_observes_input_terminator P'"
  apply(simp add: F_PARSER_RITU_def parser_not_observes_input_terminator_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P e")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac e)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(case_tac "rule_rpop e")
   apply(rename_tac e)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac e a list)(*strict*)
  apply(case_tac list)
   apply(rename_tac e a list)(*strict*)
   prefer 2
   apply(rename_tac e a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac e a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e a)(*strict*)
  apply(case_tac "rule_rpush e")
   apply(rename_tac e a)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac e a aa list)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac e a aa list k w xa)(*strict*)
  apply(subgoal_tac "xa@aa#list=[a]")
   apply(rename_tac e a aa list k w xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e a aa list k w xa)(*strict*)
  apply(thin_tac "xa @ aa # list = kPrefix k (w @ [parser_bottom P])")
  apply(thin_tac "[a] = kPrefix k (w @ [parser_bottom P])")
  apply(subgoal_tac "xa=[]")
   apply(rename_tac e a aa list k w xa)(*strict*)
   prefer 2
   apply(case_tac xa)
    apply(rename_tac e a aa list k w xa)(*strict*)
    apply(force)
   apply(rename_tac e a aa list k w xa ab lista)(*strict*)
   apply(force)
  apply(rename_tac e a aa list k w xa)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_RITU_preserves_derivation_initial: "
  valid_bounded_parser P k
  \<Longrightarrow> valid_bounded_parser (F_PARSER_RITU P) k
  \<Longrightarrow> parserS.derivation_initial P d
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> parser_fixed_input_length_recN d n < length (parserS_conf_scheduler c)
  \<Longrightarrow> parserS.derivation_initial (F_PARSER_RITU P) d"
  apply(simp (no_asm) add: parserS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    prefer 2
    apply(rule parserS.some_position_has_details_at_0)
    apply(force)
   apply(clarsimp)
   apply(rename_tac ca)(*strict*)
   apply(simp add: parserS_initial_configurations_def parserS.derivation_initial_def)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def F_PARSER_RITU_def)
  apply(simp (no_asm) add: parserS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: parserS.derivation_def)
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_step_relation_def F_PARSER_RITU_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d n = length (parserS_conf_scheduler c)")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(thin_tac "parser_fixed_input_length_recN d n < length (parserS_conf_scheduler c)")
  apply(subgoal_tac "Suc nat \<le> n")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(rule parserS.allPreMaxDomSome_prime)
     apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "parserS.belongs P d")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(rule parserS.derivation_initial_belongs)
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc nat)) \<ge> length (parserS_conf_scheduler c) - (parser_fixed_input_length_recN d ((Suc nat)+(n-Suc nat)))")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(rule_tac
      P="P"
      in PARSER_UnseenPartStrictlyDecreases)
       apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
       apply(simp add: valid_bounded_parser_def)
      apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d (Suc nat) = length (parserS_conf_scheduler c2)")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c)")
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    prefer 2
    apply(rule_tac
      M="P"
      in PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
       apply(simp add: valid_bounded_parser_def)
      apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "rule_rpush e2 = [parser_bottom P]")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(subgoal_tac "valid_parser_step_label P e2")
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa ka w xc xd)(*strict*)
    apply(case_tac xc)
     apply(rename_tac nat e1 e2 c1 c2 x xa ka w xc xd)(*strict*)
     apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa ka w xc xd a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "xa=[]")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c2 x xa w)(*strict*)
   apply(case_tac xa)
    apply(rename_tac nat e1 e2 c2 x xa w)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat e1 e2 c2 x xa w a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac nat e1 e2 c2 x xa w a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac nat e1 e2 c2 x xa w a list)(*strict*)
   apply(thin_tac "xa=a#list")
   apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d nat \<le> length (parserS_conf_scheduler c1)")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(rule_tac
      M="P"
      in PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
      apply(simp add: valid_bounded_parser_def)
     apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(force)
  done

lemma F_PARSER_RITU_reflects_derivation: "
  parserS.derivation (F_PARSER_RITU P) d
  \<Longrightarrow> parserS.derivation P d"
  apply(simp (no_asm) add: parserS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(simp add: parserS.derivation_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation (F_PARSER_RITU P) c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(force)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_step_relation_def F_PARSER_RITU_def)
  done

lemma F_PARSER_RITU_reflects_derivation_initial: "
  parserS.derivation_initial (F_PARSER_RITU P) d
  \<Longrightarrow> parserS.derivation_initial P d"
  apply(simp add: parserS.derivation_initial_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rule F_PARSER_RITU_reflects_derivation)
   apply(force)
  apply(case_tac "d 0")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac b)(*strict*)
  apply(simp add: parserS_initial_configurations_def F_PARSER_RITU_def parserS_configurations_def)
  done

lemma F_PARSER_RITU_preserves_all_rules_pop: "
  \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> \<forall>r \<in> parser_rules (F_PARSER_RITU P) . rule_rpop r \<noteq> []"
  apply(simp add: F_PARSER_RITU_def)
  done

lemma F_PARSER_RITU_preserves_configurations: "
  c \<in> parserS_configurations P
  \<Longrightarrow> c \<in> parserS_configurations (F_PARSER_RITU P)"
  apply(simp add: parserS_configurations_def F_PARSER_RITU_def)
  done

lemma F_PARSER_RITU_reflects_configurations: "
  c \<in> parserS_configurations (F_PARSER_RITU P)
  \<Longrightarrow> c \<in> parserS_configurations P"
  apply(simp add: parserS_configurations_def F_PARSER_RITU_def)
  done

lemma F_PARSER_RITU_preserves_marked_language1: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> parser_no_access_final_with_read P
  \<Longrightarrow> parser_initial P \<notin> parser_marking P
  \<Longrightarrow> valid_bounded_parser (F_PARSER_RITU P) (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> parserS.marked_language P \<subseteq> parserS.marked_language (F_PARSER_RITU P)"
  apply(simp add: parserS.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(simp add: parserS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac d c i e cb)(*strict*)
  apply(subgoal_tac "\<exists>d. (parserS.derivation_initial P d \<and> parserS.derivation P d \<and> d 0 = Some (pair None c) \<and> d i = Some (pair e cb)) \<and> maximum_of_domain d i ")
   apply(rename_tac d c i e cb)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in derivation_extend_with_maximum_of_domain)
     apply(rename_tac d c i e cb)(*strict*)
     apply(force)
    apply(rename_tac d c i e cb)(*strict*)
    apply(force)
   apply(rename_tac d c i e cb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c i e cb)(*strict*)
    apply(rule parserS.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac d c i e cb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c i e cb)(*strict*)
    apply(rule parserS.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d c i e cb)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c i e cb)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d c i e cb)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d c i e cb)(*strict*)
  apply(thin_tac "parserS.derivation_initial P d")
  apply(rename_tac d c i e cb)(*strict*)
  apply(thin_tac "parserS.derivation P d")
  apply(thin_tac "d 0 = Some (pair None c)")
  apply(thin_tac "d i = Some (pair e cb)")
  apply(clarsimp)
  apply(rename_tac c i e cb d)(*strict*)
  apply(subgoal_tac "parserS.belongs P d")
   apply(rename_tac c i e cb d)(*strict*)
   prefer 2
   apply(rule parserS.derivation_initial_belongs)
    apply(rename_tac c i e cb d)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac c i e cb d)(*strict*)
   apply(force)
  apply(rename_tac c i e cb d)(*strict*)
  apply(case_tac "parser_fixed_input_length_rec1 d i = Suc 0")
   apply(rename_tac c i e cb d)(*strict*)
   apply(subgoal_tac "\<exists>k e c. d k = Some (pair e c) \<and> parserS_conf_scheduler c = [parser_bottom P] \<and> parser_fixed_input_length_rec1 d k = 0 \<and> parser_fixed_input_length_rec1 d (Suc k) = Suc 0")
    apply(rename_tac c i e cb d)(*strict*)
    prefer 2
    apply(rule_tac
      n="i"
      in PARSER1_latest_point_where_input_bottom_not_seen)
          apply(rename_tac c i e cb d)(*strict*)
          apply(force)
         apply(rename_tac c i e cb d)(*strict*)
         apply(force)
        apply(rename_tac c i e cb d)(*strict*)
        apply(force)
       apply(rename_tac c i e cb d)(*strict*)
       apply(force)
      apply(rename_tac c i e cb d)(*strict*)
      apply(simp add: parserS_marking_configurations_def)
     apply(rename_tac c i e cb d)(*strict*)
     apply(force)
    apply(rename_tac c i e cb d)(*strict*)
    apply(force)
   apply(rename_tac c i e cb d)(*strict*)
   apply(clarsimp)
   apply(rename_tac c i e cb d k ea ca)(*strict*)
   apply(rule_tac
      x="derivation_take d k"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac c i e cb d k ea ca)(*strict*)
    apply(rule F_PARSER_RITU_preserves_derivation_initial)
          apply(rename_tac c i e cb d k ea ca)(*strict*)
          apply(force)
         apply(rename_tac c i e cb d k ea ca)(*strict*)
         apply(force)
        apply(rename_tac c i e cb d k ea ca)(*strict*)
        apply(rule parserS.derivation_take_preserves_derivation_initial)
        apply(force)
       apply(rename_tac c i e cb d k ea ca)(*strict*)
       apply(rule parserS.derivation_take_preserves_derivation)
       apply(force)
      apply(rename_tac c i e cb d k ea ca)(*strict*)
      apply(rule maximum_of_domain_derivation_take)
      apply(force)
     apply(rename_tac c i e cb d k ea ca)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac c i e cb d k ea ca)(*strict*)
    apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d k) k"
      and s="parser_fixed_input_length_recN d k"
      in ssubst)
     apply(rename_tac c i e cb d k ea ca)(*strict*)
     apply(rule parser_fixed_input_length_recN_with_derivation_take)
     apply(force)
    apply(rename_tac c i e cb d k ea ca)(*strict*)
    apply(rule_tac
      t="parser_fixed_input_length_recN d k"
      and s="parser_fixed_input_length_rec1 d k"
      in ssubst)
     apply(rename_tac c i e cb d k ea ca)(*strict*)
     apply(rule PARSER1_parser_fixed_input_length_recN_replacement)
        apply(rename_tac c i e cb d k ea ca)(*strict*)
        apply(force)
       apply(rename_tac c i e cb d k ea ca)(*strict*)
       apply(force)
      apply(rename_tac c i e cb d k ea ca)(*strict*)
      apply(force)
     apply(rename_tac c i e cb d k ea ca)(*strict*)
     apply(force)
    apply(rename_tac c i e cb d k ea ca)(*strict*)
    apply(force)
   apply(rename_tac c i e cb d k ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac c i e cb d k ea ca)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac c i e cb d k ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac c i e cb d k ea ca)(*strict*)
    apply(simp add: parserS.derivation_initial_def)
   apply(rename_tac c i e cb d k ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac c i e cb d k ea ca)(*strict*)
    apply(simp add: derivation_take_def)
    apply(rule F_PARSER_RITU_preserves_configurations)
    apply(force)
   apply(rename_tac c i e cb d k ea ca)(*strict*)
   apply(rule_tac
      x="k"
      in exI)
   apply(rule_tac
      x="ea"
      in exI)
   apply(rule_tac
      x="ca"
      in exI)
   apply(rule conjI)
    apply(rename_tac c i e cb d k ea ca)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac c i e cb d k ea ca)(*strict*)
   apply(simp add: parserS_marking_configurations_def)
   apply(clarsimp)
   apply(rename_tac c i e cb d k ea ca f w)(*strict*)
   apply(subgoal_tac "ca \<in> parserS_configurations P")
    apply(rename_tac c i e cb d k ea ca f w)(*strict*)
    prefer 2
    apply(simp add: parserS.belongs_def)
    apply(erule_tac
      x="k"
      in allE)
    apply(force)
   apply(rename_tac c i e cb d k ea ca f w)(*strict*)
   apply(rule conjI)
    apply(rename_tac c i e cb d k ea ca f w)(*strict*)
    prefer 2
    apply(rule conjI)
     apply(rename_tac c i e cb d k ea ca f w)(*strict*)
     apply(simp add: F_PARSER_RITU_def)
    apply(rename_tac c i e cb d k ea ca f w)(*strict*)
    apply(rule F_PARSER_RITU_preserves_configurations)
    apply(force)
   apply(rename_tac c i e cb d k ea ca f w)(*strict*)
   apply(case_tac "d (Suc k)")
    apply(rename_tac c i e cb d k ea ca f w)(*strict*)
    apply(clarsimp)
   apply(rename_tac c i e cb d k ea ca f w a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d k = Some (pair e1 c1) \<and> d (Suc k) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
    apply(rename_tac c i e cb d k ea ca f w a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc k"
      in parserS.step_detail_before_some_position)
      apply(rename_tac c i e cb d k ea ca f w a)(*strict*)
      apply(force)
     apply(rename_tac c i e cb d k ea ca f w a)(*strict*)
     apply(force)
    apply(rename_tac c i e cb d k ea ca f w a)(*strict*)
    apply(force)
   apply(rename_tac c i e cb d k ea ca f w a)(*strict*)
   apply(clarsimp)
   apply(rename_tac c i e cb d k ea ca f w e2 c2)(*strict*)
   apply(subgoal_tac "valid_parser_step_label P e2")
    apply(rename_tac c i e cb d k ea ca f w e2 c2)(*strict*)
    prefer 2
    apply(rule valid_parser_implies_valid_parser_step_label)
     apply(rename_tac c i e cb d k ea ca f w e2 c2)(*strict*)
     apply(simp add: valid_bounded_parser_def)
    apply(rename_tac c i e cb d k ea ca f w e2 c2)(*strict*)
    apply(simp add: parserS_step_relation_def)
   apply(rename_tac c i e cb d k ea ca f w e2 c2)(*strict*)
   apply(case_tac "rule_lpop e2")
    apply(rename_tac c i e cb d k ea ca f w e2 c2)(*strict*)
    apply(simp add: parserS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac c i e cb d k ea ca f w e2 c2 x)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_lpop e2 = w' @ [x']")
    apply(rename_tac c i e cb d k ea ca f w e2 c2 a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 a list)(*strict*)
   apply(thin_tac "rule_lpop e2=a#list")
   apply(clarsimp)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x')(*strict*)
   apply(rule_tac
      x="x'"
      in bexI)
    apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x')(*strict*)
    apply(simp add: parserS_step_relation_def)
    apply(clarsimp)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x')(*strict*)
   apply(rule_tac
      t="parser_marking (F_PARSER_RITU P)"
      and s="{n. \<exists>r\<in> parser_rules P. rule_rpop r = [parser_bottom P] \<and> n=last(rule_lpop r)}"
      in ssubst)
    apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x')(*strict*)
    apply(simp add: F_PARSER_RITU_def)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x')(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="e2"
      in bexI)
    apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x')(*strict*)
    prefer 2
    apply(simp add: parserS_step_relation_def)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x')(*strict*)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x' x xa)(*strict*)
   apply(case_tac xa)
    apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x' x xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x' x xa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x' x xa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac c i e cb d k ea ca f w e2 c2 w' x' x xa a list)(*strict*)
   apply(thin_tac "xa=a#list")
   apply(clarsimp)
  apply(rename_tac c i e cb d)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac c i e cb d)(*strict*)
   apply(force)
  apply(rename_tac c i e cb d)(*strict*)
  apply(case_tac i)
   apply(rename_tac c i e cb d)(*strict*)
   apply(clarsimp)
   apply(rename_tac cb d)(*strict*)
   apply(simp add: parserS_initial_configurations_def parserS_marking_configurations_def parserS.derivation_initial_def)
  apply(rename_tac c i e cb d nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac c e cb d nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
   apply(rename_tac c e cb d nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac c e cb d nat)(*strict*)
     apply(force)
    apply(rename_tac c e cb d nat)(*strict*)
    apply(force)
   apply(rename_tac c e cb d nat)(*strict*)
   apply(force)
  apply(rename_tac c e cb d nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac c cb d nat e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac c cb d nat e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: parserS_step_relation_def)
  apply(rename_tac c cb d nat e1 e2 c1)(*strict*)
  apply(case_tac "rule_rpop e2")
   apply(rename_tac c cb d nat e1 e2 c1)(*strict*)
   apply(clarsimp)
  apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label P e2")
   apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
   apply(simp add: parserS_step_relation_def)
  apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
  apply(subgoal_tac "list=[]")
   apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
   prefer 2
   apply(simp add: valid_bounded_parser_def)
   apply(clarsimp)
   apply(erule_tac
      A="parser_rules P"
      and x="e2"
      and P="\<lambda>e2. length (rule_rpop e2) \<le> Suc 0"
      in ballE)
    apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
    prefer 2
    apply(simp add: parserS_step_relation_def)
   apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac c cb d nat e1 e2 c1 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac c cb d nat e1 e2 c1 a)(*strict*)
  apply(subgoal_tac "rule_rpush e2 = []")
   apply(rename_tac c cb d nat e1 e2 c1 a)(*strict*)
   prefer 2
   apply(case_tac "rule_rpush e2")
    apply(rename_tac c cb d nat e1 e2 c1 a)(*strict*)
    apply(force)
   apply(rename_tac c cb d nat e1 e2 c1 a aa list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_rpush e2 = w' @ [x']")
    apply(rename_tac c cb d nat e1 e2 c1 a aa list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac c cb d nat e1 e2 c1 a aa list)(*strict*)
   apply(thin_tac "rule_rpush e2=aa#list")
   apply(clarsimp)
   apply(rename_tac c cb d nat e1 e2 c1 a w' x')(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac c cb d nat e1 e2 c1 a)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_marking_configurations_def parserS_initial_configurations_def parserS.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac c cb d nat e1 e2 c1 a f w)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c cb d nat e1 e2 c1 a f w x)(*strict*)
  apply(simp add: parser_no_access_final_with_read_def)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac c cb d nat e1 e2 c1 a f w x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c cb d nat e1 e2 c1 a f w x)(*strict*)
  apply(clarsimp)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac c cb d nat e1 e2 c1 a f w x k wa)(*strict*)
  apply(case_tac "rule_lpush e2")
   apply(rename_tac c cb d nat e1 e2 c1 a f w x k wa)(*strict*)
   apply(blast)
  apply(rename_tac c cb d nat e1 e2 c1 a f w x k wa aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. rule_lpush e2 = w' @ [x']")
   apply(rename_tac c cb d nat e1 e2 c1 a f w x k wa aa list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac c cb d nat e1 e2 c1 a f w x k wa aa list)(*strict*)
  apply(thin_tac "rule_lpush e2=aa#list")
  apply(clarsimp)
  done

lemma F_PARSER_RITU_parserS_entire_input_observed_never: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> valid_bounded_parser (F_PARSER_RITU P) (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> parserS_entire_input_observed (F_PARSER_RITU P) c
  \<Longrightarrow> Q"
  apply(simp add: parserS_entire_input_observed_def)
  apply(clarsimp)
  apply(rename_tac d e n)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c = w @ [parser_bottom (F_PARSER_RITU P)]")
   apply(rename_tac d e n)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(force)
  apply(rename_tac d e n)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e n w)(*strict*)
  apply(case_tac n)
   apply(rename_tac d e n w)(*strict*)
   apply(clarsimp)
  apply(rename_tac d e n w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d e w nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation (F_PARSER_RITU P) c1 e2 c2")
   apply(rename_tac d e w nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac d e w nat)(*strict*)
     apply(force)
    apply(rename_tac d e w nat)(*strict*)
    apply(force)
   apply(rename_tac d e w nat)(*strict*)
   apply(force)
  apply(rename_tac d e w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c1 = w @ [parser_bottom (F_PARSER_RITU P)]")
   apply(rename_tac d w nat e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(force)
  apply(rename_tac d w nat e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
  apply(subgoal_tac "length (rule_rpop e2) \<le> Suc 0")
   apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
   prefer 2
   apply(simp add: valid_bounded_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="e2"
      and A="parser_rules (F_PARSER_RITU P)"
      in ballE)
    apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
    prefer 2
    apply(simp add: parserS_step_relation_def)
   apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
   apply(force)
  apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label (F_PARSER_RITU P) e2")
   apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
   prefer 2
   apply(rule valid_parser_implies_valid_parser_step_label)
    apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
   apply(simp add: parserS_step_relation_def)
  apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
   prefer 2
   apply(simp add: parserS_step_relation_def F_PARSER_RITU_def)
  apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
  apply(case_tac "rule_rpop e2")
   apply(rename_tac d w nat e1 e2 c1 wa)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w nat e1 e2 c1 wa a list)(*strict*)
  apply(case_tac list)
   apply(rename_tac d w nat e1 e2 c1 wa a list)(*strict*)
   prefer 2
   apply(rename_tac d w nat e1 e2 c1 wa a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac d w nat e1 e2 c1 wa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d w nat e1 e2 c1 wa a)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d w nat e1 e2 c1 wa a x xa)(*strict*)
  apply(case_tac wa)
   apply(rename_tac d w nat e1 e2 c1 wa a x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w nat e1 e2 c1 x)(*strict*)
   apply(simp add: F_PARSER_RITU_def)
  apply(rename_tac d w nat e1 e2 c1 wa a x xa aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) (Suc 0) = Suc 0")
   apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
   prefer 2
   apply(subgoal_tac "parser_fixed_input_length_recN d nat \<le> Suc 0")
    apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
    prefer 2
    apply(rule_tac
      M="F_PARSER_RITU P"
      in parser_fixed_input_length_recN_maximum)
      apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
      apply(force)
     apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
     apply(force)
    apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
    apply(force)
   apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
   apply(force)
  apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
  apply(clarsimp)
  apply(case_tac "rule_rpush e2")
   apply(rename_tac d nat e1 e2 c1 a x list)(*strict*)
   apply(clarsimp)
  apply(rename_tac d nat e1 e2 c1 a x list aa lista)(*strict*)
  apply(subgoal_tac "rule_rpush e2 = [a]")
   apply(rename_tac d nat e1 e2 c1 a x list aa lista)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac d nat e1 e2 c1 a x list aa lista)(*strict*)
  apply(clarsimp)
  done

lemma F_PARSER_RITU_preserves_marked_language2: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> parserS.is_forward_deterministic_accessible P
  \<Longrightarrow> can_detect_parser_bottom_only_in_Nonblockingness_configurations P
  \<Longrightarrow> valid_bounded_parser (F_PARSER_RITU P) (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> parserS.marked_language P \<supseteq> parserS.marked_language (F_PARSER_RITU P)"
  apply(simp add: parserS.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(simp add: parserS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac d c i e cb)(*strict*)
  apply(subgoal_tac "parserS.Nonblockingness_configuration P cb")
   apply(rename_tac d c i e cb)(*strict*)
   apply(simp add: parserS.Nonblockingness_configuration_def)
   apply(clarsimp)
   apply(rename_tac d c i e cb da)(*strict*)
   apply(rule_tac
      x="derivation_append d da i"
      in exI)
   apply(subgoal_tac "parserS.derivation P (derivation_append d da i)")
    apply(rename_tac d c i e cb da)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac d c i e cb da)(*strict*)
     apply(rule parserS.derivation_append_preserves_derivation_initial)
       apply(rename_tac d c i e cb da)(*strict*)
       apply(simp add: valid_bounded_parser_def)
      apply(rename_tac d c i e cb da)(*strict*)
      apply(rule F_PARSER_RITU_reflects_derivation_initial)
      apply(force)
     apply(rename_tac d c i e cb da)(*strict*)
     apply(force)
    apply(rename_tac d c i e cb da)(*strict*)
    apply(simp add: derivation_append_def)
    apply(rule conjI)
     apply(rename_tac d c i e cb da)(*strict*)
     apply(rule F_PARSER_RITU_reflects_configurations)
     apply(force)
    apply(rename_tac d c i e cb da)(*strict*)
    apply(simp add: parserS_marking_condition_def)
    apply(clarsimp)
    apply(rename_tac d c i e cb da ia ea ca)(*strict*)
    apply(rule_tac
      x="i+ia"
      in exI)
    apply(clarsimp)
   apply(rename_tac d c i e cb da)(*strict*)
   apply(rule parserS.derivation_append_preserves_derivation)
     apply(rename_tac d c i e cb da)(*strict*)
     apply(rule F_PARSER_RITU_reflects_derivation)
     apply(force)
    apply(rename_tac d c i e cb da)(*strict*)
    apply(force)
   apply(rename_tac d c i e cb da)(*strict*)
   apply(clarsimp)
  apply(rename_tac d c i e cb)(*strict*)
  apply(simp add: can_detect_parser_bottom_only_in_Nonblockingness_configurations_def)
  apply(simp add: parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac d c i e cb f w)(*strict*)
  apply(subgoal_tac "f \<in> {n. \<exists>r\<in> parser_rules P. rule_rpop r = [parser_bottom P] \<and> n=last(rule_lpop r)}")
   apply(rename_tac d c i e cb f w)(*strict*)
   prefer 2
   apply(rule_tac
      t="{n. \<exists>r\<in> parser_rules P. rule_rpop r = [parser_bottom P] \<and> n=last(rule_lpop r)}"
      and s="parser_marking (F_PARSER_RITU P)"
      in ssubst)
    apply(rename_tac d c i e cb f w)(*strict*)
    apply(simp add: F_PARSER_RITU_def)
   apply(rename_tac d c i e cb f w)(*strict*)
   apply(simp add: F_PARSER_RITU_def)
  apply(rename_tac d c i e cb f w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply(erule_tac
      x="derivation_take d i"
      in allE)
  apply(erule impE)
   apply(rule parserS.derivation_take_preserves_derivation_initial)
   apply (metis F_PARSER_RITU_reflects_derivation_initial)
  apply(erule_tac
      x="r"
      in allE)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(erule impE)
   apply (metis not_None_eq maximum_of_domain_derivation_take)
  apply(erule impE)
   prefer 2
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(simp add: get_configuration_def derivation_take_def)
   apply(simp add: F_PARSER_RITU_def)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply(case_tac "parserS_entire_input_observed (F_PARSER_RITU P) cb")
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(rule F_PARSER_RITU_parserS_entire_input_observed_never)
      apply(rename_tac d c i e cb w r)(*strict*)
      apply(force)
     apply(rename_tac d c i e cb w r)(*strict*)
     apply(force)
    apply(rename_tac d c i e cb w r)(*strict*)
    apply(force)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(force)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply(simp add: parserS_entire_input_observed_def)
  apply(erule_tac
      x="derivation_take d i"
      in allE)
  apply(erule impE)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(rule parserS.derivation_take_preserves_derivation_initial)
   apply (metis)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply(erule impE)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(rule parserS.derivation_initial_belongs)
    apply(rename_tac d c i e cb w r)(*strict*)
    apply (metis valid_bounded_parser_vs_valid_parser)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(rule parserS.derivation_take_preserves_derivation_initial)
   apply (metis)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply(erule impE)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(rule parserS.derivation_take_preserves_derivation_initial)
   apply (metis)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply(erule_tac
      x="e"
      in allE)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply(erule impE)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply (metis not_None_eq maximum_of_domain_derivation_take)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_rec1 (derivation_take d i) i \<le> Suc 0")
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_rec1 (derivation_take d i) i \<noteq> Suc 0")
    apply(rename_tac d c i e cb w r)(*strict*)
    apply(force)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(rule_tac
      t="parser_fixed_input_length_rec1 (derivation_take d i) i"
      and s="parser_fixed_input_length_recN (derivation_take d i) i"
      in ssubst)
    apply(rename_tac d c i e cb w r)(*strict*)
    apply (metis valid_bounded_parser_vs_valid_parser PARSER1_parser_fixed_input_length_recN_replacement parser_fixed_input_length_rec1_with_derivation_take parser_fixed_input_length_recN_with_derivation_take le_refl parserS.derivation_initial_belongs)
   apply(rename_tac d c i e cb w r)(*strict*)
   apply(force)
  apply(rename_tac d c i e cb w r)(*strict*)
  apply (metis valid_bounded_parser_vs_valid_parser parser_fixed_input_length_rec1_maximum parser_fixed_input_length_rec1_with_derivation_take less_or_eq_imp_le parserS.derivation_initial_belongs)
  done

lemma F_PARSER_RITU_preserves_marked_language: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> \<forall>r\<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> parser_no_access_final_with_read P
  \<Longrightarrow> can_detect_parser_bottom_only_in_Nonblockingness_configurations P
  \<Longrightarrow> parser_initial P \<notin> parser_marking P
  \<Longrightarrow> valid_bounded_parser (F_PARSER_RITU P) (Suc 0)
  \<Longrightarrow> parserS.is_forward_deterministic_accessible P
  \<Longrightarrow> parserS.marked_language P = parserS.marked_language (F_PARSER_RITU P)"
  apply(rule order_antisym)
   apply(rule F_PARSER_RITU_preserves_marked_language1)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_PARSER_RITU_preserves_marked_language2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_PARSER_RITU_preserves_Fdeterm: "
  parserS.is_forward_deterministic P
  \<Longrightarrow> parserS.is_forward_deterministic (F_PARSER_RITU P)"
  apply(simp add: parserS.is_forward_deterministic_def)
  apply(rule conjI)
   apply(simp add: parserS.is_forward_edge_deterministic_def parserS.is_forward_target_deterministic_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e)(*strict*)
   apply(simp add: F_PARSER_RITU_def parserS_step_relation_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(thin_tac "parserS.is_forward_target_deterministic P")
  apply(simp add: parserS.is_forward_edge_deterministic_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      x="c"
      in allE)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(clarsimp)
  apply(simp add: F_PARSER_RITU_def parserS_step_relation_def)
  done

lemma F_PARSER_RITU_preserves_FdetermR: "
  parserS.is_forward_deterministic_accessible P
  \<Longrightarrow> parserS.is_forward_deterministic_accessible (F_PARSER_RITU P)"
  apply(simp add: parserS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(simp add: parserS.is_forward_edge_deterministic_accessible_def parserS.is_forward_target_deterministic_accessible_def)
   apply(clarsimp)
   apply(rename_tac c c1 c2 e)(*strict*)
   apply(simp add: F_PARSER_RITU_def parserS_step_relation_def)
   apply(clarsimp)
  apply(clarsimp)
  apply(thin_tac "parserS.is_forward_target_deterministic_accessible P")
  apply(simp add: parserS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(erule_tac
      x="c1"
      in allE)
   apply(erule_tac
      x="c2"
      in allE)
   apply(erule_tac
      x="e1"
      in allE)
   apply(erule_tac
      x="e2"
      in allE)
   apply(clarsimp)
   apply(simp add: F_PARSER_RITU_def parserS_step_relation_def)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "c \<in> parserS.get_accessible_configurations P")
   apply(rename_tac c c1 c2 e1 e2)(*strict*)
   apply(force)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(thin_tac "c \<notin> parserS.get_accessible_configurations P")
  apply(simp add: parserS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule conjI)
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(rule F_PARSER_RITU_reflects_derivation_initial)
  apply(force)
  done

lemma F_PARSER_RITU_preserves_unmarked_languageuage1: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> valid_bounded_parser (F_PARSER_RITU P) (Suc 0)
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> parserS.unmarked_language P \<subseteq> parserS.unmarked_language (F_PARSER_RITU P)"
  apply(simp add: parserS.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d c c' i e v)(*strict*)
  apply(subgoal_tac "\<exists>d'. (parserS.derivation_initial P d' \<and> parserS.derivation P d' \<and> d' 0 = Some (pair None c) \<and> d' i = Some (pair e c') \<and> parser_fixed_input_length_recN d i = parser_fixed_input_length_recN d' i ) \<and> maximum_of_domain d' i ")
   apply(rename_tac d c c' i e v)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in derivation_extend_with_maximum_of_domain)
     apply(rename_tac d c c' i e v)(*strict*)
     apply(force)
    apply(rename_tac d c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c c' i e v)(*strict*)
    apply(rule parserS.derivation_take_preserves_derivation_initial)
    apply(force)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c c' i e v)(*strict*)
    apply(rule parserS.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c c' i e v)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(rule conjI)
    apply(rename_tac d c c' i e v)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(rule sym)
   apply(rule parser_fixed_input_length_recN_with_derivation_take)
   apply(force)
  apply(rename_tac d c c' i e v)(*strict*)
  apply(thin_tac "parserS.derivation_initial P d")
  apply(rename_tac d c c' i e v)(*strict*)
  apply(thin_tac "parserS.derivation P d")
  apply(thin_tac "d 0 = Some (pair None c)")
  apply(thin_tac "d i = Some (pair e c')")
  apply(clarsimp)
  apply(rename_tac d c c' i e v d')(*strict*)
  apply(thin_tac "parser_fixed_input_length_recN d i = parser_fixed_input_length_recN d' i")
  apply(clarsimp)
  apply(rename_tac c c' i e v d')(*strict*)
  apply(subgoal_tac "parserS.belongs P d'")
   apply(rename_tac c c' i e v d')(*strict*)
   prefer 2
   apply(rule parserS.derivation_initial_belongs)
    apply(rename_tac c c' i e v d')(*strict*)
    apply(simp add: valid_bounded_parser_def)
   apply(rename_tac c c' i e v d')(*strict*)
   apply(force)
  apply(rename_tac c c' i e v d')(*strict*)
  apply(rename_tac d)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c' = w @ [parser_bottom P]")
   apply(rename_tac c c' i e v d)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(force)
  apply(rename_tac c c' i e v d)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' i e v d w)(*strict*)
  apply(case_tac "parser_fixed_input_length_rec1 d i = Suc 0")
   apply(rename_tac c c' i e v d w)(*strict*)
   apply(case_tac "w")
    apply(rename_tac c c' i e v d w)(*strict*)
    apply(subgoal_tac "\<exists>k e c. d k = Some (pair e c) \<and> parserS_conf_scheduler c = [parser_bottom P] \<and> parser_fixed_input_length_rec1 d k = 0 \<and> parser_fixed_input_length_rec1 d (Suc k) = Suc 0")
     apply(rename_tac c c' i e v d w)(*strict*)
     prefer 2
     apply(rule_tac
      n="i"
      in PARSER1_latest_point_where_input_bottom_not_seen)
           apply(rename_tac c c' i e v d w)(*strict*)
           apply(force)
          apply(rename_tac c c' i e v d w)(*strict*)
          apply(force)
         apply(rename_tac c c' i e v d w)(*strict*)
         apply(force)
        apply(rename_tac c c' i e v d w)(*strict*)
        apply(force)
       apply(rename_tac c c' i e v d w)(*strict*)
       apply(simp add: parserS_marking_configurations_def)
      apply(rename_tac c c' i e v d w)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d w)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d w)(*strict*)
    apply(clarsimp)
    apply(rename_tac c c' i e v d k ea ca)(*strict*)
    apply(rule_tac
      x="derivation_take d k"
      in exI)
    apply(rule context_conjI)
     apply(rename_tac c c' i e v d k ea ca)(*strict*)
     apply(rule F_PARSER_RITU_preserves_derivation_initial)
           apply(rename_tac c c' i e v d k ea ca)(*strict*)
           apply(force)
          apply(rename_tac c c' i e v d k ea ca)(*strict*)
          apply(force)
         apply(rename_tac c c' i e v d k ea ca)(*strict*)
         apply(rule parserS.derivation_take_preserves_derivation_initial)
         apply(force)
        apply(rename_tac c c' i e v d k ea ca)(*strict*)
        apply(rule parserS.derivation_take_preserves_derivation)
        apply(force)
       apply(rename_tac c c' i e v d k ea ca)(*strict*)
       apply(rule maximum_of_domain_derivation_take)
       apply(force)
      apply(rename_tac c c' i e v d k ea ca)(*strict*)
      apply(simp add: derivation_take_def)
     apply(rename_tac c c' i e v d k ea ca)(*strict*)
     apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d k) k"
      and s="parser_fixed_input_length_recN d k"
      in ssubst)
      apply(rename_tac c c' i e v d k ea ca)(*strict*)
      apply(rule parser_fixed_input_length_recN_with_derivation_take)
      apply(force)
     apply(rename_tac c c' i e v d k ea ca)(*strict*)
     apply(rule_tac
      t="parser_fixed_input_length_recN d k"
      and s="parser_fixed_input_length_rec1 d k"
      in ssubst)
      apply(rename_tac c c' i e v d k ea ca)(*strict*)
      apply(rule PARSER1_parser_fixed_input_length_recN_replacement)
         apply(rename_tac c c' i e v d k ea ca)(*strict*)
         apply(force)
        apply(rename_tac c c' i e v d k ea ca)(*strict*)
        apply(force)
       apply(rename_tac c c' i e v d k ea ca)(*strict*)
       apply(force)
      apply(rename_tac c c' i e v d k ea ca)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d k ea ca)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d k ea ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac c c' i e v d k ea ca)(*strict*)
     apply(rule_tac
      x="c"
      in exI)
     apply(rule conjI)
      apply(rename_tac c c' i e v d k ea ca)(*strict*)
      apply(simp add: derivation_take_def)
     apply(rename_tac c c' i e v d k ea ca)(*strict*)
     apply(rule_tac
      x="ca"
      in exI)
     apply(rule_tac
      x="k"
      in exI)
     apply(clarsimp)
     apply(rule_tac
      x="ea"
      in exI)
     apply(simp add: derivation_take_def)
    apply(rename_tac c c' i e v d k ea ca)(*strict*)
    apply(simp add: parserS.derivation_initial_def)
   apply(rename_tac c c' i e v d w a list)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac c c' i e v d w a list)(*strict*)
    apply(rule F_PARSER_RITU_preserves_derivation_initial)
          apply(rename_tac c c' i e v d w a list)(*strict*)
          apply(force)
         apply(rename_tac c c' i e v d w a list)(*strict*)
         apply(force)
        apply(rename_tac c c' i e v d w a list)(*strict*)
        apply(force)
       apply(rename_tac c c' i e v d w a list)(*strict*)
       apply(force)
      apply(rename_tac c c' i e v d w a list)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d w a list)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d w a list)(*strict*)
    apply(rule_tac
      t="parser_fixed_input_length_recN d i"
      and s="parser_fixed_input_length_rec1 d i"
      in ssubst)
     apply(rename_tac c c' i e v d w a list)(*strict*)
     apply(rule PARSER1_parser_fixed_input_length_recN_replacement)
        apply(rename_tac c c' i e v d w a list)(*strict*)
        apply(force)
       apply(rename_tac c c' i e v d w a list)(*strict*)
       apply(force)
      apply(rename_tac c c' i e v d w a list)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d w a list)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d w a list)(*strict*)
    apply(force)
   apply(rename_tac c c' i e v d w a list)(*strict*)
   apply(rule conjI)
    apply(rename_tac c c' i e v d w a list)(*strict*)
    apply(rule_tac
      x="c"
      in exI)
    apply(rule conjI)
     apply(rename_tac c c' i e v d w a list)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d w a list)(*strict*)
    apply(rule_tac
      x="c'"
      in exI)
    apply(rule_tac
      x="i"
      in exI)
    apply(clarsimp)
   apply(rename_tac c c' i e v d w a list)(*strict*)
   apply(simp add: parserS.derivation_initial_def)
  apply(rename_tac c c' i e v d w)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_rec1 d i = 0")
   apply(rename_tac c c' i e v d w)(*strict*)
   prefer 2
   apply(subgoal_tac "parser_fixed_input_length_rec1 d i \<le> Suc 0")
    apply(rename_tac c c' i e v d w)(*strict*)
    prefer 2
    apply(rule parser_fixed_input_length_rec1_maximum)
      apply(rename_tac c c' i e v d w)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d w)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d w)(*strict*)
    apply(force)
   apply(rename_tac c c' i e v d w)(*strict*)
   apply(force)
  apply(rename_tac c c' i e v d w)(*strict*)
  apply(thin_tac "parser_fixed_input_length_rec1 d i \<noteq> Suc 0")
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac c c' i e v d w)(*strict*)
   apply(rule F_PARSER_RITU_preserves_derivation_initial)
         apply(rename_tac c c' i e v d w)(*strict*)
         apply(force)
        apply(rename_tac c c' i e v d w)(*strict*)
        apply(force)
       apply(rename_tac c c' i e v d w)(*strict*)
       apply(force)
      apply(rename_tac c c' i e v d w)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d w)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d w)(*strict*)
    apply(force)
   apply(rename_tac c c' i e v d w)(*strict*)
   apply(rule_tac
      t="parser_fixed_input_length_recN d i"
      and s="parser_fixed_input_length_rec1 d i"
      in ssubst)
    apply(rename_tac c c' i e v d w)(*strict*)
    apply(rule PARSER1_parser_fixed_input_length_recN_replacement)
       apply(rename_tac c c' i e v d w)(*strict*)
       apply(force)
      apply(rename_tac c c' i e v d w)(*strict*)
      apply(force)
     apply(rename_tac c c' i e v d w)(*strict*)
     apply(force)
    apply(rename_tac c c' i e v d w)(*strict*)
    apply(force)
   apply(rename_tac c c' i e v d w)(*strict*)
   apply(force)
  apply(rename_tac c c' i e v d w)(*strict*)
  apply(rule conjI)
   apply(rename_tac c c' i e v d w)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
  apply(rename_tac c c' i e v d w)(*strict*)
  apply(simp add: parserS.derivation_initial_def)
  done

lemma F_PARSER_RITU_preserves_unmarked_languageuage2: "
  parserS.unmarked_language P \<supseteq> parserS.unmarked_language (F_PARSER_RITU P)"
  apply(simp add: parserS.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac d c c' i e v)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(rule F_PARSER_RITU_reflects_derivation_initial)
   apply(force)
  apply(rename_tac d c c' i e v)(*strict*)
  apply(rule conjI)
   apply(rename_tac d c c' i e v)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
  apply(rename_tac d c c' i e v)(*strict*)
  apply(simp add: parserS.derivation_initial_def)
  done

lemma F_PARSER_RITU_preserves_unmarked_languageuage: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> valid_bounded_parser (F_PARSER_RITU P) (Suc 0)
  \<Longrightarrow> \<forall>r\<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> parserS.unmarked_language P = parserS.unmarked_language (F_PARSER_RITU P)"
  apply(rule order_antisym)
   apply(rule F_PARSER_RITU_preserves_unmarked_languageuage1)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_PARSER_RITU_preserves_unmarked_languageuage2)
  done

theorem F_LR_PARSER_nonblock1: "
  AF_LR_PARSER_input G F Do S' G' M P (Suc 0)
  \<Longrightarrow> cfg_LRk G (Suc 0)
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> P' = F_PARSER_RITU P
  \<Longrightarrow> parserS.Nonblockingness_linear_DB P'"
  apply(subgoal_tac "valid_bounded_parser P (Suc 0)")
   prefer 2
   apply(simp add: AF_LR_PARSER_is_PARSERl)
  apply(subgoal_tac "valid_bounded_parser (F_PARSER_RITU P) (Suc 0)")
   prefer 2
   apply(simp add: F_PARSER_RITU_valid_bounded_parser)
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
   apply(simp add: AF_LR_PARSER_input_def,force)
  apply(subgoal_tac "valid_dfa M")
   prefer 2
   apply(rule_tac
      G="G'"
      in Theorem6__27_a)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "some_step_from_every_configuration M")
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_Complete)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "\<forall>r\<in> parser_rules P. rule_rpop r \<noteq> []")
   prefer 2
   apply(rule FUNRLP_all_rules_pop)
      apply(force)+
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 2
      apply(simp add: AF_LR_PARSER_input_def)
      apply(force)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "parserS.is_forward_edge_deterministic_accessible P")
   prefer 2
   apply(rule F_LR_PARSER_is_forward_edge_deterministic_accessible)
     apply(force)+
  apply(subgoal_tac "valid_parser P'")
   prefer 2
   apply(rule_tac
      t="P'"
      and s="F_PARSER_RITU P"
      in ssubst)
    apply(force)
   apply(subgoal_tac "valid_bounded_parser (F_PARSER_RITU P) (Suc 0)")
    apply(simp add: valid_bounded_parser_def)
   apply(rule F_PARSER_RITU_valid_bounded_parser)
   apply(force)
  apply(clarsimp)
  apply(rule parser_Nonblockingness_linear_restricted_DB_to_Nonblockingness_linear_DB_with_not_parserS_entire_input_observed)
    apply(force)
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(rule_tac
      P="P"
      in F_PARSER_RITU_parserS_entire_input_observed_never)
      apply(rename_tac c)(*strict*)
      apply(force)+
  apply(rule parserS.AX_BF_LinDBRest_DetR_LaOp)
    apply(force)
   apply(rule F_PARSER_RITU_preserves_FdetermR)
   apply(rule parser_is_forward_edge_deterministic_accessible_implies_is_forward_deterministic_accessible)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(rule_tac
      t="parserS.unmarked_language (F_PARSER_RITU P)"
      and s="parserS.unmarked_language P"
      in ssubst)
   apply(rule sym)
   apply(rule F_PARSER_RITU_preserves_unmarked_languageuage)
     apply(force)+
  apply(subgoal_tac "parserS.is_forward_deterministic_accessible P")
   prefer 2
   apply(rule parser_is_forward_edge_deterministic_accessible_implies_is_forward_deterministic_accessible)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(subgoal_tac "parser_initial P \<notin> parser_marking P")
   prefer 2
   apply(rule F_LR_PARSER_initial_not_in_final)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="parserS.marked_language (F_PARSER_RITU P)"
      and s="parserS.marked_language P"
      in ssubst)
   apply(rule sym)
   apply(rule F_PARSER_RITU_preserves_marked_language)
         apply(force)+
       apply (metis F_LR_PARSER_shift_rules_do_not_reach_final_state)
      apply(rule F_LR_PARSER_enforces_can_detect_parser_bottom_only_in_Nonblockingness_configurations)
               apply(force)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_LR_PARSER_nonblockingness_language)
        apply(force)+
       apply(rule CFGRM_CFG_translate_Nonblockingness_id)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(force)+
  apply(simp add: valid_bounded_parser_def)
  done

definition F_PARSERRITU__SpecInput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_PARSERRITU__SpecInput G \<equiv>
  valid_bounded_parser G (Suc 0)
  \<and> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<and> parserFS.is_forward_edge_deterministic_accessible G
  \<and> (\<forall>r\<in> parser_rules G. rule_rpop r \<noteq> [])
  \<and> parser_no_access_final_with_read G
  \<and> can_detect_parser_bottom_only_in_Nonblockingness_configurations G
  \<and> parser_initial G \<notin> parser_marking G"

definition F_PARSERRITU__SpecOutput :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "F_PARSERRITU__SpecOutput Gi Go \<equiv>
  valid_bounded_parser Go (Suc 0)
  \<and> parserFS.is_forward_edge_deterministic_accessible Go
  \<and> parser_not_observes_input_terminator Go
  \<and> (\<forall>r\<in> parser_rules Go. rule_rpop r \<noteq> [])
  \<and> parserS.marked_language Gi = parserS.marked_language Go
  \<and> nonblockingness_language (parserS.unmarked_language Go) (parserS.marked_language Go)"

theorem F_PARSERRITU__SOUND: "
  F_PARSERRITU__SpecInput G
  \<Longrightarrow> F_PARSERRITU__SpecOutput G (F_PARSER_RITU G)"
  apply(simp add: F_PARSERRITU__SpecInput_def F_PARSERRITU__SpecOutput_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rule F_PARSER_RITU_valid_bounded_parser)
   apply(force)
  apply(rule context_conjI)
   apply(rule_tac
      ?G1.0="F_PARSER_RITU G"
      in parserS_vs_parserFS.preserve_FEdetermR1)
    apply(simp add: valid_bounded_parser_def)
   apply(subgoal_tac "parserS.is_forward_deterministic_accessible (F_PARSER_RITU G)")
    apply(simp add: parserS.is_forward_deterministic_accessible_def)
   apply(rule F_PARSER_RITU_preserves_FdetermR)
   apply(rule parser_is_forward_edge_deterministic_accessible_implies_is_forward_deterministic_accessible)
    apply(simp add: valid_bounded_parser_def)
   apply(rule_tac
      ?G2.0="G"
      in parserS_vs_parserFS.preserve_FEdetermR2)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(rule conjI)
   apply (metis F_PARSER_RITU_makes_parser_not_observes_input_terminator)
  apply(rule conjI)
   apply(rule F_PARSER_RITU_preserves_all_rules_pop)
   apply(force)
  apply(rule context_conjI)
   apply(rule F_PARSER_RITU_preserves_marked_language)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rule parser_is_forward_edge_deterministic_accessible_implies_is_forward_deterministic_accessible)
    apply(simp add: valid_bounded_parser_def)
   apply(rule_tac parserS_vs_parserFS.preserve_FEdetermR2)
    apply(simp add: valid_bounded_parser_def)
   apply(force)
  apply(rule_tac
      t="parserS.unmarked_language (F_PARSER_RITU G)"
      and s="parserS.unmarked_language G"
      in ssubst)
   prefer 2
   apply(rule_tac
      t="parserS.marked_language (F_PARSER_RITU G)"
      and s="parserS.marked_language G"
      in ssubst)
    prefer 2
    apply(force)
   apply(rule sym)
   apply(force)
  apply(rule sym)
  apply(rule F_PARSER_RITU_preserves_unmarked_languageuage)
    apply(force)
   apply(force)
  apply(force)
  done

end

