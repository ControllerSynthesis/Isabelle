section {*I\_kparser\_HFS\_HF*}
theory
  I_kparser_HFS_HF

imports
  I_kparser_HF
  I_kparser_HFS

begin

lemma rule_drop_in_parser_events_no_bottom: "
  valid_parser G
  \<Longrightarrow> set w \<subseteq> parser_events G - {parser_bottom G}
  \<Longrightarrow> (\<exists>x. x @ [parser_bottom G] = kPrefix k (w @ [parser_bottom G])) \<longrightarrow> (\<exists>x. x @ [parser_bottom G] = rule_rpush e)
  \<Longrightarrow> xa @ rule_rpush e = kPrefix k (w @ [parser_bottom G])
  \<Longrightarrow> set xa \<subseteq> parser_events G \<and> parser_bottom G \<notin> set xa"
  apply(rule conjI)
   apply(rule_tac
      B="set (xa@rule_rpush e)"
      in subset_trans)
    apply(rule set_append1)
   apply(rule_tac
      t="xa@rule_rpush e"
      and s="kPrefix k (w @ [parser_bottom G])"
      in ssubst)
    apply(force)
   apply(thin_tac "xa @ rule_rpush e = kPrefix k (w @ [parser_bottom G])")
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      A="set(take k w)"
      in set_mp)
     apply(rename_tac x)(*strict*)
     apply(rule_tac
      B="set w"
      in subset_trans)
      apply(rename_tac x)(*strict*)
      apply(rule set_take_subset)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x nat xa)(*strict*)
   apply(erule disjE)
    apply(rename_tac x nat xa)(*strict*)
    apply(force)
   apply(rename_tac x nat xa)(*strict*)
   apply(simp add: valid_parser_def)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<in> set w")
    apply(force)
   apply(rule_tac
      A="set(take k w)"
      in set_mp)
    apply(rule set_take_subset)
   apply(rule_tac
      t="take k w"
      and s="xa @ rule_rpush e"
      in ssubst)
    apply(force)
   apply(thin_tac "xa @ rule_rpush e = take k w")
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat x)(*strict*)
  apply(subgoal_tac "parser_bottom G \<in> set w")
   apply(rename_tac nat x)(*strict*)
   apply(force)
  apply(rename_tac nat x)(*strict*)
  apply(case_tac e)
  apply(rename_tac nat x rule_lpop rule_rpop rule_lpush rule_rpusha more)(*strict*)
  apply(clarsimp)
  done

definition parserHFvHFS_Lin2BraConf :: "
  ('stack, 'event) parserHFS_conf
  \<Rightarrow> ('stack, 'event) parserHF_conf"
  where
    "parserHFvHFS_Lin2BraConf c \<equiv>
  \<lparr>parserHF_conf_fixed = parserHFS_conf_fixed c,
  parserHF_conf_history = parserHFS_conf_history c,
  parserHF_conf_stack = parserHFS_conf_stack c\<rparr>"

definition parserHFvHFS_Bra2LinConf :: "
  ('stack, 'event) parserHF_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserHFS_conf"
  where
    "parserHFvHFS_Bra2LinConf c w \<equiv>
  \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
  parserHFS_conf_history = parserHF_conf_history c,
  parserHFS_conf_stack = parserHF_conf_stack c,
  parserHFS_conf_scheduler = w\<rparr>"

definition parserHFvHFS_Bra2LinStep :: "
  ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> 'event list"
  where
    "parserHFvHFS_Bra2LinStep c1 e c2 \<equiv>
  the (right_quotient_word (rule_rpop e) (rule_rpush e))"

lemma parserHFvHFS_inst_AX_Lin2BraConf_preserves_initiality: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>cl. cl \<in> parserHFS_initial_configurations G \<longrightarrow> parserHFvHFS_Lin2BraConf cl \<in> parserHF_initial_configurations G)"
  apply(simp add: parserHFvHFS_Lin2BraConf_def parserHF_initial_configurations_def parserHFS_initial_configurations_def parserHF_configurations_def parserHFS_configurations_def)
  apply(clarsimp)
  done

lemma parserHFvHFS_inst_AX_Bra2LinStep_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1B. c1B \<in> parserHF_configurations G \<longrightarrow> (\<forall>e c2B. parserHF_step_relation G c1B e c2B \<longrightarrow> parserHFvHFS_Bra2LinStep c1B e c2B \<in> parser_scheduler_fragments G)))"
  apply(clarsimp)
  apply(rename_tac G c1B e c2B)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinStep_def)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c1B e c2B)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(rename_tac G c1B e c2B)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G c1B e c2B k w xa)(*strict*)
  apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xa"
      in ssubst)
   apply(rename_tac G c1B e c2B k w xa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G c1B e c2B k w xa)(*strict*)
  apply(clarsimp)
  apply(simp add: parser_scheduler_fragments_def)
  apply(rule conjI)
   apply(rename_tac G c1B e c2B k w xa)(*strict*)
   apply(rule_tac
      B="set (xa @ rule_rpush e)"
      in subset_trans)
    apply(rename_tac G c1B e c2B k w xa)(*strict*)
    apply(rule set_append1)
   apply(rename_tac G c1B e c2B k w xa)(*strict*)
   apply(rule_tac
      t="xa@(rule_rpush e)"
      and s="kPrefix k (w@[parser_bottom G])"
      in ssubst)
    apply(rename_tac G c1B e c2B k w xa)(*strict*)
    apply(force)
   apply(rename_tac G c1B e c2B k w xa)(*strict*)
   apply(thin_tac "xa @ rule_rpush e = kPrefix k (w @ [parser_bottom G])")
   apply(clarsimp)
   apply(rename_tac G c1B e c2B k w x)(*strict*)
   apply(simp add: kPrefix_def)
   apply(erule disjE)
    apply(rename_tac G c1B e c2B k w x)(*strict*)
    apply(rule_tac
      A="set w"
      in set_mp)
     apply(rename_tac G c1B e c2B k w x)(*strict*)
     apply(force)
    apply(rename_tac G c1B e c2B k w x)(*strict*)
    apply(rule_tac
      A="set (take k w)"
      in set_mp)
     apply(rename_tac G c1B e c2B k w x)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac G c1B e c2B k w x)(*strict*)
    apply(force)
   apply(rename_tac G c1B e c2B k w x)(*strict*)
   apply(case_tac "k-length w")
    apply(rename_tac G c1B e c2B k w x)(*strict*)
    apply(force)
   apply(rename_tac G c1B e c2B k w x nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G c1B e c2B k w nat xa)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac G c1B e c2B k w xa)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac G c1B e c2B k w xa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<in> set w")
    apply(rename_tac G c1B e c2B k w xa)(*strict*)
    apply(force)
   apply(rename_tac G c1B e c2B k w xa)(*strict*)
   apply(rule_tac
      A="set (take k w)"
      in set_mp)
    apply(rename_tac G c1B e c2B k w xa)(*strict*)
    apply(rule set_take_subset)
   apply(rename_tac G c1B e c2B k w xa)(*strict*)
   apply(rule_tac
      t="take k w"
      and s="xa@(rule_rpush e)"
      in ssubst)
    apply(rename_tac G c1B e c2B k w xa)(*strict*)
    apply(force)
   apply(rename_tac G c1B e c2B k w xa)(*strict*)
   apply(thin_tac "xa @ rule_rpush e = take k w")
   apply(force)
  apply(rename_tac G c1B e c2B k w xa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c1B e c2B k w xa nat x)(*strict*)
  apply(case_tac e)
  apply(rename_tac G c1B e c2B k w xa nat x rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c1B c2B k xa nat x rule_lpop rule_lpush)(*strict*)
  apply(force)
  done

lemma parserHFvHFS_inst_AX_Bra2LinFin_closed : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>cB. (parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> parserHF_conf_fixed cB \<in> parser_schedulers G) \<and> (\<not> parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> parserHF_conf_fixed cB @ [parser_bottom G] \<in> parser_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cB)(*strict*)
   apply(simp add: suffix_def parserHF_configurations_def parser_schedulers_def)
   apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(simp add: suffix_def parserHF_configurations_def parser_schedulers_def)
  apply(clarsimp)
  done

lemma parserHFvHFS_inst_AX_Bra2LinConf_schedl_get : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>cB sL. parserHFvHFS_Bra2LinConf cB sL \<in> parserHFS_configurations G \<longrightarrow> sL \<in> parser_schedulers G \<longrightarrow> parserHFS_get_scheduler (parserHFvHFS_Bra2LinConf cB sL) = sL))"
  apply(clarsimp)
  apply(rename_tac G cB sL)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFS_get_scheduler_def parserHFS_configurations_def)
  done

lemma parserHFvHFS_inst_AX_Bra2LinFin_creates_proper_extension : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>cB. (parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> parserHFvHFS_Bra2LinConf cB (parserHF_conf_fixed cB) \<in> parserHFS_configurations G) \<and> (\<not> parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> parserHFvHFS_Bra2LinConf cB (parserHF_conf_fixed cB @ [parser_bottom G]) \<in> parserHFS_configurations G)))"
  apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cB)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_configurations_def parserHFvHFS_Bra2LinConf_def parserHFS_configurations_def suffix_def prefix_def)
   apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(simp add: parserHF_configurations_def parserHFvHFS_Bra2LinConf_def parserHFS_configurations_def suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G f l c)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma parserHFvHFS_inst_AX_Lin2BraConf_preserves_configurations : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>cl. cl \<in> parserHFS_configurations G \<longrightarrow> parserHFvHFS_Lin2BraConf cl \<in> parserHF_configurations G))"
  apply(clarsimp)
  apply(rename_tac G cl)(*strict*)
  apply(simp add: parserHFvHFS_Lin2BraConf_def parserHF_configurations_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G f h l w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G f h l w c)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G f h l w c)(*strict*)
   apply (metis rotate_simps set_append1 set_rotate1 set_take_head2 subset_trans)
  apply(rename_tac G f h l w c)(*strict*)
  apply (metis List.butlast_append butlast_snoc self_append_conv set_append_contra1)
  done

lemma parserHFvHFS_inst_AX_Bra2LinConf_preserves_initiality: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>sL. sL \<in> parser_schedulers G \<longrightarrow> (\<forall>cB. cB \<in> parserHF_initial_configurations G \<longrightarrow> parserHFvHFS_Bra2LinConf cB sL \<in> parserHFS_initial_configurations G))"
  apply(clarsimp)
  apply(rename_tac G sL cB)(*strict*)
  apply(simp add: parserHFS_initial_configurations_def)
  apply(simp add: parserHF_initial_configurations_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G sL cB)(*strict*)
   apply(simp add: parserHFvHFS_Bra2LinConf_def)
  apply(rename_tac G sL cB)(*strict*)
  apply(rule conjI)
   apply(rename_tac G sL cB)(*strict*)
   apply(simp add: parserHFvHFS_Bra2LinConf_def)
  apply(rename_tac G sL cB)(*strict*)
  apply(rule conjI)
   apply(rename_tac G sL cB)(*strict*)
   apply(simp add: parserHFvHFS_Bra2LinConf_def)
  apply(rename_tac G sL cB)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFS_configurations_def parserHF_configurations_def)
  apply(clarsimp)
  apply(rename_tac G sL)(*strict*)
  apply(simp add: parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G v)(*strict*)
  apply(simp add: valid_parser_def)
  apply(simp add: prefix_def)
  done

lemma parserHFvHFS_inst_AX_lin_step_relation_from_Bra2LinStep : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1B. c1B \<in> parserHF_configurations G \<longrightarrow> (\<forall>e c2B. parserHF_step_relation G c1B e c2B \<longrightarrow> (\<forall>sL. parserHFvHFS_Bra2LinConf c2B sL \<in> parserHFS_configurations G \<longrightarrow> parserHFS_step_relation G (parserHFvHFS_Bra2LinConf c1B (parserHFvHFS_Bra2LinStep c1B e c2B @ sL)) e (parserHFvHFS_Bra2LinConf c2B sL)))))"
  apply(clarsimp)
  apply(rename_tac G c1B e c2B sL)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c1B e c2B sL)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(rename_tac G c1B e c2B sL)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
  apply(subgoal_tac "c2B \<in> parserHF_configurations G")
   apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
   prefer 2
   apply(rule parserHF.AX_step_relation_preserves_belongsC)
     apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
     apply(force)
    apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
    apply(force)
   apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
   apply(force)
  apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinStep_def parserHF_configurations_def parserHFvHFS_Bra2LinConf_def parserHFS_configurations_def suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
  apply(simp add: parserHFS_step_relation_def parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
  apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xa"
      in ssubst)
   apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
  apply(clarsimp)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="take k w"
      and s="xa @ rule_rpush e"
      in ssubst)
    apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
   apply(rule_tac
      t="wa @ [parser_bottom G]"
      and s="rule_rpush e @ drop (min (length w) k) f @ c"
      in ssubst)
    apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
   apply(rule_tac
      x="drop (min (length w) k) f @ c"
      in exI)
   apply(simp (no_asm))
  apply(rename_tac G e k w xa f c ca wa cb x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "wa=xb")
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e k w xa f ca cb x nat xb)(*strict*)
   apply(rule triv_double_append)
    apply(rename_tac G e k w xa f ca cb x nat xb)(*strict*)
    apply(force)
   apply(rename_tac G e k w xa f ca cb x nat xb)(*strict*)
   apply(force)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(rule_tac
      v="[parser_bottom G]"
      in append_injr)
  apply(rule_tac
      t="xb@[parser_bottom G]"
      and s="rule_rpush e"
      in ssubst)
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   apply(force)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(rule_tac
      t="wa @ [parser_bottom G]"
      and s="rule_rpush e @ drop (Suc (min (length w) k)) f @ c"
      in ssubst)
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   apply(force)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(subgoal_tac "drop (Suc (min (length w) k)) f @ c = []")
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   apply(force)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(clarsimp)
  apply(rule propSym)
  apply(rule context_conjI)
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   apply(case_tac c)
    apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e k w xa f c ca wa cb x nat xb a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac G e k w xa f c ca wa cb x nat xb a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x nat xb a list)(*strict*)
   apply(thin_tac "c = a # list")
   apply(clarsimp)
   apply(rename_tac G e k w xa f ca cb x nat xb w')(*strict*)
   apply(case_tac e)
   apply(rename_tac G e k w xa f ca cb x nat xb w' rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(clarsimp)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e k w xa f ca wa cb x nat xb)(*strict*)
  apply(subgoal_tac "min (length w) k = length w")
   apply(rename_tac G e k w xa f ca wa cb x nat xb)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e k w xa f ca wa cb x nat xb)(*strict*)
  apply(clarsimp)
  apply(thin_tac "min (length w) k = length w")
  apply(subgoal_tac "Suc nat+length w = k")
   apply(rename_tac G e k w xa f ca wa cb x nat xb)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e k w xa f ca wa cb x nat xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e w xa f ca wa cb x xb)(*strict*)
  apply(erule disjE)
   apply(rename_tac G e w xa f ca wa cb x xb)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e w xa f ca wa cb x xb c)(*strict*)
   apply(rule length_shorter_append)
   apply(force)
  apply(rename_tac G e w xa f ca wa cb x xb)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G e w xa ca wa cb x xb c wb)(*strict*)
  apply(case_tac c)
   apply(rename_tac G e w xa ca wa cb x xb c wb)(*strict*)
   apply(force)
  apply(rename_tac G e w xa ca wa cb x xb c wb a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac G e w xa ca wa cb x xb c wb a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e w xa ca wa cb x xb c wb a list)(*strict*)
  apply(thin_tac "c = a # list")
  apply(clarsimp)
  done

lemma parserHFvHFS_inst_AX_Bra2LinConf_only_modifies_lin_unfixed_scheduler: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>cL sL. parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) sL \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_unfixed_scheduler cL (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) sL)) = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) sL)"
  apply(clarsimp)
  apply(rename_tac G cL sL)(*strict*)
  apply(simp add: parserHFS_set_unfixed_scheduler_def parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def parserHFS_get_unfixed_scheduler_def prefix_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G cL c w)(*strict*)
  apply(rule_tac
      t="left_quotient_word (parserHFS_conf_fixed cL) (w @ [parser_bottom G])"
      and s="Some c"
      in ssubst)
   apply(rename_tac G cL c w)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cL c w)(*strict*)
  apply(clarsimp)
  done

lemma parserHFvHFS_inst_AX_Bra2LinConf_schedl_get2: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>cB. cB \<in> parserHF_configurations G \<longrightarrow> (\<forall>s1L s2L. parserHFvHFS_Bra2LinConf cB s1L = parserHFvHFS_Bra2LinConf cB s2L \<longrightarrow> s1L = s2L)))"
  apply(clarsimp)
  apply(rename_tac G cB s1L s2L)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def)
  done

lemma parserHFvHFS_inst_AX_Bra2LinConf_inj: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>cB. cB \<in> parserHF_configurations G \<longrightarrow> (\<forall>s1L. s1L \<in> parser_schedulers G \<longrightarrow> s1L = parserHFS_get_scheduler (parserHFvHFS_Bra2LinConf cB s1L))))"
  apply(clarsimp)
  apply(rename_tac G cB s1L)(*strict*)
  apply(simp add: parserHFS_get_scheduler_def parserHFvHFS_Bra2LinConf_def)
  done

lemma parserHFvHFS_inst_AX_Bra2LinConf_on_empty_bra_sched_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>cB. cB \<in> parserHF_configurations G \<longrightarrow> parserHF_conf_fixed cB = [] \<longrightarrow> parserHFvHFS_Bra2LinConf cB [parser_bottom G] \<in> parserHFS_configurations G))"
  apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(simp add: parserHF_configurations_def parserHFvHFS_Bra2LinConf_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G h l)(*strict*)
  apply(simp add: prefix_def valid_parser_def)
  done

lemma parserHFvHFS_inst_AX_Bra2LinFin_on_empty_fixed_scheduler: "
  (\<forall>G. [] \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> valid_parser G)"
  apply(simp add: suffix_def)
  done

lemma parserHFvHFS_inst_AX_Bra2LinStep_translates_backwards_Bra2LinConf_closed : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1B. c1B \<in> parserHF_configurations G \<longrightarrow> (\<forall>e c2B. parserHF_step_relation G c1B e c2B \<longrightarrow> (\<forall>sL. parserHFvHFS_Bra2LinConf c2B sL \<in> parserHFS_configurations G \<longrightarrow> parserHFvHFS_Bra2LinConf c1B (parserHFvHFS_Bra2LinStep c1B e c2B @ sL) \<in> parserHFS_configurations G))))"
  apply(clarsimp)
  apply(rename_tac G c1B e c2B sL)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c1B e c2B sL)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(rename_tac G c1B e c2B sL)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
  apply(subgoal_tac "c2B \<in> parserHF_configurations G")
   apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
   prefer 2
   apply(rule parserHF.AX_step_relation_preserves_belongsC)
     apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
     apply(force)
    apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
    apply(force)
   apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
   apply(force)
  apply(rename_tac G c1B e c2B sL k w xa)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinStep_def parserHF_configurations_def parserHFvHFS_Bra2LinConf_def parserHFS_configurations_def suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
  apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xa"
      in ssubst)
   apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
  apply(clarsimp)
  apply(rule propSym)
  apply(rule conjI)
   apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
   apply(rule rule_drop_in_parser_events_no_bottom)
      apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
      apply(force)
     apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
    apply(force)
   apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
   apply(force)
  apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
  apply(rule_tac
      s="fa @ c"
      and t="wa @ [parser_bottom G]"
      in ssubst)
   apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
   apply(force)
  apply(rename_tac G e k w xa f fa l la c ca wa cb)(*strict*)
  apply(simp add: parserHF_step_relation_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
  apply(thin_tac "set (rule_lpop e) \<subseteq> parser_nonterms G")
  apply(thin_tac "set (rule_lpush e) \<subseteq> parser_nonterms G")
  apply(thin_tac "rule_lpop e \<noteq> []")
  apply(thin_tac "rule_lpush e \<noteq> []")
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take k w) \<longrightarrow> (\<exists>x. x @ [parser_bottom G] = rule_rpush e)")
   apply(subgoal_tac "min (length w) k=k")
    apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
   apply(clarsimp)
   apply(thin_tac "min (length w) k=k")
   apply(thin_tac "parser_bottom G \<in> set (rule_rpush e) \<longrightarrow> (\<exists>w. rule_rpush e @ drop k f = w @ [parser_bottom G] \<and> parser_bottom G \<notin> set w)")
   apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
   apply(thin_tac "set (drop k f) \<subseteq> parser_events G")
   apply(erule disjE)
    apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e k w xa c ca wa cb x cc)(*strict*)
    apply(rule_tac
      t="take k w"
      and s="xa@rule_rpush e"
      in ssubst)
     apply(rename_tac G e k w xa c ca wa cb x cc)(*strict*)
     apply(force)
    apply(rename_tac G e k w xa c ca wa cb x cc)(*strict*)
    apply(rule_tac
      t="wa@[parser_bottom G]"
      and s="rule_rpush e @ cc @ c"
      in ssubst)
     apply(rename_tac G e k w xa c ca wa cb x cc)(*strict*)
     apply(force)
    apply(rename_tac G e k w xa c ca wa cb x cc)(*strict*)
    apply(rule_tac
      x="c"
      in exI)
    apply(simp (no_asm))
   apply(rename_tac G e k w xa f c ca wa cb x)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e k w xa f c ca wa cb x cc)(*strict*)
   apply(case_tac "parser_bottom G \<in> set f")
    apply(rename_tac G e k w xa f c ca wa cb x cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e k w xa c ca wa cb x cc wb)(*strict*)
    apply(subgoal_tac "parser_bottom G \<in> set w")
     apply(rename_tac G e k w xa c ca wa cb x cc wb)(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac G e k w xa c ca wa cb x cc wb)(*strict*)
      apply(force)
     apply(rename_tac G e k w xa c ca wa cb x cc wb)(*strict*)
     apply(rule_tac
      x="parser_bottom G"
      and A="parser_events G"
      and w="w"
      in nset_diff)
      apply(rename_tac G e k w xa c ca wa cb x cc wb)(*strict*)
      apply(force)
     apply(rename_tac G e k w xa c ca wa cb x cc wb)(*strict*)
     apply(force)
    apply(rename_tac G e k w xa c ca wa cb x cc wb)(*strict*)
    apply(rule take_reflects_mem)
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x cc)(*strict*)
   apply(clarsimp)
   apply(thin_tac "parser_bottom G \<in> set (drop k f) \<longrightarrow> (\<exists>w. rule_rpush e @ drop k f = w @ [parser_bottom G] \<and> parser_bottom G \<notin> set w)")
   apply(rename_tac G e k w xa f c ca wa cb x cc)(*strict*)
   apply(case_tac c)
    apply(rename_tac G e k w xa f c ca wa cb x cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e k w xa f ca wa cb x cc)(*strict*)
    apply(case_tac "drop k f")
     apply(rename_tac G e k w xa f ca wa cb x cc)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac G e k w xa f ca wa cb x cc a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. drop k f = w' @ [x']")
     apply(rename_tac G e k w xa f ca wa cb x cc a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e k w xa f ca wa cb x cc a list)(*strict*)
    apply(thin_tac "drop k f = a # list")
    apply(clarsimp)
    apply(rename_tac G e k w xa f ca cb x cc w')(*strict*)
    apply(subgoal_tac "parser_bottom G \<in> set f")
     apply(rename_tac G e k w xa f ca cb x cc w')(*strict*)
     apply(force)
    apply(rename_tac G e k w xa f ca cb x cc w')(*strict*)
    apply(rule drop_reflects_mem)
    apply(rule sym)
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x cc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac G e k w xa f c ca wa cb x cc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x cc a list)(*strict*)
   apply(thin_tac "c = a # list")
   apply(clarsimp)
   apply(rename_tac G e k w xa f ca cb x cc w')(*strict*)
   apply(subgoal_tac "prefix f xa \<or> prefix xa f")
    apply(rename_tac G e k w xa f ca cb x cc w')(*strict*)
    prefer 2
    apply(rule_tac
      b="cc"
      and d="rule_rpush e"
      in mutual_prefix_prefix)
    apply(force)
   apply(rename_tac G e k w xa f ca cb x cc w')(*strict*)
   apply(erule disjE)
    apply(rename_tac G e k w xa f ca cb x cc w')(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac G e k w xa f ca cb x cc w')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e k w xa ca cb x cc w' c)(*strict*)
   apply(rule_tac
      x="cc @ drop k xa @ drop (k - length xa) c @ w' @ [parser_bottom G]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      w="xa"
      in append_linj)
   apply(rule_tac
      t="xa @ rule_rpush e"
      and s="take k w"
      in ssubst)
    apply(rename_tac G e k w xa ca cb x cc w' c)(*strict*)
    apply(force)
   apply(rename_tac G e k w xa ca cb x cc w' c)(*strict*)
   apply(force)
  apply(rename_tac G e k w xa f c ca wa cb x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(subgoal_tac "min (length w) k = length w")
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(clarsimp)
  apply(thin_tac "min (length w) k = length w")
  apply(subgoal_tac "xa@xb=w")
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   prefer 2
   apply(rule_tac
      v="[parser_bottom G]"
      in append_injr)
   apply(rule_tac
      t="w@[parser_bottom G]"
      and s="xa @ rule_rpush e"
      in ssubst)
    apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   apply(rule_tac
      t="rule_rpush e"
      and s="xb@[parser_bottom G]"
      in ssubst)
    apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
    apply(force)
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   apply(force)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(clarify)
  apply(subgoal_tac "k=Suc nat+length (xa@xb)")
   apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
   prefer 2
   apply(arith)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb)(*strict*)
  apply(clarify)
  apply(thin_tac "Suc nat + length (xa @ xb) - length (xa @ xb) = Suc nat")
  apply(case_tac e)
  apply(rename_tac G e k w xa f c ca wa cb x nat xb rule_lpop rule_rpopa rule_lpush rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac G xa f c ca wa cb x xb rule_lpop rule_lpush w)(*strict*)
  apply(rename_tac po pu w)
  apply(rename_tac G xa f c ca wa cb x xb po pu w)(*strict*)
  apply(case_tac "drop (Suc (length xa + length xb)) f")
   apply(rename_tac G xa f c ca wa cb x xb po pu w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G xa f c ca wa cb x po pu w)(*strict*)
   apply(subgoal_tac "w=wa")
    apply(rename_tac G xa f c ca wa cb x po pu w)(*strict*)
    apply(clarsimp)
   apply(rename_tac G xa f c ca wa cb x po pu w)(*strict*)
   apply(case_tac c)
    apply(rename_tac G xa f c ca wa cb x po pu w)(*strict*)
    apply(clarsimp)
   apply(rename_tac G xa f c ca wa cb x po pu w a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac G xa f c ca wa cb x po pu w a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G xa f c ca wa cb x po pu w a list)(*strict*)
   apply(thin_tac "c = a # list")
   apply(clarsimp)
  apply(rename_tac G xa f c ca wa cb x xb po pu w a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. drop (Suc (length xa + length xb)) f = w' @ [x']")
   apply(rename_tac G xa f c ca wa cb x xb po pu w a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G xa f c ca wa cb x xb po pu w a list)(*strict*)
  apply(thin_tac "drop (Suc (length xa + length xb)) f = a # list")
  apply(clarsimp)
  done

lemma parserHFvHFS_inst_AX_equal_by_fixed_unfixed_and_nonscheduler_part: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>cB. (parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> (\<forall>cL. cL \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB (parserHF_conf_fixed cB)) (parserHFS_get_unfixed_scheduler cL) = cL \<longrightarrow> cB = parserHFvHFS_Lin2BraConf cL)) \<and> (\<not> parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> (\<forall>cL. cL \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB (parserHF_conf_fixed cB @ [parser_bottom G])) (parserHFS_get_unfixed_scheduler cL) = cL \<longrightarrow> cB = parserHFvHFS_Lin2BraConf cL)))"
  apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cB)(*strict*)
   apply(clarsimp)
   apply(rename_tac G cB cL)(*strict*)
   apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFvHFS_Bra2LinConf_def parserHFS_set_unfixed_scheduler_def)
   apply(case_tac cB)
   apply(rename_tac G cB cL parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
   apply(case_tac cL)
   apply(rename_tac G cB cL parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
   apply(clarsimp)
  apply(rename_tac G cB)(*strict*)
  apply(clarsimp)
  apply(rename_tac G cB cL)(*strict*)
  apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFvHFS_Bra2LinConf_def parserHFS_set_unfixed_scheduler_def)
  apply(case_tac cB)
  apply(rename_tac G cB cL parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(case_tac cL)
  apply(rename_tac G cB cL parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinConf_preserves_history: "
  \<forall>G cB sL. valid_parser G \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> sL \<in> parser_schedulers G \<longrightarrow> parserHFvHFS_Bra2LinConf cB sL \<in> parserHFS_configurations G \<longrightarrow> parserHFS_conf_history (parserHFvHFS_Bra2LinConf cB sL) = parserHF_conf_history cB"
  apply(clarsimp)
  apply(rename_tac G cB sL)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def)
  done

lemma parserHFvHFS_inst_AX_Lin2BraConf_preserves_steps: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>c1l. c1l \<in> parserHFS_configurations G \<longrightarrow> (\<forall>e c2l. parserHFS_step_relation G c1l e c2l \<longrightarrow> parserHF_step_relation G (parserHFvHFS_Lin2BraConf c1l) e (parserHFvHFS_Lin2BraConf c2l)))"
  apply(clarsimp)
  apply(rename_tac G c1l e c2l)(*strict*)
  apply(simp add: parserHFS_step_relation_def parserHF_step_relation_def parserHFvHFS_Lin2BraConf_def)
  apply(clarsimp)
  apply(rename_tac G c1l e c2l x xa y)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G e c2l x xa y f h w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G e c2l x xa y f h w c)(*strict*)
  apply(subgoal_tac "prefix f (rule_rpop e) \<or> prefix (rule_rpop e) f")
   apply(rename_tac G e c2l x xa y f h w c)(*strict*)
   apply(erule disjE)
    apply(rename_tac G e c2l x xa y f h w c)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac G e c2l x xa y f h w c)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac G e c2l x xa y f h w c)(*strict*)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraConf_preserves_history: "
  \<forall>G cL. valid_parser G \<longrightarrow> cL \<in> parserHFS_configurations G \<longrightarrow> parserHFS_conf_history cL = parserHF_conf_history (parserHFvHFS_Lin2BraConf cL)"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(simp add: parserHFvHFS_Lin2BraConf_def)
  done

lemma parserHF_vs_parserHFS_inst_ATS_Branching_Versus_Linear1_axioms: "
  ATS_Branching_Versus_Linear1_axioms valid_parser
     parserHFS_configurations parserHFS_initial_configurations
     parserHFS_step_relation parser_scheduler_fragments parser_schedulers
     parserHFS_get_scheduler (@) parserHFS_get_unfixed_scheduler
     parserHFS_set_unfixed_scheduler parserHFS_conf_history
     parserHF_configurations parserHF_initial_configurations
     parserHF_step_relation parserHF_conf_fixed parserHF_conf_history
     parserHFvHFS_Lin2BraConf parserHFvHFS_Bra2LinConf
     parserHFvHFS_Bra2LinStep
     (\<lambda>G w. if w \<sqsupseteq> [parser_bottom G] then w else w @ [parser_bottom G])"
  apply(simp add: ATS_Branching_Versus_Linear1_axioms_def)
  apply(simp add: parserHFvHFS_inst_AX_Bra2LinConf_preserves_initiality parserHFvHFS_inst_AX_Bra2LinStep_closed parserHFvHFS_inst_AX_Bra2LinFin_closed parserHFvHFS_inst_AX_Bra2LinConf_schedl_get parserHFvHFS_inst_AX_Bra2LinConf_schedl_get2 parserHFvHFS_inst_AX_Bra2LinFin_creates_proper_extension parserHFvHFS_inst_AX_Bra2LinStep_translates_backwards_Bra2LinConf_closed parserHFvHFS_inst_AX_lin_step_relation_from_Bra2LinStep parserHFvHFS_inst_AX_Bra2LinConf_only_modifies_lin_unfixed_scheduler parserHFvHFS_inst_AX_Bra2LinConf_inj parserHFvHFS_inst_AX_Bra2LinConf_on_empty_bra_sched_closed parserHFvHFS_inst_AX_Bra2LinFin_on_empty_fixed_scheduler parserHFvHFS_inst_AX_equal_by_fixed_unfixed_and_nonscheduler_part parserHF_vs_parserHFS_inst_AX_Bra2LinConf_preserves_history)
  apply(simp add:  parserHFvHFS_inst_AX_Lin2BraConf_preserves_configurations parserHFvHFS_inst_AX_Lin2BraConf_preserves_initiality
      )
  apply(rule conjI)
   apply(rule parserHFvHFS_inst_AX_Lin2BraConf_preserves_steps)
  apply(simp add: parserHF_vs_parserHFS_inst_AX_Lin2BraConf_preserves_history)
  done

interpretation "parserHF_vs_parserHFS" : ATS_Branching_Versus_Linear1
  (* TSstructure *)
  "valid_parser"
  (* lin_configurations *)
  "parserHFS_configurations"
  (* lin_initial_configurations *)
  "parserHFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* lin_step_relation *)
  "parserHFS_step_relation"
  (* effects *)
  "parser_markers"
  (* lin_marking_condition *)
  "parserHFS_marking_condition"
  (* lin_marked_effect *)
  "parserHFS_marked_effect"
  (* lin_unmarked_effect *)
  "parserHFS_unmarked_effect"
  (* lin_fixed_schedulers *)
  "parser_fixed_schedulers"
  (* lin_empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* lin_fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* lin_scheduler_fragments *)
  "parser_scheduler_fragments"
  (* lin_empty_scheduler_fragment *)
  "parser_empty_scheduler_fragment"
  (* lin_join_scheduler_fragments *)
  "append"
  (* lin_unfixed_schedulers *)
  "parser_unfixed_schedulers"
  (* lin_empty_unfixed_scheduler *)
  "parser_empty_unfixed_scheduler"
  (* lin_unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* lin_extend_unfixed_scheduler *)
  "append"
  (* lin_unfixed_scheduler_extendable *)
  "parser_unfixed_scheduler_extendable"
  (* lin_schedulers *)
  "parser_schedulers"
  (* lin_initial_schedulers *)
  "parser_schedulers"
  (* lin_empty_scheduler *)
  "parser_empty_scheduler"
  (* lin_get_scheduler *)
  "parserHFS_get_scheduler"
  (* lin_join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* lin_extend_scheduler *)
  "append"
  (* lin_get_unfixed_scheduler *)
  "parserHFS_get_unfixed_scheduler"
  (* lin_set_unfixed_scheduler *)
  "parserHFS_set_unfixed_scheduler"
  (* lin_get_fixed_scheduler *)
  "parserHFS_conf_fixed"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* lin_set_history *)
  "parserHFS_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* lin_get_history *)
  "parserHFS_conf_history"
  (* bra_configurations *)
  "parserHF_configurations"
  (* bra_initial_configurations *)
  "parserHF_initial_configurations"
  (* bra_step_relation *)
  "parserHF_step_relation"
  (* bra_marking_condition *)
  "parserHF_marking_condition"
  (* bra_marked_effect *)
  "parserHF_marked_effect"
  (* bra_unmarked_effect *)
  "parserHF_unmarked_effect"
  (* bra_fixed_schedulers *)
  "parser_fixed_schedulers"
  (* bra_empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* bra_fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* bra_get_fixed_scheduler *)
  "parserHF_conf_fixed"
  (* bra_set_history *)
  "parserHF_set_history"
  (* bra_get_history *)
  "parserHF_conf_history"
  (* Lin2BraConf *)
  "parserHFvHFS_Lin2BraConf"
  (* Bra2LinConf *)
  "parserHFvHFS_Bra2LinConf"
  (* Bra2LinStep *)
  "parserHFvHFS_Bra2LinStep"
  (* Bra2LinFin *)
  "\<lambda>G w. if (suffix w [parser_bottom G]) then w else w@[parser_bottom G]"
  apply(simp add: LOCALE_DEFS parserHF_interpretations parserHFS_interpretations0)

  apply(simp add: parserHF_vs_parserHFS_inst_ATS_Branching_Versus_Linear1_axioms)
  done

lemma parserHF_steps_are_empty1: "
  valid_parser G
  \<Longrightarrow> parserHF.derivation G d
  \<Longrightarrow> parserHF.belongs G d
  \<Longrightarrow> \<forall>j e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> parserHF_conf_history c = parserHF_conf_history c'
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> parserHF_conf_fixed c = [] \<or> parserHF_conf_fixed c = [parser_bottom G]
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> d n = Some (pair e' c')
  \<Longrightarrow> parserHF_conf_fixed c' = [] \<or> parserHF_conf_fixed c' = [parser_bottom G]"
  apply(induct "n-i" arbitrary: n i e c e' c')
   apply(rename_tac n i e c e' c')(*strict*)
   apply(clarsimp)
  apply(rename_tac x n i e c e' c')(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac x n i e c e' c')(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in parserHF.pre_some_position_is_some_position_prime)
      apply(rename_tac x n i e c e' c')(*strict*)
      apply(force)
     apply(rename_tac x n i e c e' c')(*strict*)
     apply(force)
    apply(rename_tac x n i e c e' c')(*strict*)
    apply(force)
   apply(rename_tac x n i e c e' c')(*strict*)
   apply(force)
  apply(rename_tac x n i e c e' c')(*strict*)
  apply(clarsimp)
  apply(rename_tac x n i e c e' c' ea ca)(*strict*)
  apply(erule_tac
      x="Some ea"
      in meta_allE)
  apply(erule_tac
      x="ca"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e'"
      in meta_allE)
  apply(erule_tac
      x="c'"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x n i e c e' c' ea ca)(*strict*)
   apply(force)
  apply(rename_tac x n i e c e' c' ea ca)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x n i e c e' c' ea ca)(*strict*)
   apply(subgoal_tac "parserHF_conf_history ca = parserHF_conf_history c")
    apply(rename_tac x n i e c e' c' ea ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n i e c e' c' ea ca j e'a c'a)(*strict*)
    apply(erule_tac
      x="j"
      in allE)
    apply(force)
   apply(rename_tac x n i e c e' c' ea ca)(*strict*)
   apply(force)
  apply(rename_tac x n i e c e' c' ea ca)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x n i e c e' c' ea ca)(*strict*)
   defer
   apply(force)
  apply(rename_tac x n i e c e' c' ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n i e c e' c' ea ca)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserHF_step_relation G c1 e2 c2")
   apply(rename_tac x n i e c e' c' ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserHF.step_detail_before_some_position)
     apply(rename_tac x n i e c e' c' ea ca)(*strict*)
     apply(force)
    apply(rename_tac x n i e c e' c' ea ca)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e' c' ea ca)(*strict*)
   apply(force)
  apply(rename_tac x n i e c e' c' ea ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label G ea")
   apply(rename_tac x n i e c e' c' ea ca)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(rename_tac x n i e c e' c' ea ca)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(clarsimp)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x n i e c e' c' ea ca k w xb)(*strict*)
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
  apply(erule_tac
      P="parserHF_conf_fixed c = []"
      in disjE)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
   apply(clarsimp)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
     apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
     apply(clarsimp)
     apply(case_tac w)
      apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(rule_tac
      B="set w"
      in nset_mp)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa nat xc)(*strict*)
   apply(subgoal_tac "w=[]")
    apply(rename_tac x n i e c e' c' ea ca k w xb xa nat xc)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n i e c e' c' ea ca xb xa xc)(*strict*)
    apply (metis drop_append Suc_length append_Nil2 drop_Nil drop_Suc_Cons drop_length_append eq_Nil_appendI le_SucE length_shorter_append2)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa nat xc)(*strict*)
   apply (metis butlast_if_match_direct)
  apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
   apply(simp add: kPrefix_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
   apply(case_tac "k-length w")
    apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
    apply(clarsimp)
    apply(case_tac cb)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa xc)(*strict*)
     apply(subgoal_tac "parser_bottom G \<in> set w")
      apply(rename_tac x n i e c e' c' ea ca k w xb xa xc)(*strict*)
      apply(force)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa xc)(*strict*)
     apply(rule_tac
      A="set (take k w)"
      in set_mp)
      apply(rename_tac x n i e c e' c' ea ca k w xb xa xc)(*strict*)
      apply(rule set_take_subset)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa xc)(*strict*)
     apply(force)
    apply(rename_tac x n i e c e' c' ea ca k w xb xa cb a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n i e c e' c' ea ca k w xb xa a list)(*strict*)
    apply(case_tac list)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
     apply(subgoal_tac "min (length w) k = 0")
      apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
     apply(clarsimp)
     apply(case_tac w)
      apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa a list)(*strict*)
     apply(subgoal_tac "k=0")
      apply(rename_tac x n i e c e' c' ea ca k w xb xa a list)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x n i e c e' c' ea ca k w xb xa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x n i e c e' c' ea ca k w xb xa a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat xc)(*strict*)
   apply(case_tac cb)
    apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat xc)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n i e c e' c' ea ca xb xa xc)(*strict*)
    apply (metis valid_parser_rules_rhs_gets_shorter length_shorter_append2 self_append_conv2)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat xc a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x n i e c e' c' ea ca k w xb xa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<in> set w")
    apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
   apply(rule_tac
      A="set (take k w)"
      in set_mp)
    apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
    apply(rule set_take_subset)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
   apply(rule_tac
      t="take k w"
      and s="parser_bottom G # cb"
      in ssubst)
    apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat xc)(*strict*)
  apply(case_tac cb)
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat xc)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n i e c e' c' ea ca xb xa xc)(*strict*)
   apply (metis valid_parser_rules_rhs_gets_shorter diff_0_eq_0 diff_Suc_Suc diff_is_0_eq le_antisym length_0_conv length_append_singleton self_append_conv2)
  apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat xc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
   apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat xc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x n i e c e' c' ea ca k w xb xa cb nat xc a list)(*strict*)
  apply(thin_tac "cb=a#list")
  apply(clarsimp)
  done

lemma parserHF_steps_are_empty2: "
  valid_parser G
  \<Longrightarrow> parserHF.derivation G d
  \<Longrightarrow> parserHF.belongs G d
  \<Longrightarrow> \<forall>j e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> parserHF_conf_history c = parserHF_conf_history c'
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> parserHF_conf_fixed c = [] \<or> parserHF_conf_fixed c = [parser_bottom G]
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> d n = Some (pair e1 c1)
  \<Longrightarrow> d (Suc n) = Some (pair (Some e2) c2)
  \<Longrightarrow> d (Suc n + m) = Some (pair e' c')
  \<Longrightarrow> parserHF_step_relation G c1 e2 c2
  \<Longrightarrow> the (right_quotient_word (rule_rpop e2) (rule_rpush e2)) = []"
  apply(induct "n-i" arbitrary: n i e c e1 c1 e2 c2)
   apply(rename_tac n i e c e1 c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 c1 e2 c2)(*strict*)
   apply(subgoal_tac "e2 \<in> parser_step_labels G \<and> c2 \<in> parserHF_configurations G")
    apply(rename_tac i e1 c1 e2 c2)(*strict*)
    prefer 2
    apply(rule parserHF.AX_step_relation_preserves_belongs)
      apply(rename_tac i e1 c1 e2 c2)(*strict*)
      apply(force)
     apply(rename_tac i e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac i e1 c1 e2 c2)(*strict*)
    apply(rule parserHF.belongs_configurations)
     apply(rename_tac i e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac i e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac i e1 c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(rename_tac i e1 c1 e2 c2)(*strict*)
    prefer 2
    apply(simp add: valid_parser_def parserHF_step_relation_def)
   apply(rename_tac i e1 c1 e2 c2)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac i e1 c1 e2 c2 k w xa)(*strict*)
   apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e2)"
      and s="Some xa"
      in ssubst)
    apply(rename_tac i e1 c1 e2 c2 k w xa)(*strict*)
    apply(rule right_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac i e1 c1 e2 c2 k w xa)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
   apply(erule_tac
      P="parserHF_conf_fixed c1 = []"
      in disjE)
    apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="Suc i"
      in allE)
    apply(clarsimp)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "take k w=[]")
      apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
      apply(clarsimp)
     apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
     apply(rule_tac
      t="take k w"
      and s="butlast_if_match (take k w) (parser_bottom G)"
      in subst)
      apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
      apply(rule butlast_if_match_direct2_prime)
      apply(rule_tac
      B="set w"
      in nset_mp)
       apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
       apply(rule set_take_subset)
      apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
      apply(force)
     apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
     apply(force)
    apply(rename_tac i e1 c1 e2 c2 k w xa x nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb)(*strict*)
    apply(subgoal_tac "w=[]")
     apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb)(*strict*)
     apply(clarsimp)
     apply(rename_tac i e1 c1 e2 c2 xa x xb)(*strict*)
     apply (metis drop_append Suc_length append_Nil2 drop_Nil drop_Suc_Cons drop_length_append eq_Nil_appendI le_SucE length_shorter_append2)
    apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb)(*strict*)
    apply (metis butlast_if_match_direct)
   apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="Suc i"
      in allE)
   apply(clarsimp)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
     apply(case_tac c)
      apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
      apply(clarsimp)
      apply(rename_tac i e1 c1 e2 c2 k w xa x xb)(*strict*)
      apply(subgoal_tac "parser_bottom G \<in> set w")
       apply(rename_tac i e1 c1 e2 c2 k w xa x xb)(*strict*)
       apply(force)
      apply(rename_tac i e1 c1 e2 c2 k w xa x xb)(*strict*)
      apply(rule_tac
      A="set (take k w)"
      in set_mp)
       apply(rename_tac i e1 c1 e2 c2 k w xa x xb)(*strict*)
       apply(rule set_take_subset)
      apply(rename_tac i e1 c1 e2 c2 k w xa x xb)(*strict*)
      apply(force)
     apply(rename_tac i e1 c1 e2 c2 k w xa x c a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
      apply(rename_tac i e1 c1 e2 c2 k w xa x c a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac i e1 c1 e2 c2 k w xa x c a list)(*strict*)
     apply(thin_tac "c=a#list")
     apply(clarsimp)
     apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
     apply(subgoal_tac "min (length w) k = 0")
      apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
      apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
      prefer 2
      apply(rule butlast_if_match_direct2_prime)
      apply(rule_tac
      B="set w"
      in nset_mp)
       apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
       apply(rule set_take_subset)
      apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
      apply(force)
     apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
     apply(clarsimp)
     apply(erule disjE)
      apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
      apply(clarsimp)
     apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
     apply(clarsimp)
    apply(rename_tac i e1 c1 e2 c2 k w xa x)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
    apply(subgoal_tac "parser_bottom G \<in> set w")
     apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
     apply(force)
    apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
    apply(rule_tac
      A="set (take k w)"
      in set_mp)
     apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
    apply(rule_tac
      t="take k w"
      and s="parser_bottom G # c"
      in ssubst)
     apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
     apply(force)
    apply(rename_tac i e1 c1 e2 c2 k w xa x c)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac i e1 c1 e2 c2 k w xa x nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb)(*strict*)
   apply(erule disjE)
    apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb c)(*strict*)
    apply(case_tac c)
     apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb c)(*strict*)
     apply(clarsimp)
     apply(rename_tac i e1 c1 e2 c2 xa x xb)(*strict*)
     apply (metis Suc_le_mono add_Suc_shift append_is_Nil_conv drop_length_append le_Suc_eq le_refl list.size(3) list.size(4) add.commute plus_nat.add_0 takePrecise take_0 take_all take_max_no_append)
    apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb c a list)(*strict*)
    apply(force)
   apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb c)(*strict*)
   apply(case_tac c)
    apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb c)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e1 c1 e2 c2 xa x xb)(*strict*)
    apply (metis add_Suc_right append_self_conv2 drop_length_append le_0_eq length_shorter_append2 list.size(3) list.size(4) add.commute not_less_eq_eq plus_nat.add_0)
   apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb c a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb c a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac i e1 c1 e2 c2 k w xa x nat xb c a list)(*strict*)
   apply(thin_tac "c=a#list")
   apply(clarsimp)
  apply(rename_tac x n i e c e1 c1 e2 c2)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
   apply(rename_tac x n i e c e1 c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
   apply(erule_tac
      x="Some ea"
      in meta_allE)
   apply(erule_tac
      x="ca"
      in meta_allE)
   apply(erule_tac
      x="e1"
      in meta_allE)
   apply(erule_tac
      x="c1"
      in meta_allE)
   apply(erule_tac
      x="e2"
      in meta_allE)
   apply(erule_tac
      x="c2"
      in meta_allE)
   apply(clarsimp)
   apply(erule meta_impE)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
    apply(subgoal_tac "parserHF_conf_history ca = parserHF_conf_history c")
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
     prefer 2
     apply(erule_tac
      x="Suc i"
      in allE)
     apply(clarsimp)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca j e'a c'a)(*strict*)
    apply(erule_tac
      x="j"
      in allE)
    apply(force)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
   apply(erule meta_impE)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
    defer
    apply(erule meta_impE)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
     apply(force)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e1 c1 e2 c2)(*strict*)
   apply(rule_tac
      m="Suc n"
      in parserHF.pre_some_position_is_some_position_prime)
      apply(rename_tac x n i e c e1 c1 e2 c2)(*strict*)
      apply(force)
     apply(rename_tac x n i e c e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac x n i e c e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserHF_step_relation G c1 e2 c2")
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserHF.step_detail_before_some_position)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
     apply(force)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
   apply(force)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label G ea")
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(clarsimp)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb)(*strict*)
  apply(thin_tac "parserHF_step_relation G c1 e2 c2")
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
  apply(erule_tac
      P="parserHF_conf_fixed c = []"
      in disjE)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
   apply(clarsimp)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
     apply(clarsimp)
     apply(case_tac w)
      apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(rule_tac
      B="set w"
      in nset_mp)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa nat xc)(*strict*)
   apply(subgoal_tac "w=[]")
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa nat xc)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca xb xa xc)(*strict*)
    apply (metis drop_append Suc_length append_Nil2 drop_Nil drop_Suc_Cons drop_length_append eq_Nil_appendI le_SucE length_shorter_append2)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa nat xc)(*strict*)
   apply (metis butlast_if_match_direct)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
   apply(simp add: kPrefix_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
   apply(case_tac "k-length w")
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
    apply(clarsimp)
    apply(case_tac cb)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa xc)(*strict*)
     apply(subgoal_tac "parser_bottom G \<in> set w")
      apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa xc)(*strict*)
      apply(force)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa xc)(*strict*)
     apply(rule_tac
      A="set (take k w)"
      in set_mp)
      apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa xc)(*strict*)
      apply(rule set_take_subset)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa xc)(*strict*)
     apply(force)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa a list)(*strict*)
    apply(case_tac list)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
     apply(subgoal_tac "min (length w) k = 0")
      apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
     apply(clarsimp)
     apply(case_tac w)
      apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
      apply(clarsimp)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa a list)(*strict*)
     apply(subgoal_tac "k=0")
      apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa a list)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat xc)(*strict*)
   apply(case_tac cb)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat xc)(*strict*)
    apply(clarsimp)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca xb xa xc)(*strict*)
    apply (metis valid_parser_rules_rhs_gets_shorter diff_0_eq_0 diff_Suc_Suc diff_is_0_eq le_antisym length_0_conv length_append_singleton self_append_conv2)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat xc a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<in> set w")
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
   apply(rule_tac
      A="set (take k w)"
      in set_mp)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
    apply(rule set_take_subset)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
   apply(rule_tac
      t="take k w"
      and s="parser_bottom G # cb"
      in ssubst)
    apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
    apply(force)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat xc)(*strict*)
  apply(case_tac cb)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat xc)(*strict*)
   apply(clarsimp)
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca xb xa xc)(*strict*)
   apply (metis valid_parser_rules_rhs_gets_shorter diff_0_eq_0 diff_Suc_Suc diff_is_0_eq le_antisym length_0_conv length_append_singleton self_append_conv2)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat xc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
   apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat xc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x n i e c e1 c1 e2 c2 ea ca k w xb xa cb nat xc a list)(*strict*)
  apply(thin_tac "cb=a#list")
  apply(clarsimp)
  done

lemma parserHFS_rhs_and_history_invariant_if_input_consumed: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G d
  \<Longrightarrow> maximum_of_domain d x
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> i \<le> j
  \<Longrightarrow> parserHFS_conf_scheduler c = [parser_bottom G]
  \<Longrightarrow> d j = Some (pair e' c')
  \<Longrightarrow>
  parserHFS_conf_scheduler c = parserHFS_conf_scheduler c'
  \<and> parserHFS_conf_history c = parserHFS_conf_history c'"
  apply(induct "j-i" arbitrary: j i e c e' c')
   apply(rename_tac j i e c e' c')(*strict*)
   apply(clarsimp)
  apply(rename_tac xa j i e c e' c')(*strict*)
  apply(erule_tac
      x="j"
      in meta_allE)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac xa j i e c e' c')(*strict*)
   prefer 2
   apply(rule_tac
      m="j"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac xa j i e c e' c')(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac xa j i e c e' c')(*strict*)
    apply(force)
   apply(rename_tac xa j i e c e' c')(*strict*)
   apply(force)
  apply(rename_tac xa j i e c e' c')(*strict*)
  apply(clarify)
  apply(rename_tac xa j i e c e' c' e1 e2 c1 c2)(*strict*)
  apply(erule_tac
      x="Some e2"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(erule_tac
      x="e'"
      in meta_allE)
  apply(erule_tac
      x="c'"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
  apply(subgoal_tac "c2 \<in> parserHFS_configurations G")
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   prefer 2
   apply(rule parserHFS.belongs_configurations)
    apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
    apply(rule parserHFS.derivation_initial_belongs)
     apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
     apply(force)
    apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
    apply(force)
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
  apply(subgoal_tac "parserHFS_conf_scheduler c2 = [parser_bottom G]")
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
    prefer 2
    apply(simp add: parserHFS_step_relation_def valid_parser_def)
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   apply(subgoal_tac "\<exists>w. parserHFS_conf_scheduler c2 = w@[parser_bottom G]")
    apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
    prefer 2
    apply(simp add: parserHFS_configurations_def)
    apply(clarsimp)
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa j i e c e' c' e2 c2 w)(*strict*)
   apply(subgoal_tac "\<exists>x. rule_rpop e2 = x@(rule_rpush e2)")
    apply(rename_tac xa j i e c e' c' e2 c2 w)(*strict*)
    prefer 2
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac xa j i e c e' c' e2 c2 w k wa xb)(*strict*)
    apply(rule_tac
      x="xb"
      in exI)
    apply(force)
   apply(rename_tac xa j i e c e' c' e2 c2 w)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa j i e c e' c' e2 c2 w xb)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarify)
   apply(rename_tac xa j i e c e' c' e2 c2 w xb xba xc)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parserHFS_conf_history c = parserHFS_conf_history c2")
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   apply(force)
  apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
  apply(thin_tac "parserHFS_conf_history c2 = parserHFS_conf_history c'")
  apply(subgoal_tac "[parser_bottom G] = parserHFS_conf_scheduler c")
   apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa j i e c e' c' e2 c2)(*strict*)
  apply(thin_tac "[parser_bottom G] = parserHFS_conf_scheduler c'")
  apply(thin_tac "parserHFS_conf_scheduler c = parserHFS_conf_scheduler c'")
  apply(thin_tac "i \<le> j")
  apply(thin_tac "d j = Some (pair e' c')")
  apply(clarsimp)
  apply(rename_tac xa j i e c c' e2 c2)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa j i e c c' e2 c2 xb xba y)(*strict*)
  apply(rule_tac
      t="butlast_if_match (rule_rpop e2) (parser_bottom G)"
      and s="[]"
      in ssubst)
   apply(rename_tac xa j i e c c' e2 c2 xb xba y)(*strict*)
   defer
   apply(force)
  apply(rename_tac xa j i e c c' e2 c2 xb xba y)(*strict*)
  apply(case_tac "rule_rpop e2")
   apply(rename_tac xa j i e c c' e2 c2 xb xba y)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa j i e c c' e2 c2 xb)(*strict*)
   apply (metis append_Nil butlast_if_match_prefix mutual_prefix_implies_equality prefix_def)
  apply(rename_tac xa j i e c c' e2 c2 xb xba y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa j i e c c' e2 c2 xb y)(*strict*)
  apply(rule butlast_if_match_direct)
  apply(force)
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraDer_preserves_marking_condition: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>dl. parserHFS.derivation_initial G dl \<longrightarrow> parserHFS_marking_condition G dl \<longrightarrow> Ex (maximum_of_domain dl) \<longrightarrow> parserHF_marking_condition G (ATS_Branching_Versus_Linear1.Lin2BraDer parserHFvHFS_Lin2BraConf dl))"
  apply(clarsimp)
  apply(rename_tac G dl x)(*strict*)
  apply(simp add: parserHF_vs_parserHFS.Lin2BraDer_def parserHF_marking_condition_def)
  apply(simp add: parserHFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G dl x i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(simp add: derivation_map_def)
  apply(rule conjI)
   apply(rename_tac G dl x i e c)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G dl x i e c j e' c')(*strict*)
   apply(simp add: parserHFS_marking_configurations_def)
   apply(clarsimp)
   apply(rename_tac G dl x i e c j e' c' f w)(*strict*)
   apply(case_tac "dl j")
    apply(rename_tac G dl x i e c j e' c' f w)(*strict*)
    apply(force)
   apply(rename_tac G dl x i e c j e' c' f w a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac G dl x i e c j e' c' f w a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G dl x i e c j e' f w b)(*strict*)
   apply(simp add: parserHFvHFS_Lin2BraConf_def)
   apply(subgoal_tac "parserHFS_conf_scheduler c = parserHFS_conf_scheduler b \<and> parserHFS_conf_history c = parserHFS_conf_history b")
    apply(rename_tac G dl x i e c j e' f w b)(*strict*)
    apply(force)
   apply(rename_tac G dl x i e c j e' f w b)(*strict*)
   apply(rule_tac
      i="i"
      and j="j"
      in parserHFS_rhs_and_history_invariant_if_input_consumed)
         apply(rename_tac G dl x i e c j e' f w b)(*strict*)
         apply(force)
        apply(rename_tac G dl x i e c j e' f w b)(*strict*)
        apply(force)
       apply(rename_tac G dl x i e c j e' f w b)(*strict*)
       apply(force)
      apply(rename_tac G dl x i e c j e' f w b)(*strict*)
      apply(force)
     apply(rename_tac G dl x i e c j e' f w b)(*strict*)
     apply(force)
    apply(rename_tac G dl x i e c j e' f w b)(*strict*)
    apply(force)
   apply(rename_tac G dl x i e c j e' f w b)(*strict*)
   apply(force)
  apply(rename_tac G dl x i e c)(*strict*)
  apply(subgoal_tac "parserHFvHFS_Lin2BraConf c \<in> parserHF_configurations G")
   apply(rename_tac G dl x i e c)(*strict*)
   apply(simp add: parserHFvHFS_Lin2BraConf_def parserHF_marking_configurations_def parserHFS_marking_configurations_def)
   apply(simp add: parserHF_configurations_def parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G dl x i e f w fa h)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G dl x i e f w fa h c)(*strict*)
   apply(case_tac c)
    apply(rename_tac G dl x i e f w fa h c)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dl x i e f w fa h c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac G dl x i e f w fa h a list)(*strict*)
   apply(case_tac fa)
    apply(rename_tac G dl x i e f w fa h a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dl x i e f w fa h a list aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac G dl x i e c)(*strict*)
  apply(rule parserHF_vs_parserHFS.AX_Lin2BraConf_preserves_configurations)
   apply(rename_tac G dl x i e c)(*strict*)
   apply(force)
  apply(rename_tac G dl x i e c)(*strict*)
  apply(rule parserHFS.belongs_configurations)
   apply(rename_tac G dl x i e c)(*strict*)
   apply(rule parserHFS.derivation_initial_belongs)
    apply(rename_tac G dl x i e c)(*strict*)
    apply(force)
   apply(rename_tac G dl x i e c)(*strict*)
   apply(force)
  apply(rename_tac G dl x i e c)(*strict*)
  apply(force)
  done

lemma parserHF_vs_parserHFS_inst_AX_set_constructed_sched_vs_set_constructed_schedUF: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>cB1. cB1 \<in> parserHFS_configurations G \<longrightarrow> (\<forall>e cB2. (parserHF_conf_fixed cB2 \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHF_step_relation G (parserHFvHFS_Lin2BraConf cB1) e cB2 \<longrightarrow> (\<forall>s. s \<in> parser_schedulers G \<longrightarrow> parserHFvHFS_Bra2LinConf cB2 s \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB2 (parserHF_conf_fixed cB2)) (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB2 s)) = parserHFvHFS_Bra2LinConf cB2 s \<longrightarrow> parserHFS_set_unfixed_scheduler cB1 (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cB1) (parserHFvHFS_Bra2LinStep (parserHFvHFS_Lin2BraConf cB1) e cB2 @ s))) = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cB1) (parserHFvHFS_Bra2LinStep (parserHFvHFS_Lin2BraConf cB1) e cB2 @ s))) \<and> (\<not> parserHF_conf_fixed cB2 \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHF_step_relation G (parserHFvHFS_Lin2BraConf cB1) e cB2 \<longrightarrow> (\<forall>s. s \<in> parser_schedulers G \<longrightarrow> parserHFvHFS_Bra2LinConf cB2 s \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB2 (parserHF_conf_fixed cB2 @ [parser_bottom G])) (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB2 s)) = parserHFvHFS_Bra2LinConf cB2 s \<longrightarrow> parserHFS_set_unfixed_scheduler cB1 (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cB1) (parserHFvHFS_Bra2LinStep (parserHFvHFS_Lin2BraConf cB1) e cB2 @ s))) = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cB1) (parserHFvHFS_Bra2LinStep (parserHFvHFS_Lin2BraConf cB1) e cB2 @ s)))))"
  apply(clarsimp)
  apply(rename_tac G cB1 e cB2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cB1 e cB2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G cB1 e cB2 s)(*strict*)
   apply(simp add: parserHFS_set_unfixed_scheduler_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def)
   apply(case_tac cB1)
   apply(rename_tac G cB1 e cB2 s parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e cB2 s parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
   apply(rename_tac f h l r)
   apply(rename_tac G e cB2 s f h l r)(*strict*)
   apply(subgoal_tac "s=parserHF_conf_fixed cB2")
    apply(rename_tac G e cB2 s f h l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e cB2 f h l r)(*strict*)
    apply(subgoal_tac "valid_parser_step_label G e")
     apply(rename_tac G e cB2 f h l r)(*strict*)
     prefer 2
     apply(simp add: parserHF_step_relation_def valid_parser_def)
    apply(rename_tac G e cB2 f h l r)(*strict*)
    apply(simp add: parserHF_step_relation_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac G e cB2 f h r k w xa xb)(*strict*)
    apply(thin_tac "the (left_quotient_word (rule_rpush e @ drop (length (kPrefix k (w @ [parser_bottom G]))) f) (rule_rpush e @ drop (length (kPrefix k (w @ [parser_bottom G]))) f)) = []")
    apply(rename_tac G e cB2 f h r k w xa xb)(*strict*)
    apply(simp add: parserHFvHFS_Bra2LinStep_def)
    apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xb"
      in ssubst)
     apply(rename_tac G e cB2 f h r k w xa xb)(*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G e cB2 f h r k w xa xb)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac G e cB2 f h r k w xa xb)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac G e cB2 h r k w xa xb c)(*strict*)
     apply(rule_tac
      t="left_quotient_word (kPrefix k (w @ [parser_bottom G]) @ c) (xb @ rule_rpush e @ c)"
      and s="Some []"
      in ssubst)
      apply(rename_tac G e cB2 h r k w xa xb c)(*strict*)
      apply(rule left_quotient_word_Some_by_append)
      apply(force)
     apply(rename_tac G e cB2 h r k w xa xb c)(*strict*)
     apply(force)
    apply(rename_tac G e cB2 f h r k w xa xb)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
    apply(rule_tac
      t="left_quotient_word f (xb @ rule_rpush e @ drop (length (kPrefix k (w @ [parser_bottom G]))) f)"
      and s="Some c"
      in ssubst)
     apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
     apply(rule left_quotient_word_Some_by_append)
     apply(rule_tac
      t="f @ c"
      and s="kPrefix k (w @ [parser_bottom G])"
      in ssubst)
      apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
      apply(force)
     apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
     apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xb @ rule_rpush e"
      in ssubst)
      apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
      apply(force)
     apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
     apply(rule_tac
      t="drop (length (xb @ rule_rpush e)) f"
      and s="[]"
      in ssubst)
      apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
      apply(rule_tac
      t="xb @ rule_rpush e"
      and s="kPrefix k (w @ [parser_bottom G])"
      in ssubst)
       apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
       apply(force)
      apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
      apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="f@c"
      in ssubst)
       apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
       apply(force)
      apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
     apply(force)
    apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="drop (length (kPrefix k (w @ [parser_bottom G]))) f"
      and s="[]"
      in ssubst)
     apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
    apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="f@c"
      in ssubst)
     apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
     apply(force)
    apply(rename_tac G e cB2 f h r k w xa xb c)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac G e cB2 s f h l r)(*strict*)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G e cB2 f h l w wa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e cB2 f h l w wa c ca)(*strict*)
   apply(case_tac ca)
    apply(rename_tac G e cB2 f h l w wa c ca)(*strict*)
    apply(force)
   apply(rename_tac G e cB2 f h l w wa c ca a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
    apply(rename_tac G e cB2 f h l w wa c ca a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e cB2 f h l w wa c ca a list)(*strict*)
   apply(thin_tac "ca=a#list")
   apply(clarsimp)
   apply(rename_tac G e cB2 f h l w c w')(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
  apply(rename_tac G cB1 e cB2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G cB1 e cB2 s)(*strict*)
  apply(simp add: parserHFS_set_unfixed_scheduler_def parserHFvHFS_Bra2LinConf_def parserHFS_get_unfixed_scheduler_def)
  apply(subgoal_tac "prefix (parserHF_conf_fixed cB2) s")
   apply(rename_tac G cB1 e cB2 s)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G cB1 e cB2 c)(*strict*)
   apply(simp add: parserHFS_set_unfixed_scheduler_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def)
   apply(case_tac cB1)
   apply(rename_tac G cB1 e cB2 c parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e cB2 c parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
   apply(rename_tac f h l r)
   apply(rename_tac G e cB2 c f h l r)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G e")
    apply(rename_tac G e cB2 c f h l r)(*strict*)
    prefer 2
    apply(simp add: parserHF_step_relation_def valid_parser_def)
   apply(rename_tac G e cB2 c f h l r)(*strict*)
   apply(simp add: parserHF_step_relation_def valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G e cB2 c f h r k w xa xb)(*strict*)
   apply(thin_tac "the (left_quotient_word (rule_rpush e @ drop (length (kPrefix k (w @ [parser_bottom G]))) f) (rule_rpush e @ drop (length (kPrefix k (w @ [parser_bottom G]))) f @ c)) = c")
   apply(rename_tac G e cB2 c f h r k w xa xb)(*strict*)
   apply(simp add: parserHFvHFS_Bra2LinStep_def)
   apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xb"
      in ssubst)
    apply(rename_tac G e cB2 c f h r k w xa xb)(*strict*)
    apply(rule right_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac G e cB2 c f h r k w xa xb)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G e cB2 c f h r k w xa xb)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e cB2 c h r k w xa xb ca)(*strict*)
    apply(rule_tac
      t="left_quotient_word (kPrefix k (w @ [parser_bottom G]) @ ca) (xb @ rule_rpush e @ ca @ c)"
      and s="Some c"
      in ssubst)
     apply(rename_tac G e cB2 c h r k w xa xb ca)(*strict*)
     apply(rule left_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G e cB2 c h r k w xa xb ca)(*strict*)
    apply(force)
   apply(rename_tac G e cB2 c f h r k w xa xb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
   apply(subgoal_tac "drop (length (kPrefix k (w @ [parser_bottom G]))) f = []")
    apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
    prefer 2
    apply(clarsimp)
    apply (metis drop_length_append)
   apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="xb @ rule_rpush e @ c"
      and s="kPrefix k (w @ [parser_bottom G]) @ c"
      in ssubst)
    apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
    apply(force)
   apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="f@ca"
      in ssubst)
    apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
    apply(force)
   apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
   apply(rule_tac
      t="left_quotient_word f ((f @ ca) @ c)"
      and s="Some (ca@c)"
      in ssubst)
    apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
    apply(rule left_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac G e cB2 c f h r k w xa xb ca)(*strict*)
   apply(force)
  apply(rename_tac G cB1 e cB2 s)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  done

lemma parserHF_vs_parserHFS_inst_set_constructed_sched_vs_set_constructed_schedUF_Fin: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>cB1. (parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cB1) \<sqsupseteq> [parser_bottom G] \<longrightarrow> cB1 \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_unfixed_scheduler cB1 (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cB1) (parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cB1)))) = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cB1) (parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cB1))) \<and> (\<not> parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cB1) \<sqsupseteq> [parser_bottom G] \<longrightarrow> cB1 \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_unfixed_scheduler cB1 (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cB1) (parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cB1) @ [parser_bottom G]))) = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cB1) (parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cB1) @ [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G cB1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cB1)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS_set_unfixed_scheduler_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def)
   apply(case_tac cB1)
   apply(rename_tac G cB1 parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
   apply(simp add: left_quotient_word_def)
  apply(rename_tac G cB1)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_set_unfixed_scheduler_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def)
  apply(case_tac cB1)
  apply(rename_tac G cB1 parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
  apply(simp add: left_quotient_word_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraConf_Bra2LinConf_idemp: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>cB. cB \<in> parserHF_configurations G \<longrightarrow> (\<forall>s. s \<in> parser_schedulers G \<longrightarrow> parserHFvHFS_Bra2LinConf cB s \<in> parserHFS_configurations G \<longrightarrow> cB = parserHFvHFS_Lin2BraConf (parserHFvHFS_Bra2LinConf cB s))))"
  apply(clarsimp)
  apply(rename_tac G cB s)(*strict*)
  apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFvHFS_Bra2LinConf_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_set_constructed_sched_vs_set_constructed_schedUF_prime_prime: "
  \<forall>G c1L c3L cB e c2L sE3 sE2 sE1. valid_parser G \<longrightarrow> c1L \<in> parserHFS_configurations G \<longrightarrow> c3L \<in> parserHFS_configurations G \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> parserHFS_step_relation G c1L e c2L \<longrightarrow> parserHFS_set_unfixed_scheduler c2L (sE3 @ parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf c3L) (sE2 @ (if parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed cB else parserHF_conf_fixed cB @ [parser_bottom G])))) = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf c2L) ((sE1 @ sE2) @ (if parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed cB else parserHF_conf_fixed cB @ [parser_bottom G])) \<longrightarrow> parserHFS_set_unfixed_scheduler c1L ((the (right_quotient_word (parserHFS_get_unfixed_scheduler c1L) (parserHFS_get_unfixed_scheduler c2L)) @ sE3) @ parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf c3L) (sE2 @ (if parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G]
then parserHF_conf_fixed cB else parserHF_conf_fixed cB @ [parser_bottom G])))) = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf c1L) ((parserHFvHFS_Bra2LinStep (parserHFvHFS_Lin2BraConf c1L) e (parserHFvHFS_Lin2BraConf c2L) @ sE1 @ sE2) @ (if parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed cB else parserHF_conf_fixed cB @ [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G c1L c3L cB)(*strict*)
  apply(rule conjI)
   apply(rename_tac G c1L c3L cB)(*strict*)
   apply(clarsimp)
   apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
   apply(subgoal_tac "c2L \<in> parserHFS_configurations G")
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    apply(simp add: parserHFvHFS_Bra2LinStep_def parserHFvHFS_Bra2LinConf_def parserHFS_set_unfixed_scheduler_def parserHFvHFS_Lin2BraConf_def)
    apply(subgoal_tac "parserHFS_get_unfixed_scheduler c1L \<sqsupseteq> parserHFS_get_unfixed_scheduler c2L")
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     prefer 2
     apply(rule parserHFS_unfixed_is_reduced_by_single_step)
         apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
         apply(force)
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
        apply(force)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
       apply(simp add: parserHFS_step_relation_def valid_parser_def)
       apply(force)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
      apply(rule parserHFS.AX_step_relation_preserves_belongsC)
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
        apply(force)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
       apply(force)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
      apply(force)
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    apply(simp add: suffix_def)
    apply(subgoal_tac "prefix (parserHFS_conf_fixed c2L) (parserHFS_conf_scheduler c2L)")
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     apply(subgoal_tac "prefix (parserHFS_conf_fixed c1L) (parserHFS_conf_scheduler c1L)")
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
      apply(subgoal_tac "prefix (parserHFS_conf_fixed c3L) (parserHFS_conf_scheduler c3L)")
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
       apply(clarsimp)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca)(*strict*)
       apply(rule_tac
      t="right_quotient_word (parserHFS_get_unfixed_scheduler c1L) (parserHFS_get_unfixed_scheduler c2L)"
      and s="Some ca"
      in ssubst)
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca)(*strict*)
        apply(rule right_quotient_word_Some_by_append)
        apply(force)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca)(*strict*)
       apply(rule_tac
      t="right_quotient_word (ca @ parserHFS_get_unfixed_scheduler c2L) (parserHFS_get_unfixed_scheduler c2L)"
      and s="Some ca"
      in ssubst)
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca)(*strict*)
        apply(rule right_quotient_word_Some_by_append)
        apply(force)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "valid_parser_step_label G e")
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca)(*strict*)
        apply(simp add: parserHFS_get_unfixed_scheduler_def)
        apply(simp add: prefix_def)
        apply(clarsimp)
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb cc "cd")(*strict*)
        apply(subgoal_tac "left_quotient_word (parserHFS_conf_fixed c1L) (parserHFS_conf_scheduler c1L) = Some cc")
         apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb cc "cd")(*strict*)
         apply(clarsimp)
         apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb "cd")(*strict*)
         apply(subgoal_tac "left_quotient_word (parserHFS_conf_fixed c2L) (parserHFS_conf_scheduler c2L) = Some cb")
          apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb "cd")(*strict*)
          apply(clarsimp)
          apply(case_tac c1L)
          apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb "cd" parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
          apply(case_tac c2L)
          apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb "cd" parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historyaa parserHFS_conf_stackaa parserHFS_conf_scheduleraa)(*strict*)
          apply(clarsimp)
          apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cb "cd" parserHFS_conf_fixeda parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_fixedaa parserHFS_conf_historya parserHFS_conf_stacka)(*strict*)
          apply(rename_tac f1 h1 l1 f2 h2 l2)
          apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cb "cd" f1 h1 l1 f2 h2 l2)(*strict*)
          apply(rule_tac
      t="sE1 @ sE2 @ c @ [parser_bottom G]"
      and s="f2 @ sE3 @ the (left_quotient_word (parserHFS_conf_fixed c3L) (sE2 @ c @ [parser_bottom G]))"
      in ssubst)
           apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cb "cd" f1 h1 l1 f2 h2 l2)(*strict*)
           apply(force)
          apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cb "cd" f1 h1 l1 f2 h2 l2)(*strict*)
          apply(simp (no_asm))
          apply(thin_tac "f2 @ sE3 @ the (left_quotient_word (parserHFS_conf_fixed c3L) (sE2 @ c @ [parser_bottom G])) = sE1 @ sE2 @ c @ [parser_bottom G]")
          apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cb "cd" f1 h1 l1 f2 h2 l2)(*strict*)
          apply(simp add: parserHFS_step_relation_def)
          apply(rename_tac G c3L cB e c ca cb "cd" f1 h1 l1 f2 h2 l2)(*strict*)
          apply(clarsimp)
          apply(rename_tac G c3L cB e c ca cb "cd" f1 h1 x y)(*strict*)
          apply(simp add: valid_parser_step_label_def)
          apply(clarsimp)
          apply(rename_tac G c3L cB e c ca cb "cd" f1 h1 x y k w xb)(*strict*)
          apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xb"
      in ssubst)
           apply(rename_tac G c3L cB e c ca cb "cd" f1 h1 x y k w xb)(*strict*)
           apply(rule right_quotient_word_Some_by_append)
           apply(force)
          apply(rename_tac G c3L cB e c ca cb "cd" f1 h1 x y k w xb)(*strict*)
          apply(force)
         apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb "cd")(*strict*)
         apply(rule left_quotient_word_Some_by_append)
         apply(force)
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb cc "cd")(*strict*)
        apply(rule left_quotient_word_Some_by_append)
        apply(force)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca)(*strict*)
       apply(simp add: valid_parser_def parserHFS_step_relation_def)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
      apply(simp add: parserHFS_configurations_def)
      apply(force)
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     apply(simp add: parserHFS_configurations_def)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    apply(simp add: parserHFS_configurations_def)
    apply(force)
   apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
   apply(rule parserHFS.AX_step_relation_preserves_belongsC)
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    apply(force)
   apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
   apply(force)
  apply(rename_tac G c1L c3L cB)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
  apply(subgoal_tac "c2L \<in> parserHFS_configurations G")
   apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
   apply(simp add: parserHFvHFS_Bra2LinStep_def parserHFvHFS_Bra2LinConf_def parserHFS_set_unfixed_scheduler_def parserHFvHFS_Lin2BraConf_def)
   apply(subgoal_tac "parserHFS_get_unfixed_scheduler c1L \<sqsupseteq> parserHFS_get_unfixed_scheduler c2L")
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    prefer 2
    apply(rule parserHFS_unfixed_is_reduced_by_single_step)
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
        apply(force)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
       apply(force)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
      apply(simp add: parserHFS_step_relation_def valid_parser_def)
      apply(force)
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     apply(rule parserHFS.AX_step_relation_preserves_belongsC)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
       apply(force)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
      apply(force)
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    apply(force)
   apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
   apply(simp add: suffix_def)
   apply(subgoal_tac "prefix (parserHFS_conf_fixed c2L) (parserHFS_conf_scheduler c2L)")
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    apply(subgoal_tac "prefix (parserHFS_conf_fixed c1L) (parserHFS_conf_scheduler c1L)")
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     apply(subgoal_tac "prefix (parserHFS_conf_fixed c3L) (parserHFS_conf_scheduler c3L)")
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
      apply(clarsimp)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c)(*strict*)
      apply(rule_tac
      t="right_quotient_word (parserHFS_get_unfixed_scheduler c1L) (parserHFS_get_unfixed_scheduler c2L)"
      and s="Some c"
      in ssubst)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c)(*strict*)
       apply(rule right_quotient_word_Some_by_append)
       apply(force)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c)(*strict*)
      apply(rule_tac
      t="right_quotient_word (c @ parserHFS_get_unfixed_scheduler c2L) (parserHFS_get_unfixed_scheduler c2L)"
      and s="Some c"
      in ssubst)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c)(*strict*)
       apply(rule right_quotient_word_Some_by_append)
       apply(force)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "valid_parser_step_label G e")
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c)(*strict*)
       apply(simp add: parserHFS_get_unfixed_scheduler_def)
       apply(simp add: prefix_def)
       apply(clarsimp)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb cc)(*strict*)
       apply(subgoal_tac "left_quotient_word (parserHFS_conf_fixed c1L) (parserHFS_conf_scheduler c1L) = Some cb")
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb cc)(*strict*)
        apply(clarsimp)
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cc)(*strict*)
        apply(subgoal_tac "left_quotient_word (parserHFS_conf_fixed c2L) (parserHFS_conf_scheduler c2L) = Some ca")
         apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cc)(*strict*)
         apply(clarsimp)
         apply(case_tac c1L)
         apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cc parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
         apply(case_tac c2L)
         apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cc parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historyaa parserHFS_conf_stackaa parserHFS_conf_scheduleraa)(*strict*)
         apply(clarsimp)
         apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc parserHFS_conf_fixeda parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_fixedaa parserHFS_conf_historya parserHFS_conf_stacka)(*strict*)
         apply(rename_tac f1 h1 l1 f2 h2 l2)
         apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 l1 f2 h2 l2)(*strict*)
         apply(thin_tac "left_quotient_word f1 (f1 @ c @ ca) = Some (c @ ca)")
         apply(thin_tac "left_quotient_word f2 (f2 @ ca) = Some ca")
         apply(simp add: parserHFS_step_relation_def)
         apply(clarsimp)
         apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 x y)(*strict*)
         apply(simp add: valid_parser_step_label_def)
         apply(clarsimp)
         apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 x y k w xb)(*strict*)
         apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xb"
      in ssubst)
          apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 x y k w xb)(*strict*)
          apply(rule right_quotient_word_Some_by_append)
          apply(force)
         apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 x y k w xb)(*strict*)
         apply(clarsimp)
         apply(rule_tac
      t="f1 @ c @ sE3 @ the (left_quotient_word (parserHFS_conf_fixed c3L) (sE2 @ parserHF_conf_fixed cB @ [parser_bottom G]))"
      and s="kPrefix k (w @ [parser_bottom G]) @ drop (length (kPrefix k (w @ [parser_bottom G]))) f1@ sE3 @ the (left_quotient_word (parserHFS_conf_fixed c3L) (sE2 @ parserHF_conf_fixed cB @ [parser_bottom G]))"
      in ssubst)
          apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 x y k w xb)(*strict*)
          apply(force)
         apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 x y k w xb)(*strict*)
         apply(rule_tac
      P="\<lambda>X. X @ drop (length (kPrefix k (w @ [parser_bottom G]))) f1 @ sE3 @ the (left_quotient_word (parserHFS_conf_fixed c3L) (sE2 @ parserHF_conf_fixed cB @ [parser_bottom G])) = xb @ sE1 @ sE2 @ parserHF_conf_fixed cB @ [parser_bottom G]"
      and t="kPrefix k (w @ [parser_bottom G])"
      and s="xb @ rule_rpush e"
      in ssubst)
          apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 x y k w xb)(*strict*)
          apply(force)
         apply(rename_tac G c3L cB e sE3 sE2 sE1 c ca cc f1 h1 x y k w xb)(*strict*)
         apply(simp (no_asm))
        apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cc)(*strict*)
        apply(rule left_quotient_word_Some_by_append)
        apply(force)
       apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c ca cb cc)(*strict*)
       apply(rule left_quotient_word_Some_by_append)
       apply(force)
      apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1 c)(*strict*)
      apply(simp add: valid_parser_def parserHFS_step_relation_def)
     apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
     apply(simp add: parserHFS_configurations_def)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    apply(simp add: parserHFS_configurations_def)
    apply(force)
   apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
   apply(simp add: parserHFS_configurations_def)
   apply(force)
  apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
  apply(rule parserHFS.AX_step_relation_preserves_belongsC)
    apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
    apply(force)
   apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
   apply(force)
  apply(rename_tac G c1L c3L cB e c2L sE3 sE2 sE1)(*strict*)
  apply(force)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinConf_triv_with_get_scheduler: "
   \<forall>G cL. valid_parser G \<longrightarrow>
           cL \<in> parserHFS_configurations G \<longrightarrow>
           parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) (parserHFS_get_scheduler cL) =
           cL"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFS_get_scheduler_def parserHFvHFS_Lin2BraConf_def)
  done

lemma parserHF_vs_parserHFS_inst_lin_unfixed_scheduler_right_quotient_drop_proper1: "
  \<forall>G cL cB sE. valid_parser G \<longrightarrow> cL \<in> parserHFS_configurations G \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> sE \<in> parser_scheduler_fragments G \<longrightarrow> \<not> \<not> parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] \<longrightarrow> the (right_quotient_word (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB (sE @ (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @ [parser_bottom G])))) (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @ [parser_bottom G])))) = the (right_quotient_word (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB (sE @ (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @ [parser_bottom G])))) [])"
  apply(clarsimp)
  apply(rename_tac G cL cB sE)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Lin2BraConf_def)
  apply(rule_tac
      t="left_quotient_word (parserHFS_conf_fixed cL) (parserHFS_conf_fixed cL)"
      and s="Some []"
      in ssubst)
   apply(rename_tac G cL cB sE)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cL cB sE)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_lin_unfixed_scheduler_right_quotient_drop_proper: "
  (\<forall>G cL cB sE. valid_parser G \<longrightarrow> cL \<in> parserHFS_configurations G \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> sE \<in> parser_scheduler_fragments G \<longrightarrow> parserHFvHFS_Bra2LinConf cB (sE @ (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @ [parser_bottom G])) \<in> parserHFS_configurations G \<longrightarrow> (\<not> \<not> parserHF_conf_fixed cB \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> \<not> parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G]) \<longrightarrow> parserHFS_set_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB (sE @ (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @ [parser_bottom G]))) (the (right_quotient_word (parserHFS_get_unfixed_scheduler
(parserHFvHFS_Bra2LinConf cB (sE @ (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @ [parser_bottom G])))) (parserHFS_get_unfixed_scheduler (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @ [parser_bottom G])))) @ parserHFS_get_unfixed_scheduler cL) = parserHFvHFS_Bra2LinConf cB (sE @ parserHFS_get_scheduler cL))"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cL)(*strict*)
   apply(clarsimp)
   apply(rename_tac G cL cB sE)(*strict*)
   apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Lin2BraConf_def parserHFS_set_unfixed_scheduler_def)
   apply(rule_tac
      t="left_quotient_word (parserHFS_conf_fixed cL) (parserHFS_conf_fixed cL)"
      and s="Some []"
      in ssubst)
    apply(rename_tac G cL cB sE)(*strict*)
    apply(rule left_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac G cL cB sE)(*strict*)
   apply(clarsimp)
   apply(simp add: right_quotient_word_def)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G cB sE f h l w wa)(*strict*)
   apply(simp add: prefix_def suffix_def parserHFS_get_scheduler_def)
   apply(clarsimp)
   apply(rename_tac G cB sE l wa c ca cb cc "cd")(*strict*)
   apply(subgoal_tac "cc=[]")
    apply(rename_tac G cB sE l wa c ca cb cc "cd")(*strict*)
    apply(clarsimp)
    apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
    apply(rule_tac
      t="left_quotient_word (wa @ [parser_bottom G]) (wa @ [parser_bottom G])"
      and s="Some []"
      in ssubst)
     apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
     apply(rule left_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="left_quotient_word (parserHF_conf_fixed cB) (sE @ wa @ [parser_bottom G])"
      and s="Some ca"
      in ssubst)
     apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
     apply(rule left_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
    apply(clarsimp)
   apply(rename_tac G cB sE l wa c ca cb cc "cd")(*strict*)
   apply(case_tac cc)
    apply(rename_tac G cB sE l wa c ca cb cc "cd")(*strict*)
    apply(clarsimp)
   apply(rename_tac G cB sE l wa c ca cb cc "cd" a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cc = w' @ [x']")
    apply(rename_tac G cB sE l wa c ca cb cc "cd" a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G cB sE l wa c ca cb cc "cd" a list)(*strict*)
   apply(thin_tac "cc=a#list")
   apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(clarsimp)
  apply(rename_tac G cL cB sE)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Lin2BraConf_def parserHFS_set_unfixed_scheduler_def parserHFS_get_scheduler_def)
  apply(rule_tac
      t="left_quotient_word (parserHFS_conf_fixed cL) (parserHFS_conf_fixed cL @ [parser_bottom G])"
      and s="Some [parser_bottom G]"
      in ssubst)
   apply(rename_tac G cL cB sE)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cL cB sE)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G cB sE f h l w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G cB sE f h l w c ca)(*strict*)
  apply(rule_tac
      t="left_quotient_word f (w @ [parser_bottom G])"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G cB sE f h l w c ca)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cB sE f h l w c ca)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="left_quotient_word (parserHF_conf_fixed cB) (sE @ f @ [parser_bottom G])"
      and s="Some c"
      in ssubst)
   apply(rename_tac G cB sE f h l w c ca)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cB sE f h l w c ca)(*strict*)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G cB sE f l w c ca cb cc)(*strict*)
  apply(case_tac ca)
   apply(rename_tac G cB sE f l w c ca cb cc)(*strict*)
   apply(force)
  apply(rename_tac G cB sE f l w c ca cb cc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac G cB sE f l w c ca cb cc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G cB sE f l w c ca cb cc a list)(*strict*)
  apply(thin_tac "ca=a#list")
  apply(clarsimp)
  apply(rename_tac G cB sE f l c cb cc w')(*strict*)
  apply(case_tac c)
   apply(rename_tac G cB sE f l c cb cc w')(*strict*)
   apply(force)
  apply(rename_tac G cB sE f l c cb cc w' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac G cB sE f l c cb cc w' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G cB sE f l c cb cc w' a list)(*strict*)
  apply(thin_tac "c=a#list")
  apply(clarsimp)
  apply(rename_tac G cB sE f l cb cc w' w'a)(*strict*)
  apply(rule_tac
      t="right_quotient_word (w'a @ [parser_bottom G]) [parser_bottom G]"
      and s="Some w'a"
      in ssubst)
   apply(rename_tac G cB sE f l cb cc w' w'a)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cB sE f l cb cc w' w'a)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraConf_ignores_set_unfixed_scheduler: "
  \<forall>G cB s sUF. valid_parser G \<longrightarrow> cB \<in> parserHF_configurations G \<longrightarrow> s \<in> parser_schedulers G \<longrightarrow> cB = parserHFvHFS_Lin2BraConf (parserHFS_set_unfixed_scheduler (parserHFvHFS_Bra2LinConf cB s) sUF)"
  apply(clarsimp)
  apply(rename_tac G cB s sUF)(*strict*)
  apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFvHFS_Bra2LinConf_def parserHFS_set_unfixed_scheduler_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraConf_preserves_fixed_scheduler_extendable: "
  \<forall>G cL.
       valid_parser G \<longrightarrow>
       cL \<in> parserHFS_configurations G \<longrightarrow>
       parser_fixed_scheduler_extendable G
        (parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL)) =
       parser_fixed_scheduler_extendable G (parserHFS_conf_fixed cL)"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(simp add: parserHFvHFS_Lin2BraConf_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_preserves_marking_condition: "
  \<forall>G. valid_parser G \<longrightarrow>
        (\<forall>db. parserHF.derivation_initial G db \<longrightarrow>
              parserHF_marking_condition G db \<longrightarrow>
              (\<forall>n. maximum_of_domain db n \<longrightarrow>
                   parserHFS_marking_condition G
                    (parserHF_vs_parserHFS.Bra2LinDer
                      G db n)))"
  apply(clarsimp)
  apply(rename_tac G db n)(*strict*)
  apply(rename_tac G dl n)
  apply(rename_tac G dl n)(*strict*)
  apply(simp add: parserHFS_marking_condition_def parserHF_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G dl n i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
  apply(subgoal_tac "i\<le>n")
   apply(rename_tac G dl n i e c)(*strict*)
   prefer 2
   apply(rule parserHF.allPreMaxDomSome_prime)
     apply(rename_tac G dl n i e c)(*strict*)
     apply(simp add: parserHF.derivation_initial_def)
     apply(force)
    apply(rename_tac G dl n i e c)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c)(*strict*)
   apply(force)
  apply(rename_tac G dl n i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dl n = Some (pair e c)")
   apply(rename_tac G dl n i e c)(*strict*)
   prefer 2
   apply(rule parserHF.some_position_has_details_before_max_dom)
     apply(rename_tac G dl n i e c)(*strict*)
     apply(simp add: parserHF.derivation_initial_def)
     apply(force)
    apply(rename_tac G dl n i e c)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c)(*strict*)
   apply(force)
  apply(rename_tac G dl n i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dl n i e c ea ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G dl n i e c ea ca)(*strict*)
   apply(simp add: parserHF_marking_configurations_def suffix_def parserHFS_marking_configurations_def)
   apply(clarsimp)
   apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
   apply(subgoal_tac "cb=[]")
    apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac G dl n i e c ea ca f w)(*strict*)
    apply(subgoal_tac "parserHFvHFS_Bra2LinConf c (parserHF_vs_parserHFS.Bra2LinDer' G dl n i @ [parser_bottom G]) \<in> parserHFS_configurations G")
     apply(rename_tac G dl n i e c ea ca f w)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHF_vs_parserHFS.Bra2LinDer'_def)
     apply(rule conjI)
      apply(rename_tac G dl n i e c ea ca f w)(*strict*)
      apply(simp add: parserHFvHFS_Bra2LinConf_def)
     apply(rename_tac G dl n i e c ea ca f w)(*strict*)
     apply(case_tac n)
      apply(rename_tac G dl n i e c ea ca f w)(*strict*)
      apply(clarsimp)
      apply(rename_tac G dl e c f w)(*strict*)
      apply(simp add: parserHFvHFS_Bra2LinConf_def)
     apply(rename_tac G dl n i e c ea ca f w nat)(*strict*)
     apply(simp add: parserHFvHFS_Bra2LinConf_def)
     apply(rule foldl_emptyX)
     apply(rename_tac G dl n i e c ea ca f w nat ia)(*strict*)
     apply(clarsimp)
     apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
     apply(subgoal_tac "length (nat_seq i nat) = nat + 1 - i")
      apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
      prefer 2
      apply(rule nat_seq_length_prime)
     apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
     apply(rule_tac
      t="nat_seq i nat ! ia"
      and s="i+ia"
      in ssubst)
      apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
      apply(rule nat_seq_nth_compute)
       apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
       apply(force)
      apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
      apply(force)
     apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "\<exists>e1 e2 c1 c2. dl (i+ia) = Some (pair e1 c1) \<and> dl (Suc(i+ia)) = Some (pair (Some e2) c2) \<and> parserHF_step_relation G c1 e2 c2")
      apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
      prefer 2
      apply(rule_tac
      m="Suc nat"
      in parserHF.step_detail_before_some_position)
        apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
        apply(simp add: parserHF.derivation_initial_def)
       apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
       apply(force)
      apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
      apply(force)
     apply(rename_tac G dl i e c ea ca f w nat ia)(*strict*)
     apply(clarsimp)
     apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
     apply(simp add: parserHFvHFS_Bra2LinStep_def)
     apply(rule_tac
      d="dl"
      and i="i"
      and n="i+ia"
      and m="nat - i - ia"
      in parserHF_steps_are_empty2)
               apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
               apply(force)
              apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
              apply(simp add: parserHF.derivation_initial_def)
             apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
             apply(rule parserHF.derivation_initial_belongs)
              apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
              apply(force)
             apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
             apply(force)
            apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
            apply(force)
           apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
           apply(force)
          apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
          apply(force)
         apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
         apply(force)
        apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac G dl i e c ea ca f w nat ia e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac G dl n i e c ea ca f w)(*strict*)
    apply(rule_tac n="n" and m="i" in parserHF_vs_parserHFS.Bra2LinDer_preserves_configurations_prime)
          apply(rename_tac G dl n i e c ea ca f w)(*strict*)
          apply(force)
         apply(rename_tac G dl n i e c ea ca f w)(*strict*)
         apply(simp add: parserHF.derivation_initial_def)
         apply(force)
        apply(rename_tac G dl n i e c ea ca f w)(*strict*)
        apply(rule parserHF.derivation_initial_belongs)
         apply(rename_tac G dl n i e c ea ca f w)(*strict*)
         apply(force)
        apply(rename_tac G dl n i e c ea ca f w)(*strict*)
        apply(force)
       apply(rename_tac G dl n i e c ea ca f w)(*strict*)
       apply(force)
      apply(rename_tac G dl n i e c ea ca f w)(*strict*)
      apply(force)
     apply(rename_tac G dl n i e c ea ca f w)(*strict*)
     apply(force)
    apply(rename_tac G dl n i e c ea ca f w)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: suffix_def)
   apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
   apply(subgoal_tac "parserHF_conf_fixed ca = [] \<or> parserHF_conf_fixed ca = [parser_bottom G]")
    apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
   apply(rule_tac
      d="dl"
      and i="i"
      and n="n"
      in parserHF_steps_are_empty1)
          apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
          apply(force)
         apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
         apply(simp add: parserHF.derivation_initial_def)
        apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
        apply(rule parserHF.derivation_initial_belongs)
         apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
         apply(force)
        apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
        apply(force)
       apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
       apply(force)
      apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
      apply(force)
     apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
     apply(force)
    apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c ea ca f w cb)(*strict*)
   apply(force)
  apply(rename_tac G dl n i e c ea ca)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(simp add: parserHF_marking_configurations_def suffix_def parserHFS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G dl n i e c ea ca f w)(*strict*)
  apply(subgoal_tac "parserHFvHFS_Bra2LinConf c (parserHF_vs_parserHFS.Bra2LinDer' G dl n i @ parserHF_conf_fixed ca @ [parser_bottom G]) \<in> parserHFS_configurations G")
   apply(rename_tac G dl n i e c ea ca f w)(*strict*)
   prefer 2
   apply(rule_tac n="n" and m="i" in parserHF_vs_parserHFS.Bra2LinDer_preserves_configurations_prime)
         apply(rename_tac G dl n i e c ea ca f w)(*strict*)
         apply(force)
        apply(rename_tac G dl n i e c ea ca f w)(*strict*)
        apply(simp add: parserHF.derivation_initial_def)
        apply(force)
       apply(rename_tac G dl n i e c ea ca f w)(*strict*)
       apply(rule parserHF.derivation_initial_belongs)
        apply(rename_tac G dl n i e c ea ca f w)(*strict*)
        apply(force)
       apply(rename_tac G dl n i e c ea ca f w)(*strict*)
       apply(force)
      apply(rename_tac G dl n i e c ea ca f w)(*strict*)
      apply(force)
     apply(rename_tac G dl n i e c ea ca f w)(*strict*)
     apply(force)
    apply(rename_tac G dl n i e c ea ca f w)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c ea ca f w)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: suffix_def)
  apply(rename_tac G dl n i e c ea ca f w)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G dl n i e c ea ca f w)(*strict*)
   apply(simp add: parserHFvHFS_Bra2LinConf_def)
  apply(rename_tac G dl n i e c ea ca f w)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def)
  apply(simp add: parserHF_vs_parserHFS.Bra2LinDer'_def)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(subgoal_tac "parserHF_conf_fixed ca = []")
   apply(rename_tac G dl n i e c ea ca f w)(*strict*)
   prefer 2
   apply(subgoal_tac "parserHF_conf_fixed ca = [] \<or> parserHF_conf_fixed ca = [parser_bottom G]")
    apply(rename_tac G dl n i e c ea ca f w)(*strict*)
    prefer 2
    apply(rule_tac
      c="c"
      and d="dl"
      and i="i"
      and n="n"
      in parserHF_steps_are_empty1)
           apply(rename_tac G dl n i e c ea ca f w)(*strict*)
           apply(force)
          apply(rename_tac G dl n i e c ea ca f w)(*strict*)
          apply(simp add: parserHF.derivation_initial_def)
         apply(rename_tac G dl n i e c ea ca f w)(*strict*)
         apply(rule parserHF.derivation_initial_belongs)
          apply(rename_tac G dl n i e c ea ca f w)(*strict*)
          apply(force)
         apply(rename_tac G dl n i e c ea ca f w)(*strict*)
         apply(force)
        apply(rename_tac G dl n i e c ea ca f w)(*strict*)
        apply(force)
       apply(rename_tac G dl n i e c ea ca f w)(*strict*)
       apply(force)
      apply(rename_tac G dl n i e c ea ca f w)(*strict*)
      apply(force)
     apply(rename_tac G dl n i e c ea ca f w)(*strict*)
     apply(force)
    apply(rename_tac G dl n i e c ea ca f w)(*strict*)
    apply(force)
   apply(rename_tac G dl n i e c ea ca f w)(*strict*)
   apply(erule_tac
      P="parserHF_conf_fixed ca = []"
      in disjE)
    apply(rename_tac G dl n i e c ea ca f w)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dl n i e c ea ca f w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G dl n i e c ea ca f w)(*strict*)
  apply(clarsimp)
  apply(rule foldl_emptyX)
  apply(rename_tac G dl n i e c ea ca f w ia)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
   apply(rename_tac G dl n i e c ea ca f w ia)(*strict*)
   apply(clarsimp)
  apply(rename_tac G dl n i e c ea ca f w ia nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
  apply(subgoal_tac "length (nat_seq i nat) = nat + 1 - i")
   apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
   prefer 2
   apply(rule nat_seq_length_prime)
  apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
  apply(rule_tac
      t="nat_seq i nat ! ia"
      and s="i+ia"
      in ssubst)
   apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
    apply(force)
   apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
   apply(force)
  apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dl (i+ia) = Some (pair e1 c1) \<and> dl (Suc(i+ia)) = Some (pair (Some e2) c2) \<and> parserHF_step_relation G c1 e2 c2")
   apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserHF.step_detail_before_some_position)
     apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
     apply(simp add: parserHF.derivation_initial_def)
    apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
    apply(force)
   apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
   apply(force)
  apply(rename_tac G dl i e c ea ca f w ia nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
  apply(rule_tac
      t="nat_seq i nat ! ia"
      and s="i+ia"
      in ssubst)
   apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
   apply(rule nat_seq_nth_compute)
    apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFvHFS_Bra2LinStep_def)
  apply(rule_tac
      d="dl"
      and i="i"
      and n="i+ia"
      and m="nat - i - ia"
      in parserHF_steps_are_empty2)
            apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
            apply(force)
           apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
           apply(simp add: parserHF.derivation_initial_def)
          apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
          apply(rule parserHF.derivation_initial_belongs)
           apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
           apply(force)
          apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
          apply(force)
         apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
         apply(force)
        apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac G dl i e c ea ca f w ia nat e1 e2 c1 c2)(*strict*)
  apply(force)
  done

lemma parserHF_vs_parserHFS_inst_AX_lin_unfixed_scheduler_right_quotient_drop_proper2: "
\<forall>G cL cB sE sL cL2.
       valid_parser G \<longrightarrow>
       cL \<in> parserHFS_configurations G \<longrightarrow>
       cB \<in> parserHF_configurations G \<longrightarrow>
       sE \<in> parser_scheduler_fragments G \<longrightarrow>
       parserHFvHFS_Bra2LinConf cB (sE @ sL) \<in> parserHFS_configurations G \<longrightarrow>
       (\<not> parser_fixed_scheduler_extendable G (parserHF_conf_fixed cB) \<longrightarrow>
        \<not> parser_fixed_scheduler_extendable G
            (parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL))) \<longrightarrow>
       sL =
       (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq>
           [parser_bottom G]
        then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL)
        else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @
             [parser_bottom G]) \<longrightarrow>
       cL2 = parserHFvHFS_Bra2LinConf cB (sE @ sL) \<longrightarrow>
       parserHFS_set_unfixed_scheduler cL2
        (the (right_quotient_word (parserHFS_get_unfixed_scheduler cL2)
               (parserHFS_get_unfixed_scheduler
                 (parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL)
                   sL))) @
         parserHFS_get_unfixed_scheduler cL) =
       parserHFvHFS_Bra2LinConf cB (sE @ parserHFS_get_scheduler cL)"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cL)(*strict*)
   apply(clarsimp)
   apply(rename_tac G cL cB sE)(*strict*)
   apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Lin2BraConf_def parserHFS_set_unfixed_scheduler_def)
   apply(rule_tac
      t="left_quotient_word (parserHFS_conf_fixed cL) (parserHFS_conf_fixed cL)"
      and s="Some []"
      in ssubst)
    apply(rename_tac G cL cB sE)(*strict*)
    apply(rule left_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac G cL cB sE)(*strict*)
   apply(clarsimp)
   apply(simp add: right_quotient_word_def)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G cB sE f h l w wa)(*strict*)
   apply(simp add: prefix_def suffix_def parserHFS_get_scheduler_def)
   apply(clarsimp)
   apply(rename_tac G cB sE l wa c ca cb cc "cd")(*strict*)
   apply(subgoal_tac "cc=[]")
    apply(rename_tac G cB sE l wa c ca cb cc "cd")(*strict*)
    apply(clarsimp)
    apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
    apply(rule_tac
      t="left_quotient_word (wa @ [parser_bottom G]) (wa @ [parser_bottom G])"
      and s="Some []"
      in ssubst)
     apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
     apply(rule left_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="left_quotient_word (parserHF_conf_fixed cB) (sE @ wa @ [parser_bottom G])"
      and s="Some ca"
      in ssubst)
     apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
     apply(rule left_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G cB sE l wa ca cb "cd")(*strict*)
    apply(clarsimp)
   apply(rename_tac G cB sE l wa c ca cb cc "cd")(*strict*)
   apply(case_tac cc)
    apply(rename_tac G cB sE l wa c ca cb cc "cd")(*strict*)
    apply(clarsimp)
   apply(rename_tac G cB sE l wa c ca cb cc "cd" a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cc = w' @ [x']")
    apply(rename_tac G cB sE l wa c ca cb cc "cd" a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G cB sE l wa c ca cb cc "cd" a list)(*strict*)
   apply(thin_tac "cc=a#list")
   apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(clarsimp)
  apply(rename_tac G cL cB sE)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFS_get_unfixed_scheduler_def parserHFvHFS_Lin2BraConf_def parserHFS_set_unfixed_scheduler_def parserHFS_get_scheduler_def)
  apply(rule_tac
      t="left_quotient_word (parserHFS_conf_fixed cL) (parserHFS_conf_fixed cL @ [parser_bottom G])"
      and s="Some [parser_bottom G]"
      in ssubst)
   apply(rename_tac G cL cB sE)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cL cB sE)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G cB sE f h l w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G cB sE f h l w c ca)(*strict*)
  apply(rule_tac
      t="left_quotient_word f (w @ [parser_bottom G])"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G cB sE f h l w c ca)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cB sE f h l w c ca)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="left_quotient_word (parserHF_conf_fixed cB) (sE @ f @ [parser_bottom G])"
      and s="Some c"
      in ssubst)
   apply(rename_tac G cB sE f h l w c ca)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cB sE f h l w c ca)(*strict*)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G cB sE f l w c ca cb cc)(*strict*)
  apply(case_tac ca)
   apply(rename_tac G cB sE f l w c ca cb cc)(*strict*)
   apply(force)
  apply(rename_tac G cB sE f l w c ca cb cc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac G cB sE f l w c ca cb cc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G cB sE f l w c ca cb cc a list)(*strict*)
  apply(thin_tac "ca=a#list")
  apply(clarsimp)
  apply(rename_tac G cB sE f l c cb cc w')(*strict*)
  apply(case_tac c)
   apply(rename_tac G cB sE f l c cb cc w')(*strict*)
   apply(force)
  apply(rename_tac G cB sE f l c cb cc w' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac G cB sE f l c cb cc w' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G cB sE f l c cb cc w' a list)(*strict*)
  apply(thin_tac "c=a#list")
  apply(clarsimp)
  apply(rename_tac G cB sE f l cb cc w' w'a)(*strict*)
  apply(rule_tac
      t="right_quotient_word (w'a @ [parser_bottom G]) [parser_bottom G]"
      and s="Some w'a"
      in ssubst)
   apply(rename_tac G cB sE f l cb cc w' w'a)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cB sE f l cb cc w' w'a)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinStep_Bra2LinFin_compatible: "
  \<forall>G cB1 e cB2.
       valid_parser G \<longrightarrow>
       parserHF_step_relation G cB1 e cB2 \<longrightarrow>
       cB1 \<in> parserHF_configurations G \<longrightarrow>
       \<not> parser_fixed_scheduler_extendable G (parserHF_conf_fixed cB1) \<longrightarrow>
       parserHFvHFS_Bra2LinStep cB1 e cB2 @
       (if parserHF_conf_fixed cB2 \<sqsupseteq> [parser_bottom G]
        then parserHF_conf_fixed cB2
        else parserHF_conf_fixed cB2 @ [parser_bottom G]) =
       (if parserHF_conf_fixed cB1 \<sqsupseteq> [parser_bottom G]
        then parserHF_conf_fixed cB1
        else parserHF_conf_fixed cB1 @ [parser_bottom G])"
  apply(rule allI)+
  apply(rename_tac G cB1 e cB2)(*strict*)
  apply(rule impI)+
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G cB1 e cB2)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(rename_tac G cB1 e cB2)(*strict*)
  apply(subgoal_tac "cB2 \<in> parserHF_configurations G")
   apply(rename_tac G cB1 e cB2)(*strict*)
   prefer 2
   apply (metis parserHF.AX_step_relation_preserves_belongs)
  apply(rename_tac G cB1 e cB2)(*strict*)
  apply(subgoal_tac "parserHF_conf_fixed cB2 \<sqsupseteq> [parser_bottom G]")
   apply(rename_tac G cB1 e cB2)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_step_relation_def parserHF_configurations_def valid_parser_step_label_def parserHFvHFS_Bra2LinStep_def)
   apply(clarsimp)
   apply(rename_tac G e f h k w xa xb)(*strict*)
   apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xb"
      in ssubst)
    apply(rename_tac G e f h k w xa xb)(*strict*)
    apply(rule right_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac G e f h k w xa xb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "prefix (xb @ rule_rpush e) f")
    apply(rename_tac G e f h k w xa xb)(*strict*)
    apply(simp add: prefix_def)
    apply(force)
   apply(rename_tac G e f h k w xa xb)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac G e k w xa xb c ca cb cc "cd")(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k - length w")
    apply(rename_tac G e k w xa xb c ca cb cc "cd")(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_bottom G \<in> set w")
     apply(rename_tac G e k w xa xb c ca cb cc "cd")(*strict*)
     apply (metis not_in_diff)
    apply(rename_tac G e k w xa xb c ca cb cc "cd")(*strict*)
    apply (metis kPrefix_def take_reflects_mem)
   apply(rename_tac G e k w xa xb c ca cb cc "cd" nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e k w xa xb c ca cb cc "cd" nat x)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(case_tac "cd")
    apply(rename_tac G e k w xa xb c ca cb cc "cd" nat x)(*strict*)
    apply(force)
   apply(rename_tac G e k w xa xb c ca cb cc "cd" nat x a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cd = w' @ [x']")
    apply(rename_tac G e k w xa xb c ca cb cc "cd" nat x a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e k w xa xb c ca cb cc "cd" nat x a list)(*strict*)
   apply(thin_tac "cd = a # list")
   apply(clarsimp)
  apply(rename_tac G cB1 e cB2)(*strict*)
  apply(subgoal_tac "\<not> parser_fixed_scheduler_extendable G (parserHF_conf_fixed cB2)")
   apply(rename_tac G cB1 e cB2)(*strict*)
   prefer 2
   apply (metis insert_Nil parserHF.AX_fixed_scheduler_extendable_translates_backwards)
  apply(rename_tac G cB1 e cB2)(*strict*)
  apply(simp add: parser_fixed_scheduler_extendable_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinConf_Lin2BraConf_on_unextendable_scheduler_fragments: "
  \<forall>G cL. valid_parser G \<longrightarrow> cL \<in> parserHFS_configurations G \<longrightarrow> \<not> parserHFS_get_unfixed_scheduler cL \<sqsupseteq> [parser_bottom G] \<longrightarrow> cL = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @ [parser_bottom G])"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cL)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFvHFS_Bra2LinConf_def)
   apply(case_tac cL)
   apply(rename_tac G cL parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
   apply(simp add: parserHFS_get_unfixed_scheduler_def)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack w)(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_stack w c ca)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_stack w c ca cb)(*strict*)
   apply(case_tac cb)
    apply(rename_tac G parserHFS_conf_stack w c ca cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac G parserHFS_conf_stack w c ca cb a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
    apply(rename_tac G parserHFS_conf_stack w c ca cb a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G parserHFS_conf_stack w c ca cb a list)(*strict*)
   apply(thin_tac "cb = a # list")
   apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFvHFS_Bra2LinConf_def parserHFS_get_unfixed_scheduler_def)
  apply(case_tac cL)
  apply(rename_tac G cL parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
  apply(simp add: parserHFS_configurations_def suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w)(*strict*)
  apply(case_tac c)
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w a list)(*strict*)
  apply(thin_tac "c = a # list")
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack ca w')(*strict*)
  apply(simp add: left_quotient_word_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_translate_proper_idemp_doulbe_transfer_on_head: "
  \<forall>G s cB2 cL1 e. valid_parser G \<longrightarrow> s \<in> parser_schedulers G \<longrightarrow> parserHFvHFS_Bra2LinConf cB2 s \<in> parserHFS_configurations G \<longrightarrow> cL1 \<in> parserHFS_configurations G \<longrightarrow> parserHFS_step_relation G cL1 e (parserHFvHFS_Bra2LinConf cB2 s) \<longrightarrow> cL1 = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL1) (parserHFvHFS_Bra2LinStep (parserHFvHFS_Lin2BraConf cL1) e cB2 @ s)"
  apply(clarsimp)
  apply(rename_tac G s cB2 cL1 e)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G s cB2 cL1 e)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHFS_step_relation_def)
  apply(rename_tac G s cB2 cL1 e)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFvHFS_Bra2LinStep_def parserHFvHFS_Lin2BraConf_def parserHFS_configurations_def parserHFS_step_relation_def valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G cB2 e f h k w xa xb y xc wb)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac G cB2 e f k w xa xb y xc wb c ca cb cc)(*strict*)
  apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xc"
      in ssubst)
   apply(rename_tac G cB2 e f k w xa xb y xc wb c ca cb cc)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cB2 e f k w xa xb y xc wb c ca cb cc)(*strict*)
  apply(clarsimp)
  apply (metis concat_asso)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinConf_Lin2BraConf_idemp_on_get_scheduler: "
  \<forall>G cL. valid_parser G \<longrightarrow> cL \<in> parserHFS_configurations G \<longrightarrow> cL = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) (parserHFS_get_scheduler cL)"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def parserHFS_get_scheduler_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinConf_Lin2BraConf_idemp_on_get_scheduler_prime: "
  (\<forall>G cL sL. valid_parser G \<longrightarrow> cL \<in> parserHFS_configurations G \<longrightarrow> sL \<in> parser_schedulers G \<longrightarrow> cL = parserHFvHFS_Bra2LinConf (parserHFvHFS_Lin2BraConf cL) sL \<longrightarrow> sL = parserHFS_get_scheduler cL)"
  apply(clarsimp)
  apply(rename_tac G cL sL)(*strict*)
  apply(simp add: parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def parserHFS_get_scheduler_def)
  apply(case_tac cL)
  apply(rename_tac G cL sL parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_proper_removal_of_scheduler_parts: "
  \<forall>G cL1 e cL2. valid_parser G \<longrightarrow> cL1 \<in> parserHFS_configurations G \<longrightarrow> parserHFS_step_relation G cL1 e cL2 \<longrightarrow> parserHFvHFS_Bra2LinStep (parserHFvHFS_Lin2BraConf cL1) e (parserHFvHFS_Lin2BraConf cL2) @ parserHFS_get_scheduler cL2 = parserHFS_get_scheduler cL1"
  apply(clarsimp)
  apply(rename_tac G cL1 e cL2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G cL1 e cL2)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHFS_step_relation_def)
  apply(rename_tac G cL1 e cL2)(*strict*)
  apply(simp add: valid_parser_step_label_def parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def parserHFS_get_scheduler_def parserHFvHFS_Bra2LinStep_def parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G cL1 e cL2 k w xa)(*strict*)
  apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xa"
      in ssubst)
   apply(rename_tac G cL1 e cL2 k w xa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G cL1 e cL2 k w xa)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinFin_takes_entire_fixed_scheduler: "
\<forall>G cL.
       valid_parser G \<longrightarrow>
       cL \<in> parserHFS_configurations G \<longrightarrow>
       \<not> parser_unfixed_scheduler_extendable G
           (parserHFS_get_unfixed_scheduler cL) \<longrightarrow>
       (if parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) \<sqsupseteq>
           [parser_bottom G]
        then parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL)
        else parserHF_conf_fixed (parserHFvHFS_Lin2BraConf cL) @
             [parser_bottom G]) =
       parserHFS_get_scheduler cL"
  apply(clarsimp)
  apply(rename_tac G cL)(*strict*)
  apply(rule conjI)
   apply(rename_tac G cL)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFvHFS_Bra2LinConf_def)
   apply(case_tac cL)
   apply(rename_tac G cL parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
   apply(simp add: parserHFS_get_unfixed_scheduler_def)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack w)(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_stack w c ca)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_stack w c ca cb)(*strict*)
   apply(rule_tac
      xs="cb"
      in rev_cases)
    apply(rename_tac G parserHFS_conf_stack w c ca cb)(*strict*)
    prefer 2
    apply(rename_tac G parserHFS_conf_stack w c ca cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac G parserHFS_conf_stack w c ca cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G parserHFS_conf_stack w ca)(*strict*)
   apply(simp add: parserHFS_get_scheduler_def)
  apply(rename_tac G cL)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFvHFS_Bra2LinConf_def parserHFS_get_unfixed_scheduler_def)
  apply(case_tac cL)
  apply(rename_tac G cL parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
  apply(simp add: parserHFS_configurations_def suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w)(*strict*)
  apply(case_tac c)
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack c ca w a list)(*strict*)
  apply(thin_tac "c = a # list")
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixed parserHFS_conf_stack ca w')(*strict*)
  apply(simp add: left_quotient_word_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_combine_consumed_and_remaining_scheduler: "
 \<forall>G s cL1 e cB2.
       valid_parser G \<longrightarrow>
       s \<in> parser_schedulers G \<longrightarrow>
       cL1 \<in> parserHFS_configurations G \<longrightarrow>
       parserHFS_step_relation G cL1 e (parserHFvHFS_Bra2LinConf cB2 s) \<longrightarrow>
       parserHFvHFS_Bra2LinStep (parserHFvHFS_Lin2BraConf cL1) e cB2 @ s =
       parserHFS_get_scheduler cL1"
  apply(clarsimp)
  apply(rename_tac G s cL1 e cL2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G s cL1 e cL2)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def parserHFS_step_relation_def)
  apply(rename_tac G s cL1 e cL2)(*strict*)
  apply(simp add: valid_parser_step_label_def parserHFvHFS_Bra2LinConf_def parserHFvHFS_Lin2BraConf_def parserHFS_get_scheduler_def parserHFvHFS_Bra2LinStep_def parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G s cL1 e cL2 k w xa)(*strict*)
  apply(rule_tac
      t="right_quotient_word (kPrefix k (w @ [parser_bottom G])) (rule_rpush e)"
      and s="Some xa"
      in ssubst)
   apply(rename_tac G cL1 e cL2 k w xa)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G s cL1 e cL2 k w xa)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G cL1 e cL2 k w xa x xb y)(*strict*)
  apply(rule_tac
      xs="xb"
      in rev_cases)
   apply(rename_tac G cL1 e cL2 k w xa x xb y)(*strict*)
   apply(clarsimp)
  apply(rename_tac G cL1 e cL2 k w xa x xb y ys ya)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_bra2lin_preserves_unmarked_effect: "
  \<forall>G db x n.
       valid_parser G \<longrightarrow>
       ATS.derivation_initial parserHF_initial_configurations
        parserHF_step_relation G db \<longrightarrow>
       x \<in> parserHF_unmarked_effect G db \<longrightarrow>
       maximum_of_domain db n \<longrightarrow>
       x \<in> parserHFS_unmarked_effect G
             (parserHF_vs_parserHFS.Bra2LinDer
               G db n)"
  apply(clarsimp)
  apply(rename_tac G db x n)(*strict*)
  apply(simp add: parserHF_unmarked_effect_def parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G db n i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(subgoal_tac "i\<le>n")
   apply(rename_tac G db n i e c)(*strict*)
   apply(subgoal_tac "\<exists>e c. db n = Some (pair e c)")
    apply(rename_tac G db n i e c)(*strict*)
    apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G db n i")
     apply(rename_tac G db n i e c)(*strict*)
     apply(clarsimp)
     apply(rename_tac G db n i e c ea ca)(*strict*)
     apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(rename_tac G db n i e c a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G db n i e c a ea ca)(*strict*)
    apply(case_tac a)
    apply(rename_tac G db n i e c a ea ca option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac G db n i e c ea ca option b)(*strict*)
    apply(subgoal_tac "parserHFS_conf_history (the (get_configuration (parserHF_vs_parserHFS.Bra2LinDer SSG SSd SSn SSi))) = parserHF_conf_history c" for SSG SSd SSn SSi)
     apply(rename_tac G db n i e c ea ca option b)(*strict*)
     prefer 2
     apply(rule_tac
      n="n"
      and d="db"
      in parserHF_vs_parserHFS.AX_Bra2LinConf_preserves_history_lift)
          apply(rename_tac G db n i e c ea ca option b)(*strict*)
          apply(force)
         apply(rename_tac G db n i e c ea ca option b)(*strict*)
         apply(simp add: parserHF.derivation_initial_def)
        apply(rename_tac G db n i e c ea ca option b)(*strict*)
        apply(rule parserHF.derivation_initial_belongs)
         apply(rename_tac G db n i e c ea ca option b)(*strict*)
         apply(force)
        apply(rename_tac G db n i e c ea ca option b)(*strict*)
        apply(force)
       apply(rename_tac G db n i e c ea ca option b)(*strict*)
       apply(force)
      apply(rename_tac G db n i e c ea ca option b)(*strict*)
      apply(force)
     apply(rename_tac G db n i e c ea ca option b)(*strict*)
     apply(force)
    apply(rename_tac G db n i e c ea ca option b)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac G db n i e c)(*strict*)
   apply(rule parserHF.some_position_has_details_before_max_dom)
     apply(rename_tac G db n i e c)(*strict*)
     apply(simp add: parserHF.derivation_initial_def)
     apply(force)
    apply(rename_tac G db n i e c)(*strict*)
    apply(force)
   apply(rename_tac G db n i e c)(*strict*)
   apply(force)
  apply(rename_tac G db n i e c)(*strict*)
  apply (metis not_None_eq parserHF.allPreMaxDomSome_prime parserHF.derivation_initial_is_derivation)
  done

lemma parserHF_vs_parserHFS_inst_AX_lin2bra_preserves_unmarked_effect: "
  \<forall>G dl x n. valid_parser G \<longrightarrow> parserHFS.derivation_initial G dl \<longrightarrow> x \<in> parserHFS_unmarked_effect G dl \<longrightarrow> maximum_of_domain dl n \<longrightarrow> x \<in> parserHF_unmarked_effect G (ATS_Branching_Versus_Linear1.Lin2BraDer parserHFvHFS_Lin2BraConf dl)"
  apply(clarsimp)
  apply(rename_tac G dl x xa)(*strict*)
  apply(simp add: parserHF_unmarked_effect_def parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G dl xa i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(case_tac "ATS_Branching_Versus_Linear1.Lin2BraDer parserHFvHFS_Lin2BraConf dl i")
   apply(rename_tac G dl xa i e c)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_vs_parserHFS.Lin2BraDer_def derivation_map_def)
  apply(rename_tac G dl xa i e c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G dl xa i e c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dl xa i e c option b)(*strict*)
  apply(subgoal_tac "parserHFS_conf_history c = parserHF_conf_history (parserHFvHFS_Lin2BraConf c)")
   apply(rename_tac G dl xa i e c option b)(*strict*)
   prefer 2
   apply(rule_tac
      d="dl"
      in parserHF_vs_parserHFS.AX_Lin2BraConf_preserves_history_lift)
      apply(rename_tac G dl xa i e c option b)(*strict*)
      apply(force)
     apply(rename_tac G dl xa i e c option b)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac G dl xa i e c option b)(*strict*)
    apply(rule parserHFS.derivation_initial_belongs)
     apply(rename_tac G dl xa i e c option b)(*strict*)
     apply(force)
    apply(rename_tac G dl xa i e c option b)(*strict*)
    apply(force)
   apply(rename_tac G dl xa i e c option b)(*strict*)
   apply(force)
  apply(rename_tac G dl xa i e c option b)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHF_vs_parserHFS.Lin2BraDer_def derivation_map_def)
  done

lemma parserHF_vs_parserHFS_inst_AX_lin2bra_preserves_marked_effect: "
  \<forall>G dl x n. valid_parser G \<longrightarrow> parserHFS.derivation_initial G dl \<longrightarrow> parserHFS_marking_condition G dl \<longrightarrow> x \<in> parserHFS_marked_effect G dl \<longrightarrow> maximum_of_domain dl n \<longrightarrow> x \<in> parserHF_marked_effect G (ATS_Branching_Versus_Linear1.Lin2BraDer parserHFvHFS_Lin2BraConf dl)"
  apply(clarsimp)
  apply(rename_tac G dl x xa)(*strict*)
  apply(simp add: parserHFS_marked_effect_def parserHF_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G dl xa i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(subgoal_tac "i\<le>xa")
   apply(rename_tac G dl xa i e c)(*strict*)
   apply(case_tac "ATS_Branching_Versus_Linear1.Lin2BraDer parserHFvHFS_Lin2BraConf dl i")
    apply(rename_tac G dl xa i e c)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Lin2BraDer_def derivation_map_def)
   apply(rename_tac G dl xa i e c a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac G dl xa i e c a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G dl xa i e c option b)(*strict*)
   apply(subgoal_tac "parserHFS_conf_history c = parserHF_conf_history (parserHFvHFS_Lin2BraConf c)")
    apply(rename_tac G dl xa i e c option b)(*strict*)
    prefer 2
    apply(rule parserHF_vs_parserHFS.AX_Lin2BraConf_preserves_history_lift)
       apply(rename_tac G dl xa i e c option b)(*strict*)
       apply(force)
      apply(rename_tac G dl xa i e c option b)(*strict*)
      apply(rule parserHFS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac G dl xa i e c option b)(*strict*)
     apply (metis parserHFS.derivation_initial_belongs)
    apply(rename_tac G dl xa i e c option b)(*strict*)
    apply(force)
   apply(rename_tac G dl xa i e c option b)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G dl xa i e c option b)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Lin2BraDer_def derivation_map_def)
   apply(rename_tac G dl xa i e c option b)(*strict*)
   apply(simp add: parserHF_marking_configurations_def parserHFS_marking_configurations_def)
   apply(clarsimp)
   apply(rename_tac G dl xa i e c option b f w)(*strict*)
   apply(rule conjI)
    apply(rename_tac G dl xa i e c option b f w)(*strict*)
    apply(rule_tac
      x="f"
      in bexI)
     apply(rename_tac G dl xa i e c option b f w)(*strict*)
     apply(rule_tac
      x="w"
      in exI)
     apply(simp add: parserHF_vs_parserHFS.Lin2BraDer_def derivation_map_def)
     apply(simp add: parserHFvHFS_Lin2BraConf_def)
     apply(clarsimp)
     apply(rename_tac G dl xa i c option b f w)(*strict*)
     apply(case_tac b)
     apply(rename_tac G dl xa i c option b f w parserHF_conf_fixed parserHF_conf_historya parserHF_conf_stacka)(*strict*)
     apply(clarsimp)
    apply(rename_tac G dl xa i e c option b f w)(*strict*)
    apply(force)
   apply(rename_tac G dl xa i e c option b f w)(*strict*)
   apply(rule conjI)
    apply(rename_tac G dl xa i e c option b f w)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Lin2BraDer_def derivation_map_def)
    apply(clarsimp)
    apply(rename_tac G dl xa i c option f w)(*strict*)
    apply(simp add: parserHFvHFS_Lin2BraConf_def)
    apply(simp add: parserHFS_configurations_def)
    apply(clarsimp)
    apply(rename_tac G dl xa i option f w fa h)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G dl xa i option f w fa h c)(*strict*)
    apply(case_tac c)
     apply(rename_tac G dl xa i option f w fa h c)(*strict*)
     apply(clarsimp)
    apply(rename_tac G dl xa i option f w fa h c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac G dl xa i option f w fa h a list)(*strict*)
    apply(subgoal_tac "fa=[]")
     apply(rename_tac G dl xa i option f w fa h a list)(*strict*)
     apply(subgoal_tac "list=[]")
      apply(rename_tac G dl xa i option f w fa h a list)(*strict*)
      apply(force)
     apply(rename_tac G dl xa i option f w fa h a list)(*strict*)
     apply(force)
    apply(rename_tac G dl xa i option f w fa h a list)(*strict*)
    apply (metis Cons_eq_appendI eq_Nil_appendI insert_Nil length_1_context_empty)
   apply(rename_tac G dl xa i e c option b f w)(*strict*)
   prefer 2
   apply(rename_tac G dl xa i e c)(*strict*)
   apply (metis not_Some_eq parserHFS.allPreMaxDomSome_prime parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G dl xa i e c option b f w)(*strict*)
  apply(simp add: parserHF_vs_parserHFS.Lin2BraDer_def derivation_map_def)
  apply(clarsimp)
  apply(rename_tac G dl xa i c option f w)(*strict*)
  apply(simp add: parserHFvHFS_Lin2BraConf_def)
  apply(simp add: parserHF_configurations_def parserHFS_configurations_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G dl xa i option f w fa h ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G dl xa i option f w fa h ca)(*strict*)
   apply (metis set_append1 set_subset_in2 subset_trans)
  apply(rename_tac G dl xa i option f w fa h ca)(*strict*)
  apply(clarsimp)
  apply(case_tac ca)
   apply(rename_tac G dl xa i option f w fa h ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac G dl xa i option f w fa h ca a list)(*strict*)
  apply(subgoal_tac "fa=[]")
   apply(rename_tac G dl xa i option f w fa h ca a list)(*strict*)
   apply(subgoal_tac "list=[]")
    apply(rename_tac G dl xa i option f w fa h ca a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dl xa i option f w fa h ca a list)(*strict*)
   apply(force)
  apply(rename_tac G dl xa i option f w fa h ca a list)(*strict*)
  apply (metis List.butlast_append Nil_is_append_conv butlast.simps(2) list.simps(2))
  done

lemma parserHF_vs_parserHFS_inst_AX_bra2lin_preserves_marked_effect: "
  \<forall>G db x n. valid_parser G \<longrightarrow> parserHF.derivation_initial G db \<longrightarrow> parserHF_marking_condition G db \<longrightarrow> x \<in> parserHF_marked_effect G db \<longrightarrow> maximum_of_domain db n \<longrightarrow> (\<exists>i\<le>n. parserHF_marking_condition G (derivation_take db i) \<and> x \<in> parserHFS_marked_effect G (parserHF_vs_parserHFS.Bra2LinDer G (derivation_take db i) i))"
  apply(clarsimp)
  apply(rename_tac G db x n)(*strict*)
  apply(simp add: parserHFS_marked_effect_def parserHF_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G db n i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G db n i e c)(*strict*)
   apply (metis not_Some_eq parserHF.allPreMaxDomSome_prime parserHF.derivation_initial_is_derivation)
  apply(rename_tac G db n i e c)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G db n i e c)(*strict*)
   apply(simp add: parserHF_marking_condition_def)
   apply(clarsimp)
   apply(rename_tac G db n i e c ia ea ca)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G db n i e c ia ea ca)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G db n i e c ia ea ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G db n i e c ia ea ca j e' c')(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G db n i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(simp add: parserHF_marking_configurations_def)
  apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_take db i) i i")
   apply(rename_tac G db n i e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G db n i e c f w)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def derivation_take_def)
  apply(rename_tac G db n i e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G db n i e c a f w)(*strict*)
  apply(case_tac a)
  apply(rename_tac G db n i e c a f w option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G db n i e c f w option b)(*strict*)
  apply(subgoal_tac "parserHFS_conf_history (the (get_configuration (parserHF_vs_parserHFS.Bra2LinDer SSG SSd SSn SSi))) = parserHF_conf_history c" for SSG SSd SSn SSi)
   apply(rename_tac G db n i e c f w option b)(*strict*)
   prefer 2
   apply(rule_tac
      i="i"
      and n="i"
      and d="derivation_take db i"
      in parserHF_vs_parserHFS.AX_Bra2LinConf_preserves_history_lift)
        apply(rename_tac G db n i e c f w option b)(*strict*)
        apply(force)
       apply(rename_tac G db n i e c f w option b)(*strict*)
       apply(rule parserHF.derivation_take_preserves_derivation)
       apply(rule parserHF.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G db n i e c f w option b)(*strict*)
      apply(rule parserHF.derivation_initial_belongs)
       apply(rename_tac G db n i e c f w option b)(*strict*)
       apply(force)
      apply(rename_tac G db n i e c f w option b)(*strict*)
      apply(rule parserHF.derivation_take_preserves_derivation_initial)
      apply(force)
     apply(rename_tac G db n i e c f w option b)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac G db n i e c f w option b)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G db n i e c f w option b)(*strict*)
   apply(force)
  apply(rename_tac G db n i e c f w option b)(*strict*)
  apply(rule conjI)
   apply(rename_tac G db n i e c f w option b)(*strict*)
   apply(simp add: get_configuration_def ATS_Branching_Versus_Linear1.Bra2LinDer_def)
  apply(rename_tac G db n i e c f w option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: parserHFS_marking_configurations_def)
  apply(rule conjI)
   apply(rename_tac G db n i e c f w option b)(*strict*)
   apply(rule_tac
      x="f"
      in bexI)
    apply(rename_tac G db n i e c f w option b)(*strict*)
    apply(rule_tac
      x="w"
      in exI)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def derivation_take_def parserHFvHFS_Bra2LinConf_def)
    apply(case_tac b)
    apply(rename_tac G db n i e c f w option b parserHFS_conf_fixed parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduler)(*strict*)
    apply(clarsimp)
   apply(rename_tac G db n i e c f w option b)(*strict*)
   apply(force)
  apply(rename_tac G db n i e c f w option b)(*strict*)
  apply(rule conjI)
   apply(rename_tac G db n i e c f w option b)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def derivation_take_def parserHFvHFS_Bra2LinConf_def parserHF_vs_parserHFS.Bra2LinDer'_def)
   apply(case_tac b)
   apply(rename_tac G db n i e c f w option b parserHFS_conf_fixed parserHFS_conf_historya parserHFS_conf_stack parserHFS_conf_schedulera)(*strict*)
   apply(clarsimp)
   apply(rename_tac G db n i c f w option)(*strict*)
   apply(subgoal_tac "case_nat [] (nat_seq i) i=[]")
    apply(rename_tac G db n i c f w option)(*strict*)
    apply(clarsimp)
    apply(erule disjE)
     apply(rename_tac G db n i c f w option)(*strict*)
     apply(clarsimp)
     apply(simp add: suffix_def)
    apply(rename_tac G db n i c f w option)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def)
   apply(rename_tac G db n i c f w option)(*strict*)
   apply(case_tac i)
    apply(rename_tac G db n i c f w option)(*strict*)
    apply(clarsimp)
   apply(rename_tac G db n i c f w option nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G db n c f w option nat)(*strict*)
   apply (metis lessI nat_seqEmpty)
  apply(rename_tac G db n i e c f w option b)(*strict*)
  apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def derivation_take_def parserHFvHFS_Bra2LinConf_def parserHF_vs_parserHFS.Bra2LinDer'_def)
  apply(case_tac b)
  apply(rename_tac G db n i e c f w option b parserHFS_conf_fixed parserHFS_conf_historya parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
  apply(clarsimp)
  apply(rename_tac G db n i c f w option)(*strict*)
  apply(subgoal_tac "case_nat [] (nat_seq i) i=[]")
   apply(rename_tac G db n i c f w option)(*strict*)
   prefer 2
   apply(case_tac i)
    apply(rename_tac G db n i c f w option)(*strict*)
    apply(clarsimp)
   apply(rename_tac G db n i c f w option nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G db n c f w option nat)(*strict*)
   apply (metis lessI nat_seqEmpty)
  apply(rename_tac G db n i c f w option)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac G db n i c f w option)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
   apply(simp add: parserHFS_configurations_def parserHF_configurations_def)
   apply(clarsimp)
   apply(rename_tac G db n i f w option h)(*strict*)
   apply(simp add: prefix_def)
   apply(simp add: valid_parser_def)
  apply(rename_tac G db n i c f w option)(*strict*)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(simp add: parserHFS_configurations_def parserHF_configurations_def)
  apply(clarsimp)
  apply(rename_tac G db n i f w option h)(*strict*)
  apply(simp add: prefix_def)
  done

lemma three_cases_strict_prefix: "
  prefix a x
  \<Longrightarrow> prefix b x
  \<Longrightarrow> a=b \<or> strict_prefix a b \<or> strict_prefix b a"
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(subgoal_tac "prefix a b \<or> prefix b a")
   apply(rename_tac c ca)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(rule sym)
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(erule disjE)
   apply(simp add: prefix_def strict_prefix_def)
   apply(force)
  apply(simp add: prefix_def strict_prefix_def)
  apply(force)
  done

lemma set_butlast_if_match_subset: "
  set w \<subseteq> A
  \<Longrightarrow> set(butlast_if_match w X) \<subseteq> A"
  apply(rule_tac
      xs="w"
      in rev_cases)
   apply(simp add: butlast_if_match_def)
  apply(rename_tac ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ys y x)(*strict*)
  apply(simp add: butlast_if_match_def)
  apply(case_tac "y=X")
   apply(rename_tac ys y x)(*strict*)
   apply(clarsimp)
   apply(rename_tac ys x uu_ uua_)(*strict*)
   apply(force)
  apply(rename_tac ys y x)(*strict*)
  apply(force)
  done

lemma parserHFS_post_history_prefix_of_pre_history_and_remaining_rhs: "
         valid_parser G \<Longrightarrow>
       parserHFS_step_relation G cL e1 cL1 \<Longrightarrow>
       valid_parser_step_label G e1 \<Longrightarrow>
       cL \<in> parserHFS_configurations G \<Longrightarrow>
       parserHFS_conf_history cL1 \<sqsubseteq>
       parserHFS_conf_history cL @
       drop (length (parserHFS_conf_fixed cL)) (parserHFS_conf_scheduler cL)"
  apply(simp add: parserHFS_step_relation_def parserHFvHFS_Lin2BraConf_def Let_def)
  apply(clarsimp)
  apply(rename_tac x xa y)(*strict*)
  apply(case_tac cL)
  apply(rename_tac x xa y parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(case_tac cL1)
  apply(rename_tac x xa y parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historyaa parserHFS_conf_stackaa parserHFS_conf_scheduleraa)(*strict*)
  apply(case_tac e1)
  apply(rename_tac x xa y parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historyaa parserHFS_conf_stackaa parserHFS_conf_scheduleraa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa y parserHFS_conf_fixed parserHFS_conf_history rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
  apply(simp add: prefix_def)
  apply(rule_tac xs="rule_rpop" in rev_cases)
   apply(rename_tac x xa y parserHFS_conf_fixed parserHFS_conf_history rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa y parserHFS_conf_fixed parserHFS_conf_history rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(simp add: butlast_if_match_def)
  apply(rename_tac x xa y parserHFS_conf_fixed parserHFS_conf_history rule_lpop rule_rpop rule_lpush rule_rpush ys ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa y parserHFS_conf_fixed parserHFS_conf_history rule_lpop rule_lpush rule_rpush ys ya)(*strict*)
  apply(simp add: parserHFS_configurations_def valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x xa y parserHFS_conf_fixed parserHFS_conf_history rule_lpop rule_lpush rule_rpush ys ya k w xc wa)(*strict*)
  apply(thin_tac "parserHFS_conf_history \<sqsupseteq>
       butlast_if_match parserHFS_conf_fixed (parser_bottom G)")
  apply(thin_tac "\<lparr>rule_lpop = rule_lpop, rule_rpop = kPrefix k (w @ [parser_bottom G]),
          rule_lpush = rule_lpush, rule_rpush = rule_rpush\<rparr>
       \<in> parser_rules G")
  apply(rename_tac f h XXXXXXXXXXX YYYYYYYY rpu ys ya k w xc wa)
  apply(rename_tac x xa y f h XXXXXXXXXXX YYYYYYYY rpu ys ya k w xc wa)(*strict*)
  apply(thin_tac "set XXXXXXXXXXX \<subseteq> parser_nonterms G" for XXXXXXXXXXX)
  apply(thin_tac "set XXXXXXXXXXX \<subseteq> parser_nonterms G" for XXXXXXXXXXX)
  apply(thin_tac "set XXXXXXXXXXX \<subseteq> parser_nonterms G" for XXXXXXXXXXX)
  apply(thin_tac "XXXXXXXXXXX \<noteq> []" for XXXXXXXXXXX)
  apply(thin_tac "XXXXXXXXXXX \<noteq> []" for XXXXXXXXXXX)
  apply(clarsimp)
  apply(rename_tac xa y f h rpu ys ya k w xc wa)(*strict*)
  apply(simp add: prefix_def kPrefix_def)
  apply(clarsimp)
  apply(rename_tac xa y f h rpu ys ya k w xc wa c)(*strict*)
  apply(case_tac "k-length w")
   apply(rename_tac xa y f h rpu ys ya k w xc wa c)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "min (length w) k=k")
    apply(rename_tac xa y f h rpu ys ya k w xc wa c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa y f h rpu ys ya k w xc wa c)(*strict*)
   apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
    apply(rename_tac xa y f h rpu ys ya k w xc wa c)(*strict*)
    prefer 2
    apply (metis butlast_if_match_reduces in_set_conv_decomp in_set_takeD nset_diff)
   apply(rename_tac xa y f h rpu ys ya k w xc wa c)(*strict*)
   apply(clarsimp)
   apply(rule_tac xs="xa" in rev_cases)
    apply(rename_tac xa y f h rpu ys ya k w xc wa c)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa y f h rpu ys ya k w xc wa c ysa yb)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h rpu ys ya k w xc c ysa)(*strict*)
   apply(rule_tac xs="c" in rev_cases)
    apply(rename_tac f h rpu ys ya k w xc c ysa)(*strict*)
    apply(clarsimp)
    apply(rename_tac h rpu ys ya k w xc ysa)(*strict*)
    apply (metis ConsApp List.length_take add_Suc_right append_assoc drop_length_append length_append list.size(4) monoid_add_class.add.right_neutral)
   apply(rename_tac f h rpu ys ya k w xc c ysa ysb y)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h rpu ys ya k w xc ysa ysb)(*strict*)
   apply(rule_tac t="take k w" and s="ys @ [ya]" in ssubst)
    apply(rename_tac f h rpu ys ya k w xc ysa ysb)(*strict*)
    apply(force)
   apply(rename_tac f h rpu ys ya k w xc ysa ysb)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac xa y f h rpu ys ya k w xc wa c nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa y f h k xc wa c nat x)(*strict*)
  apply(subgoal_tac "butlast_if_match ((xc @ x) @ [parser_bottom G])
              (parser_bottom G) = xc@x")
   apply(rename_tac xa y f h k xc wa c nat x)(*strict*)
   prefer 2
   apply (metis append_assoc butlast_if_match_direct)
  apply(rename_tac xa y f h k xc wa c nat x)(*strict*)
  apply(clarsimp)
  done

lemma elem_in_append_set: "
  w@ A # v = r @ s
  \<Longrightarrow> A \<notin> set r
  \<Longrightarrow> A \<notin> set s
  \<Longrightarrow> Q"
  apply (metis in_set_conv_decomp not_set_append)
  done

lemma parser_bottom_take_end: "
  ysa @ [A] = take ka wa
  \<Longrightarrow> set wa \<subseteq> X - {A}
  \<Longrightarrow> Q"
  apply(subgoal_tac "A \<in> set wa")
   apply(force)
  apply(rule_tac A="set (take ka wa)" in set_mp)
   apply(rule set_take_subset2)
   apply(force)
  apply(rule_tac A="set (ysa @ [A])" in set_mp)
   apply(force)
  apply(simp (no_asm))
  done

lemma parserHFS_step_precise_history: "
       parserHFS_step_relation G cL e1 cL1 \<Longrightarrow>
       parserHFS_conf_history cL1 =
       parserHFS_conf_history cL @
       drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e1) (parser_bottom G))"
  apply(simp add: parserHFS_step_relation_def parserHFvHFS_Lin2BraConf_def Let_def)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB_hlp: "
  prefix w1 w2 \<and> P1
  \<or> prefix w2 w1 \<and> P2
  \<or> w1=w2
  \<Longrightarrow> w2 \<in> parser_markers G
  \<Longrightarrow> w1 \<in> parser_markers G
  \<Longrightarrow> ATS_History.history_fragment_prefixes parser_markers (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<and> P1 \<or> ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w1 \<and> P2 \<or> ATS_History.history_fragment_prefixes parser_markers (@) G w1 = ATS_History.history_fragment_prefixes parser_markers (@) G w2"
  apply(erule disjE)
   apply(rule disjI1)
   apply(rule conjI)
    prefer 2
    apply(clarsimp)
   apply(rule_tac t="ATS_History.history_fragment_prefixes parser_markers (@) G w1" and s="prefix_closure {w1}" in ssubst)
    apply(simp add: parserHFS.history_fragment_prefixes_def)
    apply(rule antisym)
     apply(clarsimp)
     apply(rename_tac x hf'')(*strict*)
     apply(simp add: prefix_closure_def prefix_def)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac x c ca)(*strict*)
    apply(simp add: parser_markers_def)
   apply(rule_tac t="ATS_History.history_fragment_prefixes parser_markers (@) G w2" and s="prefix_closure {w2}" in ssubst)
    apply(simp add: parserHFS.history_fragment_prefixes_def)
    apply(rule antisym)
     apply(clarsimp)
     apply(rename_tac x hf'')(*strict*)
     apply(simp add: prefix_closure_def prefix_def)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac x c ca)(*strict*)
    apply(simp add: parser_markers_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(force)
  apply(erule disjE)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(rule conjI)
    prefer 2
    apply(clarsimp)
   apply(rule_tac t="ATS_History.history_fragment_prefixes parser_markers (@) G w1" and s="prefix_closure {w1}" in ssubst)
    apply(simp add: parserHFS.history_fragment_prefixes_def)
    apply(rule antisym)
     apply(clarsimp)
     apply(rename_tac x hf'')(*strict*)
     apply(simp add: prefix_closure_def prefix_def)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac x c ca)(*strict*)
    apply(simp add: parser_markers_def)
   apply(rule_tac t="ATS_History.history_fragment_prefixes parser_markers (@) G w2" and s="prefix_closure {w2}" in ssubst)
    apply(simp add: parserHFS.history_fragment_prefixes_def)
    apply(rule antisym)
     apply(clarsimp)
     apply(rename_tac x hf'')(*strict*)
     apply(simp add: prefix_closure_def prefix_def)
    apply(simp add: prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac x c ca)(*strict*)
    apply(simp add: parser_markers_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_closure_def prefix_def)
   apply(force)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(rule_tac t="ATS_History.history_fragment_prefixes parser_markers (@) G w1" and s="prefix_closure {w1}" in ssubst)
   apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(rule antisym)
    apply(clarsimp)
    apply(rename_tac x hf'')(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(simp add: parser_markers_def)
  apply(rule_tac t="ATS_History.history_fragment_prefixes parser_markers (@) G w2" and s="prefix_closure {w2}" in ssubst)
   apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(rule antisym)
    apply(clarsimp)
    apply(rename_tac x hf'')(*strict*)
    apply(simp add: prefix_closure_def prefix_def)
   apply(simp add: prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x c)(*strict*)
   apply(simp add: parser_markers_def)
  apply(clarsimp)
  done

lemma prefix_alt_apply: "
  w1@w2=v1@v2
  \<Longrightarrow> (prefix w1 v1 \<Longrightarrow> P)
  \<Longrightarrow> (prefix v1 w1 \<Longrightarrow> P)
  \<Longrightarrow> P"
  apply (metis mutual_strict_prefix_prefix strict_prefix_to_prefix)
  done

lemma tail_empty: "
  k\<le>length c
  \<Longrightarrow> c@x = take k w
  \<Longrightarrow> x = []"
  apply (metis List.length_take append_eq_conv_conj append_self_conv take_all_length take_take)
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB_hlp2: "
  x = cc @ drop (length cc) x @ c
  \<Longrightarrow> c \<noteq> []
  \<Longrightarrow> False"
  apply(subgoal_tac "length (cc @ drop (length cc) x @ c) = length x + length c")
   apply(force)
  apply(subgoal_tac "length (cc @ drop (length cc) x @ c) = length (cc @ drop (length cc) x)+length c")
   prefer 2
   apply(simp (no_asm))
  apply(subgoal_tac "length (cc @ drop (length cc) x) = length x")
   prefer 2
   apply(force)
  apply(simp (no_asm_use))
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB_hlp3: "
       valid_parser G \<Longrightarrow>
       parserHFS_step_relation G cL e1 cL1 \<Longrightarrow>
       parserHFS_step_relation G cL e2 cL2 \<Longrightarrow>
       valid_parser_step_label G e1 \<Longrightarrow>
       valid_parser_step_label G e2 \<Longrightarrow>
       cL \<in> parserHFS_configurations G \<Longrightarrow>
       drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e1) (parser_bottom G))
       \<in> parser_markers G \<and>
       drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e2) (parser_bottom G))
       \<in> parser_markers G \<Longrightarrow>
       parserHFS_conf_history cL1 \<sqsubset> parserHFS_conf_history cL2 \<Longrightarrow>
       ATS_determHIST_SB.compatible_history_fragment_SB parser_markers (@)
        (@) parserHF_conf_history parser_fixed_scheduler_extendable
        parserHF_conf_fixed G (parserHFvHFS_Lin2BraConf cL)
        (parserHFvHFS_Lin2BraConf cL1) (parserHFvHFS_Lin2BraConf cL2)"
  apply(simp add: parserHF.compatible_history_fragment_SB_def)
  apply(rule_tac x="drop (length (parserHFS_conf_fixed cL))
         (butlast_if_match (rule_rpop e1) (parser_bottom G))" in exI)
  apply(rule conjI)
   apply(clarsimp)
  apply(rule_tac x="drop (length (parserHFS_conf_fixed cL))
         (butlast_if_match (rule_rpop e2) (parser_bottom G))" in exI)
  apply(rule conjI)
   apply(clarsimp)
  apply(simp add: Let_def)
  apply(rule context_conjI)
   apply(simp add: parserHFvHFS_Lin2BraConf_def)
   apply(rule parserHFS_step_precise_history)
   apply(force)
  apply(rule context_conjI)
   apply(simp add: parserHFvHFS_Lin2BraConf_def)
   apply(rule parserHFS_step_precise_history)
   apply(force)
  apply(rule parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB_hlp)
    prefer 2
    apply(force)
   prefer 2
   apply(force)
  apply(rule disjI1)
  apply(rule conjI)
   apply(simp add: strict_prefix_def prefix_def)
   apply(thin_tac "drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e1) (parser_bottom G))
       \<in> parser_markers G \<and>
       drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e2) (parser_bottom G))
       \<in> parser_markers G")
   apply(clarsimp)
   apply(rename_tac c)(*strict*)
   apply(simp add: parserHFS_configurations_def valid_parser_step_label_def parserHFS_step_relation_def parserHFvHFS_Lin2BraConf_def)
   apply(clarsimp)
   apply(rename_tac c f h k w ka wa xb xc xd xe y ya xf xg wb)(*strict*)
   apply(rule_tac x="c" in exI)
   apply(force)
  apply(thin_tac "drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e1) (parser_bottom G))
       \<in> parser_markers G \<and>
       drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e2) (parser_bottom G))
       \<in> parser_markers G")
  apply(simp add: parserHFS_configurations_def valid_parser_step_label_def parserHFS_step_relation_def parserHFvHFS_Lin2BraConf_def)
  apply(clarsimp)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb)(*strict*)
  apply(thin_tac "e1 \<in> parser_rules G" for e1)
  apply(thin_tac "e1 \<in> parser_rules G" for e1)
  apply(thin_tac "set xd \<subseteq> parser_nonterms G" for xd)
  apply(thin_tac "set xd \<subseteq> parser_nonterms G" for xd)
  apply(thin_tac "set xd \<subseteq> parser_nonterms G" for xd)
  apply(thin_tac "set xd \<subseteq> parser_nonterms G" for xd)
  apply(thin_tac "set xd \<subseteq> parser_nonterms G" for xd)
  apply(thin_tac "rule_lpop e1 \<noteq> []")
  apply(thin_tac "rule_lpop e2 \<noteq> []")
  apply(thin_tac "rule_lpush e1 \<noteq> []")
  apply(thin_tac "rule_lpush e2 \<noteq> []")
  apply(thin_tac "parserHFS_conf_stack cL1 = xb @ rule_lpush e1")
  apply(thin_tac "parserHFS_conf_stack cL2 = xd @ rule_lpush e2")
  apply(thin_tac "xb @ rule_lpop e1 = xd @ rule_lpop e2")
  apply(case_tac cL1)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stack parserHFS_conf_schedulera)(*strict*)
  apply(rename_tac f1 h1 l1 r1)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb f1 h1 l1 r1)(*strict*)
  apply(case_tac cL2)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb f1 h1 l1 r1 parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stack parserHFS_conf_schedulera)(*strict*)
  apply(rename_tac f2 h2 cons_l2 r2)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb f1 h1 l1 r1 f2 h2 cons_l2 r2)(*strict*)
  apply(case_tac e1)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb f1 h1 l1 r1 f2 h2 cons_l2 r2 rule_lpop rule_rpopa rule_lpush rule_rpusha)(*strict*)
  apply(rename_tac lpo1 rpo1 lpu1 rpu1)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb f1 h1 l1 r1 f2 h2 cons_l2 r2 lpo1 rpo1 lpu1 rpu1)(*strict*)
  apply(case_tac e2)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb f1 h1 l1 r1 f2 h2 cons_l2 r2 lpo1 rpo1 lpu1 rpu1 rule_lpop rule_rpopa rule_lpush rule_rpusha)(*strict*)
  apply(rename_tac lpo2 rpo2 lpu2 rpu2)
  apply(rename_tac f h k w ka wa xb xc xd xe y ya xf xg wb f1 h1 l1 r1 f2 h2 cons_l2 r2 lpo1 rpo1 lpu1 rpu1 lpo2 rpo2 lpu2 rpu2)(*strict*)
  apply(clarsimp)
  apply(simp add: strict_prefix_def prefix_def kPrefix_def)
  apply(clarsimp)
  apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca)(*strict*)
  apply(case_tac "k-length w")
   apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "min (length w) k=k")
    apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
    apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca)(*strict*)
    prefer 2
    apply (metis butlast_if_match_reduces parser_bottom_take_end)
   apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac xs="drop k f" in rev_cases)
    apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu2 c ca cb cc)(*strict*)
    apply(rule_tac w="xf @ cc" and v="[]" and r="take k w" and s="[]" and A="parser_bottom G" in elem_in_append_set)
      apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu2 c ca cb cc)(*strict*)
      apply(force)
     apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu2 c ca cb cc)(*strict*)
     apply (metis in_set_takeD nset_diff)
    apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu2 c ca cb cc)(*strict*)
    apply(force)
   apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca ys yb)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca ys cb)(*strict*)
   apply(case_tac "ka-length wa")
    apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca ys cb)(*strict*)
    apply(subgoal_tac "min (length wa) ka = ka")
     apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca ys cb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca ys cb)(*strict*)
    apply(clarsimp)
    apply(rule_tac xs="xe" in rev_cases)
     apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca ys cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac f k w ka wa xc y ya xf xg wb rpu1 c ca ys cb)(*strict*)
     apply(rule_tac w="xg @ ya" and v="[]" and r="take ka wa" and s="[]" and A="parser_bottom G" in elem_in_append_set)
       apply(rename_tac f k w ka wa xc y ya xf xg wb rpu1 c ca ys cb)(*strict*)
       apply(force)
      apply(rename_tac f k w ka wa xc y ya xf xg wb rpu1 c ca ys cb)(*strict*)
      apply (metis in_set_takeD nset_diff)
     apply(rename_tac f k w ka wa xc y ya xf xg wb rpu1 c ca ys cb)(*strict*)
     apply(force)
    apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca ys cb ysa yb)(*strict*)
    apply(clarsimp)
    apply(rename_tac f k w ka wa xc y xf xg rpu1 rpu2 c ca ys cb ysa)(*strict*)
    apply(rule_tac xs="xc" in rev_cases)
     apply(rename_tac f k w ka wa xc y xf xg rpu1 rpu2 c ca ys cb ysa)(*strict*)
     apply(clarsimp)
     apply(rename_tac f k w ka wa y xf xg rpu2 c ca ys cb ysa)(*strict*)
     apply(rule_tac w="take ka wa @ ysa" and v="[]" and r="take k w" and s="[]" and A="parser_bottom G" in elem_in_append_set)
       apply(rename_tac f k w ka wa y xf xg rpu2 c ca ys cb ysa)(*strict*)
       apply(force)
      apply(rename_tac f k w ka wa y xf xg rpu2 c ca ys cb ysa)(*strict*)
      apply (metis in_set_takeD nset_diff)
     apply(rename_tac f k w ka wa y xf xg rpu2 c ca ys cb ysa)(*strict*)
     apply(force)
    apply(rename_tac f k w ka wa xc y xf xg rpu1 rpu2 c ca ys cb ysa ysb ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac f k w ka wa xf xg rpu1 rpu2 c ca ys cb ysa ysb)(*strict*)
    apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take k w) \<longrightarrow>
       (\<exists>x. x @ [parser_bottom G] = rpu1)")
    apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take ka wa) \<longrightarrow>
       (\<exists>x. x @ [parser_bottom G] = rpu2)")
    apply(subgoal_tac "butlast_if_match (take ka wa) (parser_bottom G) = take ka wa")
     apply(rename_tac f k w ka wa xf xg rpu1 rpu2 c ca ys cb ysa ysb)(*strict*)
     prefer 2
     apply (metis butlast_if_match_reduces parser_bottom_take_end)
    apply(rename_tac f k w ka wa xf xg rpu1 rpu2 c ca ys cb ysa ysb)(*strict*)
    apply(clarsimp)
    apply(rule_tac xs="f" in rev_cases)
     apply(rename_tac f k w ka wa xf xg rpu1 rpu2 c ca ys cb ysa ysb)(*strict*)
     apply(clarsimp)
    apply(rename_tac f k w ka wa xf xg rpu1 rpu2 c ca ys cb ysa ysb ysc y)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w ka wa xf xg rpu1 rpu2 c ca ys cb ysa ysb ysc y)(*strict*)
    apply(case_tac "k - length ysc")
     apply(rename_tac k w ka wa xf xg rpu1 rpu2 c ca ys cb ysa ysb ysc y)(*strict*)
     apply(clarsimp)
     apply(rename_tac k w ka wa xf xg rpu1 rpu2 ca cb ysa ysb ysc)(*strict*)
     apply(rule_tac xs="ca" in rev_cases)
      apply(rename_tac k w ka wa xf xg rpu1 rpu2 ca cb ysa ysb ysc)(*strict*)
      apply(clarsimp)
     apply(rename_tac k w ka wa xf xg rpu1 rpu2 ca cb ysa ysb ysc ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac k w ka wa xf xg rpu1 rpu2 cb ysa ysb ysc ys)(*strict*)
     apply(rule_tac w="ysc" and v="ys" and r="take ka wa" and s="ysa" and A="parser_bottom G" in elem_in_append_set)
       apply(rename_tac k w ka wa xf xg rpu1 rpu2 cb ysa ysb ysc ys)(*strict*)
       apply(force)
      apply(rename_tac k w ka wa xf xg rpu1 rpu2 cb ysa ysb ysc ys)(*strict*)
      apply (metis in_set_takeD nset_diff)
     apply(rename_tac k w ka wa xf xg rpu1 rpu2 cb ysa ysb ysc ys)(*strict*)
     apply(force)
    apply(rename_tac k w ka wa xf xg rpu1 rpu2 c ca ys cb ysa ysb ysc y nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac f k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca ys cb nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac f k w ka xc xe y ya xf xg wb rpu1 c ca ys cb nat x)(*strict*)
   apply(subgoal_tac "ka = Suc nat+(length xg + length x)")
    apply(rename_tac f k w ka xc xe y ya xf xg wb rpu1 c ca ys cb nat x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f k w ka xc xe y ya xf xg wb rpu1 c ca ys cb nat x)(*strict*)
   apply(clarsimp)
   apply(rename_tac f k w xc xe y ya xf xg wb rpu1 c ca ys cb x)(*strict*)
   apply(rule_tac xs="xc" in rev_cases)
    apply(rename_tac f k w xc xe y ya xf xg wb rpu1 c ca ys cb x)(*strict*)
    apply(clarsimp)
    apply(rename_tac f k w xe y ya xf xg wb c ca ys cb x)(*strict*)
    apply(rule_tac w="xg @ x" and v="xe" and r="take k w" and s="[]" and A="parser_bottom G" in elem_in_append_set)
      apply(rename_tac f k w xe y ya xf xg wb c ca ys cb x)(*strict*)
      apply(force)
     apply(rename_tac f k w xe y ya xf xg wb c ca ys cb x)(*strict*)
     apply (metis in_set_takeD nset_diff)
    apply(rename_tac f k w xe y ya xf xg wb c ca ys cb x)(*strict*)
    apply(force)
   apply(rename_tac f k w xc xe y ya xf xg wb rpu1 c ca ys cb x ysa yb)(*strict*)
   apply(clarsimp)
   apply(rename_tac f k w xe ya xf xg wb rpu1 c ca ys cb x ysa)(*strict*)
   apply(rule_tac xs="xe" in rev_cases)
    apply(rename_tac f k w xe ya xf xg wb rpu1 c ca ys cb x ysa)(*strict*)
    prefer 2
    apply(rename_tac f k w xe ya xf xg wb rpu1 c ca ys cb x ysa ysb y)(*strict*)
    apply(clarsimp)
   apply(rename_tac f k w xe ya xf xg wb rpu1 c ca ys cb x ysa)(*strict*)
   apply(clarsimp)
   apply(rename_tac f k w xf xg rpu1 c ca ys cb x ysa)(*strict*)
   apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take k w) \<longrightarrow>
       (\<exists>x. x @ [parser_bottom G] = rpu1)")
   apply(rule_tac xs="f" in rev_cases)
    apply(rename_tac f k w xf xg rpu1 c ca ys cb x ysa)(*strict*)
    apply(clarsimp)
   apply(rename_tac f k w xf xg rpu1 c ca ys cb x ysa ysb y)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w xf xg rpu1 c ca ys cb x ysa ysb y)(*strict*)
   apply(subgoal_tac "butlast_if_match ((xg @ x) @ [parser_bottom G])
          (parser_bottom G) = xg@x")
    apply(rename_tac k w xf xg rpu1 c ca ys cb x ysa ysb y)(*strict*)
    prefer 2
    apply (metis append_assoc butlast_if_match_direct)
   apply(rename_tac k w xf xg rpu1 c ca ys cb x ysa ysb y)(*strict*)
   apply(clarsimp)
   apply(case_tac "k - length ysb")
    apply(rename_tac k w xf xg rpu1 c ca ys cb x ysa ysb y)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w xf xg rpu1 ca cb x ysa ysb)(*strict*)
    apply(rule_tac xs="ca" in rev_cases)
     apply(rename_tac k w xf xg rpu1 ca cb x ysa ysb)(*strict*)
     apply(clarsimp)
    apply(rename_tac k w xf xg rpu1 ca cb x ysa ysb ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w xf xg rpu1 cb x ysa ysb ys)(*strict*)
    apply(rule_tac w="ysb" and v="ys" and r="xg" and s="x" and A="parser_bottom G" in elem_in_append_set)
      apply(rename_tac k w xf xg rpu1 cb x ysa ysb ys)(*strict*)
      apply(force)
     apply(rename_tac k w xf xg rpu1 cb x ysa ysb ys)(*strict*)
     apply (metis in_set_takeD nset_diff)
    apply(rename_tac k w xf xg rpu1 cb x ysa ysb ys)(*strict*)
    apply(force)
   apply(rename_tac k w xf xg rpu1 c ca ys cb x ysa ysb y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca nat)(*strict*)
  apply(subgoal_tac "k = Suc nat+length w")
   apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac f h k w ka wa xc xe y ya xf xg wb rpu1 rpu2 c ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x)(*strict*)
  apply(case_tac "ka - length wa")
   apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "min (length wa) ka=ka")
    apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x)(*strict*)
   apply(subgoal_tac "butlast_if_match (take ka wa) (parser_bottom G) = take ka wa")
    apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x)(*strict*)
    prefer 2
    apply (metis butlast_if_match_reduces in_set_conv_decomp in_set_takeD nset_diff)
   apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x)(*strict*)
   apply(rule_tac xs="xe" in rev_cases)
    apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x)(*strict*)
    apply(clarsimp)
    apply(rename_tac f h ka wa xc y ya xf xg wb c ca nat x)(*strict*)
    apply(rule_tac w="xf @ x" and v="xc" and r="take ka wa" and s="[]" and A="parser_bottom G" in elem_in_append_set)
      apply(rename_tac f h ka wa xc y ya xf xg wb c ca nat x)(*strict*)
      apply(force)
     apply(rename_tac f h ka wa xc y ya xf xg wb c ca nat x)(*strict*)
     apply (metis in_set_takeD nset_diff)
    apply(rename_tac f h ka wa xc y ya xf xg wb c ca nat x)(*strict*)
    apply(force)
   apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x ys yb)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h ka wa xc y xf xg rpu2 c ca nat x ys)(*strict*)
   apply(rule_tac ?w1.0="f" and ?w2.0="ca" and ?v1.0="take ka wa" and ?v2.0="ys @ [parser_bottom G]" in prefix_alt_apply)
     apply(rename_tac f h ka wa xc y xf xg rpu2 c ca nat x ys)(*strict*)
     apply(force)
    apply(rename_tac f h ka wa xc y xf xg rpu2 c ca nat x ys)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac f h ka wa xc y xf xg rpu2 c ca nat x ys)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac f h ka wa xc y xf xg rpu2 c ca nat x ys cb)(*strict*)
   apply(subgoal_tac "ca = cb@ys @ [parser_bottom G]")
    apply(rename_tac f h ka wa xc y xf xg rpu2 c ca nat x ys cb)(*strict*)
    prefer 2
    apply (metis Nil_is_append_conv append_eq_append_conv_if append_eq_conv_conj)
   apply(rename_tac f h ka wa xc y xf xg rpu2 c ca nat x ys cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h ka wa xc y xf xg rpu2 c nat x ys cb)(*strict*)
   apply(subgoal_tac "butlast_if_match ((xf @ x) @ [parser_bottom G]) (parser_bottom G) = xf@x")
    apply(rename_tac f h ka wa xc y xf xg rpu2 c nat x ys cb)(*strict*)
    prefer 2
    apply (metis append_assoc butlast_if_match_direct)
   apply(rename_tac f h ka wa xc y xf xg rpu2 c nat x ys cb)(*strict*)
   apply(clarsimp)
   apply(thin_tac "butlast_if_match (xf @ x @ [parser_bottom G]) (parser_bottom G) =
       xf @ x")
   apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take ka wa) \<longrightarrow>
       (\<exists>x. x @ [parser_bottom G] = rpu2)")
   apply(rule_tac xs="xc" in rev_cases)
    apply(rename_tac f h ka wa xc y xf xg rpu2 c nat x ys cb)(*strict*)
    prefer 2
    apply(rename_tac f h ka wa xc y xf xg rpu2 c nat x ys cb ysa ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb ysa)(*strict*)
    apply(rule_tac ?w.0="xf @ x" and v="ysa" and A="parser_bottom G" in elem_in_append_set)
      apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb ysa)(*strict*)
      apply(force)
     apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb ysa)(*strict*)
     apply(force)
    apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb ysa)(*strict*)
    apply(force)
   apply(rename_tac f h ka wa xc y xf xg rpu2 c nat x ys cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb)(*strict*)
   apply(rule_tac xs="drop
         (Suc (min (length xf + length x)
                (Suc (nat + (length xf + length x)))))
         f" in rev_cases)
    apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb)(*strict*)
    prefer 2
    apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb ysa y)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac f ka wa xf xg rpu2 c nat x ys cb ysa ca)(*strict*)
    apply(rule_tac xs="f" in rev_cases)
     apply(rename_tac f ka wa xf xg rpu2 c nat x ys cb ysa ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac f ka wa xf xg rpu2 c nat x ys cb ysa ca ysb y)(*strict*)
    apply(clarsimp)
    apply(rename_tac ka wa xf xg rpu2 c nat x ys cb ysa ca ysb y)(*strict*)
    apply(case_tac "(Suc (min (length xf + length x)
               (Suc (nat + (length xf + length x)))) -
         length ysb)")
     apply(rename_tac ka wa xf xg rpu2 c nat x ys cb ysa ca ysb y)(*strict*)
     apply(clarsimp)
     apply(rename_tac ka wa xf xg rpu2 nat x ys cb ca ysb)(*strict*)
     apply (metis in_set_conv_decomp)
    apply(rename_tac ka wa xf xg rpu2 c nat x ys cb ysa ca ysb y nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "min (length xf + length x)
                (Suc (nat + (length xf + length x))) = (length xf + length x)")
    apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb)(*strict*)
   apply(clarsimp)
   apply(rule_tac ?w1.0="xf" and ?w2.0="x" and ?v1.0="f" and ?v2.0="cb@ys" in prefix_alt_apply)
     apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb)(*strict*)
     apply(force)
    apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac f h ka wa xg rpu2 c nat x ys cb ca)(*strict*)
    apply (metis append_assoc append_eq_conv_conj drop_length_append tail_empty)
   apply(rename_tac f h ka wa xf xg rpu2 c nat x ys cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac h ka wa xf xg rpu2 c nat x ys cb ca)(*strict*)
   apply(subgoal_tac "x=ca @ cb@ys")
    apply(rename_tac h ka wa xf xg rpu2 c nat x ys cb ca)(*strict*)
    prefer 2
    apply (metis (erased, hide_lams) append_assoc append_eq_conv_conj)
   apply(rename_tac h ka wa xf xg rpu2 c nat x ys cb ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac h ka wa xf xg rpu2 c nat ys cb ca)(*strict*)
   apply(thin_tac "min (length xf + (length ca + (length cb + length ys)))
        (Suc (nat + (length xf + (length ca + (length cb + length ys))))) =
       length xf + (length ca + (length cb + length ys))")
   apply(thin_tac "(ca @ cb @ ys @ [parser_bottom G]) \<sqsupseteq> [parser_bottom G]")
   apply(thin_tac "set (take ka wa) \<subseteq> parser_events G")
   apply(thin_tac "parser_bottom G \<notin> set (take ka wa)")
   apply(thin_tac "h \<sqsupseteq> butlast_if_match (xf @ ca) (parser_bottom G)")
   apply(thin_tac "set h \<subseteq> parser_events G")
   apply(subgoal_tac "drop (length xf + length ca) (take ka wa) = cb")
    apply(rename_tac h ka wa xf xg rpu2 c nat ys cb ca)(*strict*)
    prefer 2
    apply(rule_tac t="take ka wa" and s="xf @ ca @ cb" in subst)
     apply(rename_tac h ka wa xf xg rpu2 c nat ys cb ca)(*strict*)
     apply(force)
    apply(rename_tac h ka wa xf xg rpu2 c nat ys cb ca)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac h ka wa xf xg rpu2 c nat ys cb ca)(*strict*)
   apply(force)
  apply(rename_tac f h ka wa xc xe y ya xf xg wb rpu2 c ca nat x nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h ka xc xe y ya xf xg wb c ca nat x nata xa)(*strict*)
  apply(subgoal_tac "ka  = Suc nata+(length xg + length xa)")
   apply(rename_tac f h ka xc xe y ya xf xg wb c ca nat x nata xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac f h ka xc xe y ya xf xg wb c ca nat x nata xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h xc xe y ya xf xg wb c ca nat x xa)(*strict*)
  apply(subgoal_tac "butlast_if_match ((xf @ x) @ [parser_bottom G]) (parser_bottom G) = xf @ x")
   apply(rename_tac f h xc xe y ya xf xg wb c ca nat x xa)(*strict*)
   prefer 2
   apply (metis butlast_if_match_direct)
  apply(rename_tac f h xc xe y ya xf xg wb c ca nat x xa)(*strict*)
  apply(subgoal_tac "butlast_if_match ((xg @ xa) @ [parser_bottom G]) (parser_bottom G) = xg @ xa")
   apply(rename_tac f h xc xe y ya xf xg wb c ca nat x xa)(*strict*)
   prefer 2
   apply (metis butlast_if_match_direct)
  apply(rename_tac f h xc xe y ya xf xg wb c ca nat x xa)(*strict*)
  apply(clarsimp)
  apply(thin_tac "butlast_if_match (xf @ x @ [parser_bottom G]) (parser_bottom G) =
       xf @ x")
  apply(thin_tac "butlast_if_match (xg @ xa @ [parser_bottom G]) (parser_bottom G) =
       xg @ xa")
  apply(rule_tac xs="xe" in rev_cases)
   apply(rename_tac f h xc xe y ya xf xg wb c ca nat x xa)(*strict*)
   prefer 2
   apply(rename_tac f h xc xe y ya xf xg wb c ca nat x xa ys yb)(*strict*)
   apply(clarsimp)
  apply(rename_tac f h xc xe y ya xf xg wb c ca nat x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h xc y xf xg c ca nat x xa)(*strict*)
  apply(rule_tac xs="xc" in rev_cases)
   apply(rename_tac f h xc y xf xg c ca nat x xa)(*strict*)
   prefer 2
   apply(rename_tac f h xc y xf xg c ca nat x xa ys ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h xf xg c ca nat x xa ys)(*strict*)
   apply(rule_tac w="xf@x" and A="parser_bottom G" and v="ys" and r="xg" and s="xa" in elem_in_append_set)
     apply(rename_tac f h xf xg c ca nat x xa ys)(*strict*)
     apply(force)
    apply(rename_tac f h xf xg c ca nat x xa ys)(*strict*)
    apply(force)
   apply(rename_tac f h xf xg c ca nat x xa ys)(*strict*)
   apply(force)
  apply(rename_tac f h xc y xf xg c ca nat x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h xf xg c ca nat x xa)(*strict*)
  apply(thin_tac "h \<sqsupseteq> butlast_if_match f (parser_bottom G)")
  apply(thin_tac "set h \<subseteq> parser_events G")
  apply(rule_tac xs="drop
         (Suc (min (length xf + length x)
                (Suc (nat + (length xf + length x)))))
         f" in rev_cases)
   apply(rename_tac f h xf xg c ca nat x xa)(*strict*)
   prefer 2
   apply(rename_tac f h xf xg c ca nat x xa ys y)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "y=parser_bottom G")
    apply(rename_tac f h xf xg c ca nat x xa ys y)(*strict*)
    prefer 2
    apply(simp add: suffix_def)
   apply(rename_tac f h xf xg c ca nat x xa ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h xf xg c ca nat x xa ys)(*strict*)
   apply(rule_tac xs="f" in rev_cases)
    apply(rename_tac f h xf xg c ca nat x xa ys)(*strict*)
    apply(force)
   apply(rename_tac f h xf xg c ca nat x xa ys ysa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac h xf xg c ca nat x xa ys ysa y)(*strict*)
   apply(case_tac "Suc (min (length xf + length x)
               (Suc (nat + (length xf + length x)))) -
         length ysa")
    apply(rename_tac h xf xg c ca nat x xa ys ysa y)(*strict*)
    prefer 2
    apply(rename_tac h xf xg c ca nat x xa ys ysa y nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac h xf xg c ca nat x xa ys ysa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac h xf xg ca nat x xa ysa)(*strict*)
   apply(rule_tac xs="ca" in rev_cases)
    apply(rename_tac h xf xg ca nat x xa ysa)(*strict*)
    apply(clarsimp)
   apply(rename_tac h xf xg ca nat x xa ysa ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac h xf xg nat x xa ysa ys)(*strict*)
   apply(rule_tac w="ysa" and A="parser_bottom G" and v="ys" and r="xg" and s="xa" in elem_in_append_set)
     apply(rename_tac h xf xg nat x xa ysa ys)(*strict*)
     apply(force)
    apply(rename_tac h xf xg nat x xa ysa ys)(*strict*)
    apply(force)
   apply(rename_tac h xf xg nat x xa ysa ys)(*strict*)
   apply(force)
  apply(rename_tac f h xf xg c ca nat x xa)(*strict*)
  apply(clarsimp)
  apply(thin_tac "(x @ [parser_bottom G]) \<sqsupseteq> [parser_bottom G]")
  apply(thin_tac "parser_bottom G \<notin> set h")
  apply(subgoal_tac "min (length xf + length x)
                (Suc (nat + (length xf + length x))) = length xf + length x")
   apply(rename_tac f h xf xg c ca nat x xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac f h xf xg c ca nat x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac f xf xg c ca nat x xa)(*strict*)
  apply(thin_tac "min (length xf + length x)
                (Suc (nat + (length xf + length x))) = length xf + length x")
  apply(thin_tac "length f \<le> Suc (length xf + length x)")
  apply(rule_tac ?w1.0="f" and ?w2.0="ca" and ?v1.0="xg" and ?v2.0="xa @ [parser_bottom G]" in prefix_alt_apply)
    apply(rename_tac f xf xg c ca nat x xa)(*strict*)
    apply(force)
   apply(rename_tac f xf xg c ca nat x xa)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(rename_tac f xf xg c ca x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xf xg c ca x xa cb)(*strict*)
   apply(rule_tac ?w1.0="cb" and ?w2.0="ca" and ?v1.0="xa" and ?v2.0="[parser_bottom G]" in prefix_alt_apply)
     apply(rename_tac xf xg c ca x xa cb)(*strict*)
     apply(force)
    apply(rename_tac xf xg c ca x xa cb)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac xf xg c ca x xa cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac xf xg c x cb)(*strict*)
   apply(rule_tac ?w1.0="xf" and ?w2.0="x" and ?v1.0="xg" and ?v2.0="cb @
       drop (length xg + length cb) xf @
       drop (length xg + length cb - length xf) x @ c" in prefix_alt_apply)
     apply(rename_tac xf xg c x cb)(*strict*)
     apply(force)
    apply(rename_tac xf xg c x cb)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac xg c x cb ca)(*strict*)
    apply(rule_tac ?w1.0="ca" and ?w2.0="x" and ?v1.0="cb" and ?v2.0="drop (length cb) ca @ drop (length cb - length ca) x @ c" in prefix_alt_apply)
      apply(rename_tac xg c x cb ca)(*strict*)
      apply(force)
     apply(rename_tac xg c x cb ca)(*strict*)
     prefer 2
     apply(simp add: prefix_def)
     apply(clarsimp)
    apply(rename_tac xg c x cb ca)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac xg c x ca cc)(*strict*)
    apply(rule parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB_hlp2)
     apply(rename_tac xg c x ca cc)(*strict*)
     apply(force)
    apply(rename_tac xg c x ca cc)(*strict*)
    apply(force)
   apply(rename_tac xf xg c x cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac xf c x cb ca)(*strict*)
   apply(rule_tac x="x" and cc="ca @ cb" and c="c" in parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB_hlp2)
    apply(rename_tac xf c x cb ca)(*strict*)
    apply(force)
   apply(rename_tac xf c x cb ca)(*strict*)
   apply(force)
  apply(rename_tac f xf xg c ca nat x xa)(*strict*)
  apply(simp add: prefix_def)
  apply(rename_tac f xf xg c ca x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac f xf c x xa cb)(*strict*)
  apply(rule_tac ?w1.0="xf" and ?w2.0="x" and ?v1.0="f" and ?v2.0="cb @ xa" in prefix_alt_apply)
    apply(rename_tac f xf c x xa cb)(*strict*)
    apply(force)
   apply(rename_tac f xf c x xa cb)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac f c x xa cb ca)(*strict*)
   apply(rule_tac ?w1.0="ca" and ?w2.0="x" and ?v1.0="cb" and ?v2.0="xa" in prefix_alt_apply)
     apply(rename_tac f c x xa cb ca)(*strict*)
     apply(force)
    apply(rename_tac f c x xa cb ca)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac f c x xa cb ca)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac f xf c x xa cb)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma compatible_history_fragment_SB_sym: "
       parserHF.compatible_history_fragment_SB G (parserHFvHFS_Lin2BraConf cL)
        (parserHFvHFS_Lin2BraConf cL1) (parserHFvHFS_Lin2BraConf cL2) =
       parserHF.compatible_history_fragment_SB G (parserHFvHFS_Lin2BraConf cL)
        (parserHFvHFS_Lin2BraConf cL2) (parserHFvHFS_Lin2BraConf cL1)"
  apply(simp add: parserHF.compatible_history_fragment_SB_def)
  apply(simp add: Let_def)
  apply(rule antisym)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB: "
 (\<forall>G. valid_parser G \<longrightarrow>
         (\<forall>cL. cL \<in> ATS.get_accessible_configurations
                      parserHFS_initial_configurations
                      parserHFS_step_relation G \<longrightarrow>
               (\<forall>e1 cL1.
                   parserHFS_step_relation G cL e1 cL1 \<longrightarrow>
                   (\<forall>e2 cL2.
                       parserHFS_step_relation G cL e2 cL2 \<longrightarrow>
                       ATS_determHIST_SB.compatible_history_fragment_SB
                        parser_markers (@) (@) parserHF_conf_history
                        parser_fixed_scheduler_extendable
                        parserHF_conf_fixed G (parserHFvHFS_Lin2BraConf cL)
                        (parserHFvHFS_Lin2BraConf cL1)
                        (parserHFvHFS_Lin2BraConf cL2)))))"
  apply(clarsimp)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   prefer 2
   apply(simp add: parserHFS_step_relation_def valid_parser_def)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   prefer 2
   apply(simp add: parserHFS_step_relation_def valid_parser_def)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(subgoal_tac "cL \<in> parserHFS_configurations G")
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   prefer 2
   apply (metis parserHFS.get_accessible_configurations_are_configurations2)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(thin_tac "cL \<in> ATS.get_accessible_configurations
              parserHFS_initial_configurations parserHFS_step_relation G")
  apply(subgoal_tac "parserHFS_conf_history cL1 = parserHFS_conf_history cL2 \<or> (strict_prefix (parserHFS_conf_history cL1) (parserHFS_conf_history cL2)) \<or> (strict_prefix (parserHFS_conf_history cL2) (parserHFS_conf_history cL1))")
   prefer 2
   apply(rule_tac x="parserHFS_conf_history cL @ drop (length (parserHFS_conf_fixed cL)) (parserHFS_conf_scheduler cL)" in three_cases_strict_prefix)
    apply(rule parserHFS_post_history_prefix_of_pre_history_and_remaining_rhs)
       apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
       apply(force)
      apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
      apply(force)
     apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
     apply(force)
    apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   apply(rule parserHFS_post_history_prefix_of_pre_history_and_remaining_rhs)
      apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
      apply(force)
     apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
     apply(force)
    apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   apply(force)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(subgoal_tac "
       drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e1) (parser_bottom G))
       \<in> parser_markers G \<and>
       drop (length (parserHFS_conf_fixed cL))
        (butlast_if_match (rule_rpop e2) (parser_bottom G))
       \<in> parser_markers G")
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   prefer 2
   apply(simp add: parserHFS_step_relation_def parserHFvHFS_Lin2BraConf_def Let_def)
   apply(clarsimp)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
   apply(rule conjI)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
    apply(simp add: parser_markers_def)
    apply(rule_tac B="set (
             (butlast_if_match (rule_rpop e1) (parser_bottom G)))" in subset_trans)
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
     apply(rule set_drop_subset)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
    apply(rule_tac B="set (
             ((rule_rpop e1) ))" in subset_trans)
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
     apply(rule set_butlast_if_match_subset)
     apply(force)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
    apply(simp add: valid_parser_def)
    apply(clarsimp)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd)(*strict*)
    apply(erule_tac x="e1" in ballE)
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd)(*strict*)
    apply(simp add: valid_parser_step_label_def kPrefix_def)
    apply(clarsimp)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
    apply(simp add: kPrefix_def)
    apply(erule_tac P="xd \<in> set (take k w)" in disjE)
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
     apply(rule_tac A="set w" in set_mp)
      apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
      apply(blast)
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
     apply(rule_tac A="set (take k w)" in set_mp)
      apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
      apply(rule set_take_subset2)
      apply(force)
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
     apply(force)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
    apply(case_tac "k-length w")
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
     apply(clarsimp)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
   apply(simp add: parser_markers_def)
   apply(rule_tac B="set (
             (butlast_if_match (rule_rpop e2) (parser_bottom G)))" in subset_trans)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
   apply(rule_tac B="set (
             ((rule_rpop e2) ))" in subset_trans)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
    apply(rule set_butlast_if_match_subset)
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya)(*strict*)
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd)(*strict*)
   apply(erule_tac x="e2" in ballE)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd)(*strict*)
   apply(simp add: valid_parser_step_label_def kPrefix_def)
   apply(clarsimp)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
   apply(simp add: kPrefix_def)
   apply(erule_tac P="xd \<in> set (take k w)" in disjE)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
    apply(rule_tac A="set w" in set_mp)
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
     apply(blast)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
    apply(rule_tac A="set (take k w)" in set_mp)
     apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
     apply(rule set_take_subset2)
     apply(force)
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
   apply(case_tac "k-length w")
    apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf)(*strict*)
    apply(clarsimp)
   apply(rename_tac G cL e1 cL1 e2 cL2 x xa xb xc y ya xd k w xf nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(erule_tac P="parserHFS_conf_history cL1 = parserHFS_conf_history cL2" in disjE)
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   apply(simp add: parserHF.compatible_history_fragment_SB_def)
   apply(simp add: parserHFS_step_relation_def parserHFvHFS_Lin2BraConf_def Let_def)
   apply(clarsimp)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(erule_tac P="parserHFS_conf_history cL1 \<sqsubset> parserHFS_conf_history cL2" in disjE)
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   apply(rule parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB_hlp3)
          apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
          apply(force)
         apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
         apply(force)
        apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
        apply(force)
       apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
       apply(force)
      apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
      apply(force)
     apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
     apply(force)
    apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   apply(force)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(rule_tac t="ATS_determHIST_SB.compatible_history_fragment_SB parser_markers (@)
        (@) parserHF_conf_history parser_fixed_scheduler_extendable
        parserHF_conf_fixed G (parserHFvHFS_Lin2BraConf cL)
        (parserHFvHFS_Lin2BraConf cL1) (parserHFvHFS_Lin2BraConf cL2)" and s="ATS_determHIST_SB.compatible_history_fragment_SB parser_markers (@)
        (@) parserHF_conf_history parser_fixed_scheduler_extendable
        parserHF_conf_fixed G (parserHFvHFS_Lin2BraConf cL)
        (parserHFvHFS_Lin2BraConf cL2) (parserHFvHFS_Lin2BraConf cL1)" in ssubst)
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   prefer 2
   apply(rule_tac ?cL2.0="cL1" in parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB_hlp3)
          apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
          apply(force)
         apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
         apply(force)
        apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
        apply(force)
       apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
       apply(force)
      apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
      apply(force)
     apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
     apply(force)
    apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
    apply(force)
   apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
   apply(force)
  apply(rename_tac G cL e1 cL1 e2 cL2)(*strict*)
  apply(rule compatible_history_fragment_SB_sym)
  done

corollary example_translation_0: "
  valid_parser G
  \<Longrightarrow> \<lparr>parserHF_conf_fixed=f, parserHF_conf_history=h, parserHF_conf_stack = l\<rparr> \<in> parserHF_configurations G
  \<Longrightarrow> \<exists>r. \<lparr>parserHFS_conf_fixed=f, parserHFS_conf_history=h, parserHFS_conf_stack = l, parserHFS_conf_scheduler=r\<rparr> \<in> parserHFS_configurations G"
  apply(simp add: parserHF_configurations_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(case_tac "parser_bottom G \<in> set f")
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      x="(w @ [parser_bottom G])"
      in exI)
   apply(clarsimp)
   apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rule_tac
      x="(f @ [parser_bottom G])"
      in exI)
  apply(clarsimp)
  apply(simp add: prefix_def)
  apply(simp add: valid_parser_def)
  done

corollary example_translation_1: "
  valid_parser G
  \<Longrightarrow> \<lparr>parserHFS_conf_fixed=f, parserHFS_conf_history=h, parserHFS_conf_stack = l, parserHFS_conf_scheduler=r\<rparr> \<in> parserHFS_configurations G
  \<Longrightarrow> \<lparr>parserHF_conf_fixed=f, parserHF_conf_history=h, parserHF_conf_stack = l\<rparr> \<in> parserHF_configurations G"
  apply(simp add: parserHF_configurations_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac w c)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac w c)(*strict*)
   apply(rule_tac
      B="set(f@c)"
      in subset_trans)
    apply(rename_tac w c)(*strict*)
    apply(rule set_append1)
   apply(rename_tac w c)(*strict*)
   apply(force)
  apply(rename_tac w c)(*strict*)
  apply(clarsimp)
  apply(case_tac "c")
   apply(rename_tac w c)(*strict*)
   apply(clarsimp)
  apply(rename_tac w c a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac w c a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w c a list)(*strict*)
  apply(thin_tac "c = a # list")
  apply(clarsimp)
  done

corollary example_translation_2: "
  \<lparr>rule_lpop = [p], rule_rpop = [a, b], rule_lpush = [q], rule_rpush = [b]\<rparr> \<in> parser_rules G
  \<Longrightarrow> b \<noteq> parser_bottom G
  \<Longrightarrow> a \<noteq> parser_bottom G
  \<Longrightarrow> parserHF_step_relation G \<lparr>parserHF_conf_fixed=[a], parserHF_conf_history=[a], parserHF_conf_stack = [p]\<rparr> \<lparr>rule_lpop=[p], rule_rpop=[a, b], rule_lpush=[q], rule_rpush=[b]\<rparr> \<lparr>parserHF_conf_fixed=[b], parserHF_conf_history=[a, b], parserHF_conf_stack = [q]\<rparr> "
  apply(simp only: parserHF_step_relation_def)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   defer
   apply(rule conjI)
    apply(force)
   apply(clarsimp)
   apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(subgoal_tac "butlast_if_match [a, b] (parser_bottom G) = [a, b]")
   apply(clarsimp)
  apply(rule butlast_if_match_direct2_prime)
  apply(clarsimp)
  done

lemma parserHF_rpop_prefix_closureeeds_fixed_append_history_mod: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w
  \<Longrightarrow> prefix (butlast_if_match (rule_rpop e1) (parser_bottom G))
  (butlast_if_match (parserHF_conf_fixed c) (parser_bottom G) @ w @ v)"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule disjE)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x ca)(*strict*)
   apply(case_tac "suffix (parserHF_conf_fixed c) [parser_bottom G]")
    apply(rename_tac x ca)(*strict*)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac x ca caa)(*strict*)
    apply(subgoal_tac "butlast_if_match (caa @ [parser_bottom G]) (parser_bottom G) = caa")
     apply(rename_tac x ca caa)(*strict*)
     prefer 2
     apply (metis butlast_if_match_direct)
    apply(rename_tac x ca caa)(*strict*)
    apply(clarsimp)
    apply(thin_tac "butlast_if_match (caa @ [parser_bottom G]) (parser_bottom G) = caa")
    apply(case_tac ca)
     apply(rename_tac x ca caa)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ca)(*strict*)
     apply(subgoal_tac "butlast_if_match (ca @ [parser_bottom G]) (parser_bottom G)=ca")
      apply(rename_tac x ca)(*strict*)
      prefer 2
      apply (metis butlast_if_match_direct)
     apply(rename_tac x ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac x ca caa a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
     apply(rename_tac x ca caa a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac x ca caa a list)(*strict*)
    apply(thin_tac "ca = a # list")
    apply(clarsimp)
    apply(rename_tac x w')(*strict*)
    apply(subgoal_tac "butlast_if_match (rule_rpop e1) (parser_bottom G)=rule_rpop e1")
     apply(rename_tac x w')(*strict*)
     apply(force)
    apply(rename_tac x w')(*strict*)
    apply(simp add: parserHF_configurations_def)
    apply(clarsimp)
    apply(rename_tac x w' h)(*strict*)
    apply(subgoal_tac "butlast_if_match (rule_rpop e1 @ w' @ [parser_bottom G]) (parser_bottom G) = rule_rpop e1 @ w'")
     apply(rename_tac x w' h)(*strict*)
     prefer 2
     apply (metis butlast_if_match_direct butlast_if_match_pull_out_prime)
    apply(rename_tac x w' h)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac x w' c)(*strict*)
    apply (metis butlast_if_match_direct2_prime)
   apply(rename_tac x ca)(*strict*)
   apply(subgoal_tac "butlast_if_match (parserHF_conf_fixed c) (parser_bottom G) = parserHF_conf_fixed c")
    apply(rename_tac x ca)(*strict*)
    apply(subgoal_tac "butlast_if_match (rule_rpop e1) (parser_bottom G) = rule_rpop e1")
     apply(rename_tac x ca)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      x="ca@drop (length (parserHF_conf_fixed c)) (rule_rpop e1) @ v"
      in exI)
     apply(force)
    apply(rename_tac x ca)(*strict*)
    apply(simp add: parserHF_configurations_def)
    apply(clarsimp)
    apply(rename_tac x c h)(*strict*)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac x c ca)(*strict*)
    apply (metis butlast_if_match_direct2_prime)
   apply(rename_tac x ca)(*strict*)
   apply (metis butlast_if_match_reduces suffix_def)
  apply(rename_tac x)(*strict*)
  apply(case_tac "suffix (rule_rpop e1) [parser_bottom G]")
   apply(rename_tac x)(*strict*)
   apply(simp add: suffix_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x ca caa)(*strict*)
   apply(subgoal_tac "butlast_if_match (caa @ [parser_bottom G]) (parser_bottom G) = caa")
    apply(rename_tac x ca caa)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct)
   apply(rename_tac x ca caa)(*strict*)
   apply(clarsimp)
   apply(case_tac "ca")
    apply(rename_tac x ca caa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x ca caa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
    apply(rename_tac x ca caa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x ca caa a list)(*strict*)
   apply(thin_tac "ca = a # list")
   apply(clarsimp)
   apply(rename_tac x w')(*strict*)
   apply(subgoal_tac "butlast_if_match (parserHF_conf_fixed c) (parser_bottom G)=parserHF_conf_fixed c")
    apply(rename_tac x w')(*strict*)
    apply(clarsimp)
   apply(rename_tac x w')(*strict*)
   apply(simp add: parserHF_configurations_def)
   apply(clarsimp)
   apply(rename_tac x w' f h)(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac x w' f c)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G e1")
    apply(rename_tac x w' f c)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x w' f c k w xb xc)(*strict*)
    apply(case_tac "parser_bottom G \<in> set f")
     apply(rename_tac x w' f c k w xb xc)(*strict*)
     apply(clarsimp)
     apply(rename_tac x w' c k w xb xc wa)(*strict*)
     apply (metis append_Cons butlast_only_tail_contra butlast_snoc butlast_snoc_2 head_in_set in_set_butlast_appendI triv_compl)
    apply(rename_tac x w' f c k w xb xc)(*strict*)
    apply(clarsimp)
    apply (metis butlast_if_match_direct2_prime)
   apply(rename_tac x w' f c)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "butlast_if_match (rule_rpop e1) (parser_bottom G) = rule_rpop e1")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply (metis butlast_if_match_reduces suffix_def)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x ca)(*strict*)
  apply(subgoal_tac "butlast_if_match (parserHF_conf_fixed c) (parser_bottom G) = parserHF_conf_fixed c")
   apply(rename_tac x ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t=" drop (length (parserHF_conf_fixed c)) (rule_rpop e1)"
      and s="ca"
      in ssubst)
    apply(rename_tac x ca)(*strict*)
    apply (metis dropPrecise)
   apply(rename_tac x ca)(*strict*)
   apply(rule_tac
      t="rule_rpop e1"
      and s="parserHF_conf_fixed c @ ca"
      in ssubst)
    apply(rename_tac x ca)(*strict*)
    apply(force)
   apply(rename_tac x ca)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(force)
  apply(rename_tac x ca)(*strict*)
  apply(rule butlast_if_match_direct2_prime)
  apply(rule_tac
      B="set (rule_rpop e1)"
      in nset_mp)
   apply(rename_tac x ca)(*strict*)
   apply (metis set_app_subset)
  apply(rename_tac x ca)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(rename_tac x ca)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x ca k w xb)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x ca k w xb)(*strict*)
    apply(clarsimp)
    apply (metis in_set_takeD not_in_diff)
   apply(rename_tac x ca k w xb nat)(*strict*)
   apply(force)
  apply(rename_tac x ca)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma parserHF_history_extensions_longer_implies_rpop_longer: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w @ v
  \<Longrightarrow> w@v\<noteq>[]
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w
  \<Longrightarrow> length (butlast_if_match (rule_rpop e2) (parser_bottom G)) \<le> length (butlast_if_match (rule_rpop e1) (parser_bottom G))"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: parserHF_configurations_def)
  apply(clarsimp)
  apply(rename_tac x xa f h)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x xa f c)(*strict*)
  apply(case_tac "length (butlast_if_match (rule_rpop e1) (parser_bottom G)) \<ge> length f")
   apply(rename_tac x xa f c)(*strict*)
   apply(rule drop_length_leq)
    apply(rename_tac x xa f c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa f c)(*strict*)
   apply(force)
  apply(rename_tac x xa f c)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_minimal_step_prefix_closureondition: "
  valid_parser G
  \<Longrightarrow> e \<in> parser_rules G
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> suffix (parserHFS_conf_stack c) (rule_lpop e)
  \<Longrightarrow> prefix (rule_rpop e) (parserHFS_conf_scheduler c)
  \<Longrightarrow> \<exists>c'. parserHFS_step_relation G c e c'"
  apply(simp add: parserHFS_step_relation_def)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac ca caa)(*strict*)
  apply(rule_tac
      x="\<lparr>parserHFS_conf_fixed=rule_rpush e @ drop (length (rule_rpop e)) (parserHFS_conf_fixed c), parserHFS_conf_history=parserHFS_conf_history c @ drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e) (parser_bottom G)), parserHFS_conf_stack =SSl, parserHFS_conf_scheduler=SSr\<rparr>" for SSr SSl
      in exI)
  apply(rename_tac ca caa)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac ca caa)(*strict*)
   apply(force)
  apply(rename_tac ca caa)(*strict*)
  apply(rule_tac
      x="caa"
      in exI)
  apply(rule conjI)
   apply(rename_tac ca caa)(*strict*)
   apply(force)
  apply(rename_tac ca caa)(*strict*)
  apply(rule conjI)
   apply(rename_tac ca caa)(*strict*)
   apply(force)
  apply(rename_tac ca caa)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac c ca f h w)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac c ca f w cb)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac c ca f w cb)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac c ca f w cb k wa xa)(*strict*)
   apply (metis last_append append_Nil2 butlast_pull_out2 last_snoc)
  apply(rename_tac c ca f w cb)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma step_which_turns_fixed_unextendable_exceeds_fixed: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> prefix (parserHF_conf_fixed c) (rule_rpop e1)"
  apply(simp add: parserHF_step_relation_def parserHF_configurations_def prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac c x ca cb cc)(*strict*)
  apply(case_tac cc)
   apply(rename_tac c x ca cb cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac c x ca cb cc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. cc = w' @ [x']")
   apply(rename_tac c x ca cb cc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac c x ca cb cc a list)(*strict*)
  apply(thin_tac "cc = a # list")
  apply(clarsimp)
  done

lemma step_which_modifies_history_exceeds_fixed: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> w2 \<noteq> []
  \<Longrightarrow> prefix (parserHF_conf_fixed c) (rule_rpop e1)"
  apply(simp add: parserHF_step_relation_def parserHF_configurations_def prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x c ca cb)(*strict*)
  apply(case_tac cb)
   apply(rename_tac x c ca cb)(*strict*)
   apply(clarsimp)
  apply(rename_tac x c ca cb a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
   apply(rename_tac x c ca cb a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x c ca cb a list)(*strict*)
  apply(thin_tac "cb = a # list")
  apply(clarsimp)
  apply(rename_tac x c ca w' x')(*strict*)
  apply (metis append_length_inc butlast_if_match_direct2_prime le_Suc_eq length_append)
  done

lemma step_which_almost_modifies_history_exceeds_fixed: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> rule_rpop e1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> length (parserHF_conf_fixed c) \<le> length (butlast_if_match (rule_rpop e1) (parser_bottom G))"
  apply(simp add: parserHF_step_relation_def parserHF_configurations_def prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac f c x ca cb)(*strict*)
  apply(subgoal_tac "butlast_if_match (c @ [parser_bottom G]) (parser_bottom G)=c")
   apply(rename_tac f c x ca cb)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac f c x ca cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac f c x ca cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac f c x ca cb cc)(*strict*)
   apply (metis List.butlast_append butlast_if_match_direct2_prime butlast_snoc drop_length_append self_append_conv)
  apply(rename_tac f c x ca cb)(*strict*)
  apply (metis butlast_if_match_direct insert_Nil)
  done

lemma step_which_turns_fixed_unextendable_has_bottom_as_suffix: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> suffix (rule_rpop e1) [parser_bottom G]"
  apply(subgoal_tac "prefix (parserHF_conf_fixed c) (rule_rpop e1)")
   prefer 2
   apply(rule step_which_turns_fixed_unextendable_exceeds_fixed)
         apply(force)
        apply(force)
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: parserHF_step_relation_def parserHF_configurations_def prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac f c ca x cb cc)(*strict*)
  apply(subgoal_tac "\<exists>x. rule_rpop e1 = x @ (rule_rpush e1)")
   apply(rename_tac f c ca x cb cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac f c ca x cb cc xa)(*strict*)
   apply(subgoal_tac "drop (length xa + length (rule_rpush e1)) f=[]")
    apply(rename_tac f c ca x cb cc xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac f c ca x cb cc xa)(*strict*)
   apply (metis drop_all drop_length_append length_append)
  apply(rename_tac f c ca x cb cc)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(rename_tac f c ca x cb cc)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac f c ca x cb cc k w xb)(*strict*)
   apply(rule_tac
      x="xb"
      in exI)
   apply(force)
  apply(rename_tac f c ca x cb cc)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma step_which_not_turns_fixed_unextendable_has_not_bottom_as_suffix: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> suffix (rule_rpop e1) [parser_bottom G]"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x ca)(*strict*)
  apply(simp add: parserHF_configurations_def)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x c f ca cb)(*strict*)
  apply(subgoal_tac "butlast_if_match f (parser_bottom G) = f")
   apply(rename_tac x c f ca cb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast_if_match (rule_rpush e1 @ drop (Suc (length c)) f) (parser_bottom G)= rule_rpush e1 @ drop (Suc (length c)) f")
    apply(rename_tac x c f ca cb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (c @ [parser_bottom G]) (parser_bottom G)=c")
     apply(rename_tac x c f ca cb)(*strict*)
     apply(clarsimp)
     apply(erule disjE)
      apply(rename_tac x c f ca cb)(*strict*)
      apply(clarsimp)
     apply(rename_tac x c f ca cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac x c f ca cb cc)(*strict*)
     apply(case_tac cc)
      apply(rename_tac x c f ca cb cc)(*strict*)
      apply(clarsimp)
     apply(rename_tac x c f ca cb cc a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. cc = w' @ [x']")
      apply(rename_tac x c f ca cb cc a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac x c f ca cb cc a list)(*strict*)
     apply(thin_tac "cc = a # list")
     apply(clarsimp)
     apply(rename_tac x f ca cb w')(*strict*)
     apply(subgoal_tac "valid_parser_step_label G e1")
      apply(rename_tac x f ca cb w')(*strict*)
      apply(simp add: valid_parser_step_label_def)
      apply(clarsimp)
      apply(rename_tac x f ca cb w' k w xb xc)(*strict*)
      apply(erule_tac
      x="xc"
      and P="\<lambda>xc. rule_rpush e1 \<noteq> xc @ [parser_bottom G]"
      in allE)
      apply(force)
     apply(rename_tac x f ca cb w')(*strict*)
     apply(simp add: valid_parser_def)
    apply(rename_tac x c f ca cb)(*strict*)
    apply (metis butlast_if_match_direct insert_Nil)
   apply(rename_tac x c f ca cb)(*strict*)
   apply (metis butlast_if_match_direct2_prime butlast_if_match_pull_out_prime)
  apply(rename_tac x c f ca cb)(*strict*)
  apply (metis butlast_if_match_direct2_prime)
  done

lemma parserHF_prefix_closureise_history_modification: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_fixed c \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> rule_rpop e1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> w2 = butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) (parser_bottom G)"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac x ca)(*strict*)
  apply(subgoal_tac "butlast_if_match (ca @ [parser_bottom G]) (parser_bottom G)=ca")
   apply(rename_tac x ca)(*strict*)
   apply(clarsimp)
   apply(case_tac "length (parserHF_conf_fixed c) - length ca")
    apply(rename_tac x ca)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (drop (length (parserHF_conf_fixed c)) ca @ [parser_bottom G]) (parser_bottom G) = drop (length (parserHF_conf_fixed c)) ca")
     apply(rename_tac x ca)(*strict*)
     prefer 2
     apply (metis butlast_if_match_direct rotate_simps)
    apply(rename_tac x ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac x ca nat)(*strict*)
   apply(clarsimp)
   apply(simp add: butlast_if_match_def)
  apply(rename_tac x ca)(*strict*)
  apply (metis butlast_if_match_direct)
  done

lemma parserHF_prefix_closureise_history_modification_prime: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_fixed c \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> \<not> rule_rpop e1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> w2 = butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) (parser_bottom G)"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: suffix_def)
  apply(subgoal_tac "butlast_if_match (rule_rpop e1) (parser_bottom G)=rule_rpop e1")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply (metis butlast_if_match_reduces rotate_simps)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply (metis butlast_if_match_reduces concat_asso drop_prefix_closureise prefix_def)
  done

lemma parserHF_equal_history_extension_and_turning_nonextendable_implies_eq_rpop: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> c2 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w2
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> rule_rpop e1 = rule_rpop e2"
  apply(subgoal_tac "prefix (parserHF_conf_fixed c) (rule_rpop e1)")
   prefer 2
   apply(rule step_which_turns_fixed_unextendable_exceeds_fixed)
         apply(force)
        apply(force)
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "prefix (parserHF_conf_fixed c) (rule_rpop e2)")
   prefer 2
   apply(rule step_which_turns_fixed_unextendable_exceeds_fixed)
         apply(force)
        apply(force)
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "suffix (rule_rpop e1) [parser_bottom G]")
   prefer 2
   apply(rule step_which_turns_fixed_unextendable_has_bottom_as_suffix)
         apply(force)
        apply(force)
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "suffix (rule_rpop e2) [parser_bottom G]")
   prefer 2
   apply(rule step_which_turns_fixed_unextendable_has_bottom_as_suffix)
         apply(force)
        apply(force)
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "w2 = butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) (parser_bottom G)")
   apply(subgoal_tac "w2 = butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e2)) (parser_bottom G)")
    apply(clarsimp)
    apply(subgoal_tac "(drop (length (parserHF_conf_fixed c)) (rule_rpop e2)) = (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) ")
     apply(clarsimp)
     apply(rule equal_prefix_removal)
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply(rule_tac
      X="parser_bottom G"
      in equal_suffix_removal1)
      apply(simp add: prefix_def suffix_def)
      apply(clarsimp)
      apply(rename_tac ca caa cb cc "cd" ce)(*strict*)
      apply(case_tac "length (parserHF_conf_fixed c) - length ce")
       apply(rename_tac ca caa cb cc "cd" ce)(*strict*)
       apply(clarsimp)
      apply(rename_tac ca caa cb cc "cd" ce nat)(*strict*)
      apply(clarsimp)
      apply(simp add: parserHF_step_relation_def)
      apply(clarsimp)
      apply(rename_tac ca caa cb cc "cd" ce nat x xa)(*strict*)
      apply(simp add: prefix_def suffix_def)
      apply (metis Suc_length append_Nil2 dropPrecise drop_0 drop_all drop_eq_Nil le0 length_drop not_less_eq_eq)
     apply(simp add: prefix_def suffix_def)
     apply(clarsimp)
     apply(rename_tac ca caa cb cc "cd" ce)(*strict*)
     apply(case_tac "length (parserHF_conf_fixed c) - length cd")
      apply(rename_tac ca caa cb cc "cd" ce)(*strict*)
      apply(clarsimp)
     apply(rename_tac ca caa cb cc "cd" ce nat)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHF_step_relation_def)
     apply(clarsimp)
     apply(rename_tac ca caa cb cc "cd" ce nat x xa)(*strict*)
     apply(simp add: prefix_def suffix_def)
     apply (metis Suc_length append_Nil2 dropPrecise drop_0 drop_all drop_eq_Nil le0 length_drop not_less_eq_eq)
    apply(force)
   apply(rule parserHF_prefix_closureise_history_modification)
          apply(force)
         apply(force)
        prefer 2
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule parserHF_prefix_closureise_history_modification)
         apply(force)
        apply(force)
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma parserHF_equal_history_extension_and_turning_nonextendable_implies_eq_rpop_prime: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> c2 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w2
  \<Longrightarrow> w2 \<noteq> []
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> rule_rpop e1 = rule_rpop e2"
  apply(subgoal_tac "prefix (parserHF_conf_fixed c) (rule_rpop e1)")
   prefer 2
   apply(rule step_which_modifies_history_exceeds_fixed)
        apply(force)
       apply(force)
      prefer 2
      apply(force)
     apply(force)+
  apply(subgoal_tac "prefix (parserHF_conf_fixed c) (rule_rpop e2)")
   prefer 2
   apply(rule step_which_modifies_history_exceeds_fixed)
        apply(force)
       apply(force)
      prefer 2
      apply(force)
     apply(force)+
  apply(subgoal_tac "\<not> suffix (rule_rpop e1) [parser_bottom G]")
   prefer 2
   apply(rule step_which_not_turns_fixed_unextendable_has_not_bottom_as_suffix)
        apply(force)
       apply(force)
      prefer 2
      apply(force)
     apply(force)+
  apply(subgoal_tac "\<not> suffix (rule_rpop e2) [parser_bottom G]")
   prefer 2
   apply(rule step_which_not_turns_fixed_unextendable_has_not_bottom_as_suffix)
        apply(force)
       apply(force)
      prefer 2
      apply(force)
     apply(force)+
  apply(subgoal_tac "w2 = butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) (parser_bottom G)")
   apply(subgoal_tac "w2 = butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e2)) (parser_bottom G)")
    apply(clarsimp)
    apply(subgoal_tac "(drop (length (parserHF_conf_fixed c)) (rule_rpop e2)) = (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) ")
     apply(clarsimp)
     apply(rule_tac
      v="parserHF_conf_fixed c"
      in equal_prefix_removal)
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply(rule_tac
      t="drop (length (parserHF_conf_fixed c)) (rule_rpop e2)"
      and s="butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e2)) (parser_bottom G)"
      in ssubst)
     apply (metis butlast_if_match_reduces drop_prefix_closureise parser_inst_AX_extend_unfixed_scheduler_preserves_unfixed_scheduler_extendable prefix_def suffix_def)
    apply(rule_tac
      t="drop (length (parserHF_conf_fixed c)) (rule_rpop e1)"
      and s="butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) (parser_bottom G)"
      in ssubst)
     apply (metis butlast_if_match_reduces drop_prefix_closureise parser_inst_AX_extend_unfixed_scheduler_preserves_unfixed_scheduler_extendable prefix_def suffix_def)
    apply(force)
   apply(rule parserHF_prefix_closureise_history_modification_prime)
          apply(force)
         apply(force)
        prefer 2
        apply(force)
       apply(force)+
  apply(rule parserHF_prefix_closureise_history_modification_prime)
         apply(force)
        apply(force)
       prefer 2
       apply(force)
      apply(force)+
  done

lemma parserHF_extendable_and_not_dollar_bottom_then_extendable: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> rule_rpop e1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]"
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(simp add: prefix_def suffix_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x ca caa k w xb)(*strict*)
    apply(case_tac "drop (length (rule_rpop e1)) (parserHF_conf_fixed c)")
     apply(rename_tac x ca caa k w xb)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "caa=[]")
      apply(rename_tac x ca caa k w xb)(*strict*)
      apply(clarsimp)
      apply(rename_tac x ca k w xb)(*strict*)
      apply(erule_tac
      x="xb@ca"
      in allE)
      apply(force)
     apply(rename_tac x ca caa k w xb)(*strict*)
     apply (metis mutual_prefix_implies_equality2 prefix_def self_append_conv)
    apply(rename_tac x ca caa k w xb a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. drop (length (rule_rpop e1)) (parserHF_conf_fixed c) = w' @ [x']")
     apply(rename_tac x ca caa k w xb a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac x ca caa k w xb a list)(*strict*)
    apply(thin_tac "drop (length (rule_rpop e1)) (parserHF_conf_fixed c) = a # list")
    apply(clarsimp)
    apply(rename_tac x ca k w xb w')(*strict*)
    apply (metis append_Cons append_Nil2 concat_asso drop_append2 eq_Nil_appendI last_snoc)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac x ca caa)(*strict*)
   apply(case_tac "drop (length (rule_rpop e1)) (parserHF_conf_fixed c)")
    apply(rename_tac x ca caa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "caa=[]")
     apply(rename_tac x ca caa)(*strict*)
     apply(clarsimp)
     apply(rename_tac x ca)(*strict*)
     apply(simp add: prefix_def suffix_def valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac x ca k w xb)(*strict*)
     apply(erule_tac
      x="xb@ca"
      in allE)
     apply(force)
    apply(rename_tac x ca caa)(*strict*)
    apply (metis valid_parser_step_label_not_parser_bottom_random_insertion rotate_simps)
   apply(rename_tac x ca caa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. drop (length (rule_rpop e1)) (parserHF_conf_fixed c) = w' @ [x']")
    apply(rename_tac x ca caa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x ca caa a list)(*strict*)
   apply(thin_tac "drop (length (rule_rpop e1)) (parserHF_conf_fixed c) = a # list")
   apply(clarsimp)
   apply(rename_tac x ca w')(*strict*)
   apply (metis list.simps(3) prefix_append prefix_drop_none rotate1_is_Nil_conv rotate_simps)
  apply(simp add: valid_parser_def parserHF_step_relation_def)
  done

lemma parserHF_extendable_and_not_dollar_bottom_then_extendable_rev: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> rule_rpop e1 \<sqsupseteq> [parser_bottom G]"
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(erule disjE)
    apply(rename_tac x)(*strict*)
    apply(simp add: prefix_def suffix_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x ca caa k w xb xa)(*strict*)
    apply(case_tac "drop (length (rule_rpop e1)) (parserHF_conf_fixed c)")
     apply(rename_tac x ca caa k w xb xa)(*strict*)
     apply(clarsimp)
     apply(erule_tac
      x="xa"
      and P="\<lambda>xa. rule_rpush e1 \<noteq> xa @ [parser_bottom G]"
      in allE)
     apply(force)
    apply(rename_tac x ca caa k w xb xa a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. drop (length (rule_rpop e1)) (parserHF_conf_fixed c) = w' @ [x']")
     apply(rename_tac x ca caa k w xb xa a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac x ca caa k w xb xa a list)(*strict*)
    apply(thin_tac "drop (length (rule_rpop e1)) (parserHF_conf_fixed c) = a # list")
    apply(clarsimp)
    apply(rename_tac x ca caa k w xb xa w' x')(*strict*)
    apply(subgoal_tac "caa=[]")
     apply(rename_tac x ca caa k w xb xa w' x')(*strict*)
     apply(clarsimp)
     apply(rename_tac x ca k w xb xa w' x')(*strict*)
     apply(erule_tac
      x="ca"
      in allE)
     apply(force)
    apply(rename_tac x ca caa k w xb xa w' x')(*strict*)
    apply(simp add: parserHF_configurations_def)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac x ca caa)(*strict*)
   apply(case_tac "drop (length (rule_rpop e1)) (parserHF_conf_fixed c)")
    apply(rename_tac x ca caa)(*strict*)
    apply(clarsimp)
    apply(simp add: prefix_def suffix_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x ca caa k w xb xc)(*strict*)
    apply(erule_tac
      x="xc"
      and P="\<lambda>xc. rule_rpush e1 \<noteq> xc @ [parser_bottom G]"
      in allE)
    apply(force)
   apply(rename_tac x ca caa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. drop (length (rule_rpop e1)) (parserHF_conf_fixed c) = w' @ [x']")
    apply(rename_tac x ca caa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x ca caa a list)(*strict*)
   apply(thin_tac "drop (length (rule_rpop e1)) (parserHF_conf_fixed c) = a # list")
   apply(clarsimp)
   apply(rename_tac x ca caa w' x')(*strict*)
   apply (metis Suc_neq_Zero drop_eq_Nil drop_length_append length_Suc list.size(3))
  apply(simp add: valid_parser_def parserHF_step_relation_def)
  done

lemma parserHF_history_modification_exists: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w
  \<Longrightarrow> \<not> rule_rpop e2 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> length (rule_rpop e2) \<le> length (parserHF_conf_fixed c)
  \<Longrightarrow> w \<noteq> []"
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(simp add: parserHF_step_relation_def valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac k w xa xb)(*strict*)
   apply(erule disjE)
    apply(rename_tac k w xa xb)(*strict*)
    apply(simp add: prefix_def suffix_def)
    apply(clarsimp)
    apply(rename_tac k w xa xb ca)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac k w xa xb ca)(*strict*)
     apply(clarsimp)
     apply (metis List.length_take append_length_inc kPrefix_def)
    apply(rename_tac k w xa xb ca nat)(*strict*)
    apply(force)
   apply(rename_tac k w xa xb)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac k w xa xb ca)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac k w xa xb ca)(*strict*)
    apply(clarsimp)
    apply (metis List.length_take butlast_if_match_direct2_prime in_set_takeD kPrefix_def not_in_diff take_all_length)
   apply(rename_tac k w xa xb ca nat)(*strict*)
   apply(force)
  apply(simp add: parserHF_step_relation_def valid_parser_def)
  done

lemma parserHF_step_preserved_under_context_switch_with_minimal_requirements: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> c' \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> c2 \<in> parserHF_configurations G
  \<Longrightarrow> parserHFS_step_relation G c' e1 c1'
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w
  \<Longrightarrow> parserHFvHFS_Lin2BraConf c' = c
  \<Longrightarrow> \<exists>c2'. parserHFS_step_relation G c' e2 c2'"
  apply(rule parserHFS_minimal_step_prefix_closureondition)
      apply(force)
     apply(simp add: parserHF_step_relation_def)
    apply(force)
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa xb xc y)(*strict*)
   apply(simp add: suffix_def prefix_def parserHFvHFS_Lin2BraConf_def)
   apply(clarsimp)
   apply(rename_tac x xa xc y)(*strict*)
   apply(metis)
  apply(subgoal_tac "\<exists>x. rule_rpop e1 = x @ (rule_rpush e1)")
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e1")
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac k wa xa)(*strict*)
    apply(metis)
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(subgoal_tac "\<exists>x. rule_rpop e2 = x @ (rule_rpush e2)")
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x k wa xb)(*strict*)
    apply(metis)
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(case_tac "parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]")
   apply(subgoal_tac "rule_rpop e1 = rule_rpop e2")
    prefer 2
    apply(rule parserHF_equal_history_extension_and_turning_nonextendable_implies_eq_rpop)
              apply(force)
             prefer 4
             apply(force)
            prefer 4
            apply(force)
           apply (metis)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa xb xc y)(*strict*)
   apply(simp add: prefix_def)
  apply(subgoal_tac "length (butlast_if_match (rule_rpop e2) (parser_bottom G)) \<le> length (butlast_if_match (rule_rpop e1) (parser_bottom G)) \<or> length (butlast_if_match (rule_rpop e1) (parser_bottom G)) \<le> length (butlast_if_match (rule_rpop e2) (parser_bottom G))")
   prefer 2
   apply(force)
  apply(subgoal_tac "\<not> rule_rpop e2 \<sqsupseteq> [parser_bottom G]")
   apply(erule disjE)
    apply(subgoal_tac "prefix (butlast_if_match (rule_rpop e2)(parser_bottom G)) (butlast_if_match (rule_rpop e1)(parser_bottom G))")
     prefer 2
     apply(rule_tac
      w="butlast_if_match (parserHF_conf_fixed c)(parser_bottom G) @ w@[parser_bottom G]"
      in prefix_common_max)
       apply(rule_tac
      w="w"
      and v="[parser_bottom G]"
      in parserHF_rpop_prefix_closureeeds_fixed_append_history_mod)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(rule_tac
      w="w"
      and v="[parser_bottom G]"
      in parserHF_rpop_prefix_closureeeds_fixed_append_history_mod)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(rule_tac
      y="butlast_if_match (rule_rpop e1) (parser_bottom G)"
      in prefix_transitive)
     apply(rule_tac
      t="rule_rpop e2"
      and s="butlast_if_match (rule_rpop e2) (parser_bottom G)"
      in ssubst)
      apply (metis butlast_if_match_reduces suffix_def)
     apply(force)
    apply(rule_tac
      y="rule_rpop e1"
      in prefix_transitive)
     apply (metis butlast_if_match_prefix)
    apply (metis parserHFS_get_scheduler_def parserHFS_step_relation_def prefix_def)
   apply(subgoal_tac "prefix (butlast_if_match (rule_rpop e1) (parser_bottom G)) (butlast_if_match (rule_rpop e2) (parser_bottom G))")
    prefer 2
    apply(rule_tac
      w="butlast_if_match (parserHF_conf_fixed c)(parser_bottom G) @ w@[parser_bottom G]"
      in prefix_common_max)
      apply(rule_tac
      w="w"
      and v="[parser_bottom G]"
      in parserHF_rpop_prefix_closureeeds_fixed_append_history_mod)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(rule_tac
      w="w"
      and v="[parser_bottom G]"
      in parserHF_rpop_prefix_closureeeds_fixed_append_history_mod)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(case_tac "\<not> rule_rpop e1 \<sqsupseteq> [parser_bottom G]")
    apply(case_tac "length (rule_rpop e2) \<le> length (parserHF_conf_fixed c)")
     apply(rule_tac
      y="parserHF_conf_fixed c"
      in prefix_transitive)
      apply(simp add: parserHF_step_relation_def)
      apply(erule conjE)+
      apply(erule_tac
      P="rule_rpop e2 \<sqsubseteq> parserHF_conf_fixed c"
      in disjE)
       apply(force)
      apply(simp add: prefix_def)
      apply (metis append_Nil2 dropPrecise drop_eq_Nil)
     apply(rule_tac
      t="parserHF_conf_fixed c"
      and s="parserHFS_conf_fixed c'"
      in ssubst)
      apply(simp add: parserHFvHFS_Lin2BraConf_def)
      apply(clarsimp)
     apply(simp add: parserHFS_configurations_def)
     apply(clarsimp)
    apply(subgoal_tac "w\<noteq>[]")
     apply(subgoal_tac "rule_rpop e1 = rule_rpop e2")
      prefer 2
      apply(rule parserHF_equal_history_extension_and_turning_nonextendable_implies_eq_rpop_prime)
                 apply(force)
                prefer 4
                apply(force)
               prefer 4
               apply(force)
              apply (metis)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(rule parserHF_extendable_and_not_dollar_bottom_then_extendable)
          apply(force)
         prefer 2
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(rename_tac x xa)(*strict*)
     apply(simp add: parserHF_step_relation_def)
     apply(clarsimp)
     apply(rename_tac x xa xb xc)(*strict*)
     apply(simp add: prefix_def)
     apply (metis concat_asso parserHFS_step_relation_def)
    apply(rule_tac
      ?e2.0="e2"
      in parserHF_history_modification_exists)
         apply(force)
        prefer 2
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   prefer 2
   apply(rule parserHF_extendable_and_not_dollar_bottom_then_extendable_rev)
       apply(force)
      prefer 2
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>x. rule_rpop e1 = x @ [parser_bottom G]")
   prefer 2
   apply(simp add: suffix_def)
  apply(erule exE)+
  apply(rename_tac x xa xb)(*strict*)
  apply(subgoal_tac "prefix xb (rule_rpop e2)")
   apply(rename_tac x xa xb)(*strict*)
   prefer 2
   apply(subgoal_tac "butlast_if_match (rule_rpop e2) (parser_bottom G) = rule_rpop e2")
    apply(rename_tac x xa xb)(*strict*)
    prefer 2
    apply (metis butlast_if_match_reduces suffix_def)
   apply(rename_tac x xa xb)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac x xa c ca)(*strict*)
   apply(subgoal_tac "butlast_if_match (ca @ [parser_bottom G]) (parser_bottom G)=ca")
    apply(rename_tac x xa c ca)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct)
   apply(rename_tac x xa c ca)(*strict*)
   apply(clarsimp)
   apply(thin_tac "butlast_if_match (ca @ [parser_bottom G]) (parser_bottom G) = ca")
   apply(force)
  apply(rename_tac x xa xb)(*strict*)
  apply(subgoal_tac "\<exists>x. xb @ x = rule_rpop e2")
   apply(rename_tac x xa xb)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
  apply(rename_tac x xa xb)(*strict*)
  apply(erule exE)+
  apply(rename_tac x xa xb xc)(*strict*)
  apply(case_tac xc)
   apply(rename_tac x xa xb xc)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac x xa c)(*strict*)
   apply(simp add: parserHF_step_relation_def parserHFvHFS_Lin2BraConf_def parserHF_configurations_def)
   apply(clarsimp)
   apply(rename_tac x xa c xb xc)(*strict*)
   apply (metis Cons_eq_appendI append_assoc append_self_conv2 parserHFS_step_relation_def)
  apply(rename_tac x xa xb xc a list)(*strict*)
  apply(subgoal_tac "xc\<noteq>[]")
   apply(rename_tac x xa xb xc a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xa xb xc a list)(*strict*)
  apply(thin_tac "xc=a#list")
  apply(subgoal_tac "False")
   apply(rename_tac x xa xb xc a list)(*strict*)
   apply(force)
  apply(rename_tac x xa xb xc a list)(*strict*)
  apply(subgoal_tac "length (parserHF_conf_fixed c) \<le> length xb")
   apply(rename_tac x xa xb xc a list)(*strict*)
   apply(subgoal_tac "xb=rule_rpop e2")
    apply(rename_tac x xa xb xc a list)(*strict*)
    apply(force)
   apply(rename_tac x xa xb xc a list)(*strict*)
   apply(rule_tac
      t="xb"
      and s="parserHF_conf_fixed c @ drop (length (parserHF_conf_fixed c)) xb"
      in ssubst)
    apply(rename_tac x xa xb xc a list)(*strict*)
    defer
    apply(rule_tac
      t="drop (length (parserHF_conf_fixed c)) xb"
      and s="butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) (parser_bottom G)"
      in subst)
     apply(rename_tac x xa xb xc a list)(*strict*)
     apply(rule butlast_if_match_direct)
     apply (metis drop_distrib_append)
    apply(rename_tac x xa xb xc a list)(*strict*)
    apply(rule_tac
      t="butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e1)) (parser_bottom G)"
      and s="w"
      in subst)
     apply(rename_tac x xa xb xc a list)(*strict*)
     apply(rule parserHF_prefix_closureise_history_modification)
            apply(rename_tac x xa xb xc a list)(*strict*)
            apply(force)
           apply(rename_tac x xa xb xc a list)(*strict*)
           apply(force)
          apply(rename_tac x xa xb xc a list)(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac x xa xb xc a list)(*strict*)
         apply(force)+
      apply(rename_tac x xa xb xc a list)(*strict*)
      apply(simp add: parserHF_step_relation_def parserHF_configurations_def parserHFvHFS_Lin2BraConf_def)
      apply(rename_tac x xa xb xc)(*strict*)
      apply(clarsimp)
      apply(rename_tac x xa xb xc xd xe)(*strict*)
      apply(simp add: prefix_def suffix_def)
      apply(clarsimp)
      apply(rename_tac x xa xc xd xe c ca cb cc "cd" ce cf)(*strict*)
      apply (metis ConsApp concat_asso set_bi_append set_subset_in)
     apply(rename_tac x xa xb xc a list)(*strict*)
     apply(force)
    apply(rename_tac x xa xb xc a list)(*strict*)
    apply(rule_tac
      t="rule_rpop e2"
      and s="parserHF_conf_fixed c @ drop (length (parserHF_conf_fixed c)) (rule_rpop e2)"
      in ssubst)
     apply(rename_tac x xa xb xc a list)(*strict*)
     defer
     apply(rule_tac
      t="drop (length (parserHF_conf_fixed c)) (rule_rpop e2)"
      and s="butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e2)) (parser_bottom G)"
      in subst)
      apply(rename_tac x xa xb xc a list)(*strict*)
      apply(rule_tac
      t="butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e2)) (parser_bottom G)"
      and s="(drop (length (parserHF_conf_fixed c)) (butlast_if_match (rule_rpop e2) (parser_bottom G)))"
      in ssubst)
       apply(rename_tac x xa xb xc a list)(*strict*)
       apply (metis butlast_if_match_pull_out drop_distrib_append)
      apply(rename_tac x xa xb xc a list)(*strict*)
      apply (metis butlast_if_match_reduces suffix_def)
     apply(rename_tac x xa xb xc a list)(*strict*)
     apply(rule_tac
      t="butlast_if_match (drop (length (parserHF_conf_fixed c)) (rule_rpop e2)) (parser_bottom G)"
      and s="w"
      in subst)
      apply(rename_tac x xa xb xc a list)(*strict*)
      defer
      apply(force)
     apply(rename_tac x xa xb xc a list)(*strict*)
     apply(rule_tac
      t="xb"
      and s="butlast_if_match (rule_rpop e1) (parser_bottom G)"
      in ssubst)
      apply(rename_tac x xa xb xc a list)(*strict*)
      apply (metis butlast_if_match_direct)
     apply(rename_tac x xa xb xc a list)(*strict*)
     apply(rule step_which_almost_modifies_history_exceeds_fixed)
          apply(rename_tac x xa xb xc a list)(*strict*)
          apply(force)
         apply(rename_tac x xa xb xc a list)(*strict*)
         apply(force)
        apply(rename_tac x xa xb xc a list)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac x xa xb xc a list)(*strict*)
       apply(force)
      apply(rename_tac x xa xb xc a list)(*strict*)
      apply(force)
     apply(rename_tac x xa xb xc a list)(*strict*)
     apply(force)
    apply(rename_tac x xa xb xc a list)(*strict*)
    apply (metis dropPrecise parserHF_step_relation_def prefix_transitive prefix_common_max prefix_def)
   apply(rename_tac x xa xb xc a list)(*strict*)
   apply (metis dropPrecise parserHF_step_relation_def prefix_transitive prefix_common_max prefix_def)
  apply(rename_tac x xa xb xc a list)(*strict*)
  apply(rule parserHF_prefix_closureise_history_modification_prime)
         apply(rename_tac x xa xb xc a list)(*strict*)
         apply(force)
        apply(rename_tac x xa xb xc a list)(*strict*)
        apply(force)
       apply(rename_tac x xa xb xc a list)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac x xa xb xc a list)(*strict*)
      apply(force)+
   apply(rename_tac x xa xb xc a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xa xb xc a list)(*strict*)
  apply (metis (no_types, hide_lams) parserHF_step_relation_def mutual_prefix_implies_equality2 prefix_transitive prefix_def)
  done

lemma parserHFS2HF_FEdetermHist_hlp1: "
  valid_parser G
  \<Longrightarrow> \<forall>c\<in> parserHFS.get_accessible_configurations G. \<forall>c1 c2 e1 e2. parserHFS_step_relation G c e1 c1 \<and> parserHFS_step_relation G c e2 c2 \<longrightarrow> e1 = e2
  \<Longrightarrow> parserHF.derivation_initial G d
  \<Longrightarrow> get_configuration (d n) = Some c
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w2
  \<Longrightarrow> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> e1 = e2"
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option)(*strict*)
  apply(subgoal_tac "c \<in> parserHF_configurations G")
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in parserHF.belongs_configurations)
    apply(rename_tac option)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac option)(*strict*)
   apply (metis parserHF.derivation_initial_belongs)
  apply(rename_tac option)(*strict*)
  apply(subgoal_tac "c1 \<in> parserHF_configurations G")
   apply(rename_tac option)(*strict*)
   prefer 2
   apply (metis parserHF.AX_step_relation_preserves_belongsC)
  apply(rename_tac option)(*strict*)
  apply(subgoal_tac "c2 \<in> parserHF_configurations G")
   apply(rename_tac option)(*strict*)
   prefer 2
   apply (metis parserHF.AX_step_relation_preserves_belongsC)
  apply(rename_tac option)(*strict*)
  apply(subgoal_tac "parserHFS.derivation_initial G (parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n))")
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(simp add: parserHFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac option)(*strict*)
    apply(rule parserHF_vs_parserHFS.Bra2LinDer_preserves_derivation)
       apply(rename_tac option)(*strict*)
       apply(force)
      apply(rename_tac option)(*strict*)
      apply(rule parserHF.derivation_append_preserves_derivation)
        apply(rename_tac option)(*strict*)
        apply (metis parserHF.derivation_initial_is_derivation)
       apply(rename_tac option)(*strict*)
       apply(rule parserHF.der2_is_derivation)
       apply(force)
      apply(rename_tac option)(*strict*)
      apply(clarsimp)
      apply(simp add: der2_def)
     apply(rename_tac option)(*strict*)
     apply(rule parserHF.derivation_append_preserves_belongs)
       apply(rename_tac option)(*strict*)
       apply(force)
      apply(rename_tac option)(*strict*)
      apply (metis parserHF.derivation_initial_belongs)
     apply(rename_tac option)(*strict*)
     apply(rule parserHF.derivation_append_preserves_derivation)
       apply(rename_tac option)(*strict*)
       apply (metis parserHF.derivation_initial_is_derivation)
      apply(rename_tac option)(*strict*)
      apply(rule parserHF.der2_is_derivation)
      apply(force)
     apply(rename_tac option)(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def)
    apply(rename_tac option)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option)(*strict*)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(rename_tac option)(*strict*)
    prefer 2
    apply (metis parserHF.derivation_initial_is_derivation parserHF.some_position_has_details_at_0)
   apply(rename_tac option)(*strict*)
   apply(clarsimp)
   apply(rename_tac option ca)(*strict*)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) 0")
    apply(rename_tac option ca)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option ca a)(*strict*)
   apply(case_tac a)
   apply(rename_tac option ca a optiona b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option ca optiona b)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
   apply(rule_tac
      t="b"
      and s="parserHFvHFS_Bra2LinConf ca (parserHF_vs_parserHFS.Bra2LinDer' G (\<lambda>x. if x \<le> n then d x else if x - n = 0 then Some (pair None c) else if x - n = Suc 0 then Some (pair (Some e1) c1) else None) (Suc n) 0 @ (if parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed c1 else parserHF_conf_fixed c1 @ [parser_bottom G]))"
      in ssubst)
    apply(rename_tac option ca optiona b)(*strict*)
    apply(force)
   apply(rename_tac option ca optiona b)(*strict*)
   apply(rule parserHF_vs_parserHFS.AX_Bra2LinConf_preserves_initiality)
     apply(rename_tac option ca optiona b)(*strict*)
     apply(force)
    apply(rename_tac option ca optiona b)(*strict*)
    apply(subgoal_tac " parserHF_vs_parserHFS.Bra2LinDer' SSG (derivation_append d (der2 c e1 c1) n) (Suc n) 0 \<in> parser_scheduler_fragments SSG" for SSG)
     apply(rename_tac option ca optiona b)(*strict*)
     prefer 2
     apply(rule parserHF_vs_parserHFS.Bra2LinDer_prime_closed)
         apply(rename_tac option ca optiona b)(*strict*)
         apply(force)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(rule parserHF.derivation_append_preserves_derivation)
          apply(rename_tac option ca optiona b)(*strict*)
          apply (metis parserHF.derivation_initial_is_derivation)
         apply(rename_tac option ca optiona b)(*strict*)
         apply(rule parserHF.der2_is_derivation)
         apply(force)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(clarsimp)
        apply(rename_tac option ca)(*strict*)
        apply(simp add: der2_def)
       apply(rename_tac option ca optiona b)(*strict*)
       apply (rule parserHF.derivation_initial_belongs)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(force)
       apply(rename_tac option ca optiona b)(*strict*)
       apply(rule parserHF.derivation_append_preserves_derivation_initial)
         apply(rename_tac option ca optiona b)(*strict*)
         apply(force)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(force)
       apply(rename_tac option ca optiona b)(*strict*)
       apply(rule parserHF.derivation_append_preserves_derivation)
         apply(rename_tac option ca optiona b)(*strict*)
         apply (metis parserHF.derivation_initial_is_derivation)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(rule parserHF.der2_is_derivation)
        apply(force)
       apply(rename_tac option ca optiona b)(*strict*)
       apply(clarsimp)
       apply(rename_tac option ca)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac option ca optiona b)(*strict*)
      apply(simp add: derivation_append_def der2_def)
     apply(rename_tac option ca optiona b)(*strict*)
     apply(force)
    apply(rename_tac option ca optiona b)(*strict*)
    apply(simp add: parser_scheduler_fragments_def parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac option ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac option ca)(*strict*)
     apply(clarsimp)
     apply(simp add: suffix_def)
     apply(clarsimp)
     apply(rename_tac option ca caa)(*strict*)
     apply(simp add: derivation_append_def der2_def)
     apply(simp add: parserHF_configurations_def)
     apply(clarsimp)
    apply(rename_tac option ca)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def der2_def)
    apply(simp add: parserHF_configurations_def)
    apply(clarsimp)
    apply(rename_tac option c f fb h l la lb w)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac option ca optiona b)(*strict*)
   apply(simp add: parserHF.derivation_initial_def)
  apply(rename_tac option)(*strict*)
  apply(erule_tac
      x="the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n))"
      in ballE)
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(simp add: parserHFS.get_accessible_configurations_def)
   apply(subgoal_tac "False")
    apply(rename_tac option)(*strict*)
    apply(force)
   apply(rename_tac option)(*strict*)
   apply(erule_tac
      x="parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n)"
      in allE)
   apply(rename_tac option)(*strict*)
   apply(erule_tac
      P="parserHFS.derivation_initial G (parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n))"
      in impE)
    apply(rename_tac option)(*strict*)
    apply(force)
   apply(rename_tac option)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
    apply(rename_tac option)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac option a optiona b)(*strict*)
   apply(clarsimp)
  apply(rename_tac option)(*strict*)
  apply(erule_tac
      x="the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) (Suc n)))"
      in allE)
  apply(erule_tac
      x="THE c2. parserHFS_step_relation G (the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n))) e2 c2"
      in allE)
  apply(rename_tac option)(*strict*)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule_tac
      Q="e1 = e2"
      in impE)
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac option)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac option)(*strict*)
   apply(rule_tac
      d="parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n)"
      and n="n"
      and ?e1.0="option"
      in parserHFS.position_change_due_to_step_relation)
     apply(rename_tac option)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac option)(*strict*)
    apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
     apply(rename_tac option)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac option a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac option a optiona b)(*strict*)
    apply(simp add: get_configuration_def)
    apply(clarsimp)
    apply(rename_tac option optiona b)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option)(*strict*)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) (Suc n)")
    apply(rename_tac option)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac option a optiona b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac option optiona b)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac option)(*strict*)
  apply(rule HOL.theI')
  apply(rule parserHFS_unique_step)
   apply(rename_tac option)(*strict*)
   apply(force)
  apply(rename_tac option)(*strict*)
  apply(rule parserHF_step_preserved_under_context_switch_with_minimal_requirements)
              apply(rename_tac option)(*strict*)
              apply(force)
             apply(rename_tac option)(*strict*)
             prefer 3
             apply(force)
            apply(rename_tac option)(*strict*)
            apply(force)
           apply(rename_tac option)(*strict*)
           prefer 6
           apply(force)
          apply(rename_tac option)(*strict*)
          prefer 4
          apply(force)
         apply(rename_tac option)(*strict*)
         prefer 4
         apply(force)
        apply(rename_tac option)(*strict*)
        apply(force)
       apply(rename_tac option)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac option)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac option)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac option)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
    apply(rename_tac option)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option a)(*strict*)
   apply(case_tac a)
   apply(rename_tac option a optiona b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option optiona b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: parserHFvHFS_Lin2BraConf_def)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
   apply(rename_tac optiona)(*strict*)
   apply(rule conjI)
    apply(rename_tac optiona)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer'_def)
    apply(subgoal_tac "nat_seq n n=[n]")
     apply(rename_tac optiona)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "nat_seq (Suc n) n=[]")
      apply(rename_tac optiona)(*strict*)
      apply(clarsimp)
      apply(simp add: parserHFvHFS_Bra2LinStep_def)
      apply(simp add: parserHFvHFS_Bra2LinConf_def)
     apply(rename_tac optiona)(*strict*)
     apply (metis lessI nat_seqEmpty)
    apply(rename_tac optiona)(*strict*)
    apply (metis natUptTo_n_n)
   apply(rename_tac optiona)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer'_def)
   apply(subgoal_tac "nat_seq n n=[n]")
    apply(rename_tac optiona)(*strict*)
    apply(subgoal_tac "nat_seq (Suc n) n=[]")
     apply(rename_tac optiona)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHFvHFS_Bra2LinStep_def)
     apply(simp add: parserHFvHFS_Bra2LinConf_def)
    apply(rename_tac optiona)(*strict*)
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac optiona)(*strict*)
   apply (metis natUptTo_n_n)
  apply(rename_tac option)(*strict*)
  apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
   apply(rename_tac option)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac option a)(*strict*)
  apply(case_tac a)
  apply(rename_tac option a optiona b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option optiona b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule parserHFS.belongs_configurations)
   apply(rename_tac option optiona b)(*strict*)
   apply(rule parserHFS.derivation_initial_belongs)
    apply(rename_tac option optiona b)(*strict*)
    apply(force)
   apply(rename_tac option optiona b)(*strict*)
   apply(force)
  apply(rename_tac option optiona b)(*strict*)
  apply(force)
  done

lemma not_extendable_implies_pop_prefix_closureeeds_fixed: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> rule_rpop e2 \<sqsubseteq> parserHF_conf_fixed c"
  apply(simp add: parserHF_configurations_def parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac f h x)(*strict*)
  apply(simp add: suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x c ca cb)(*strict*)
  apply(subgoal_tac "\<exists>x. rule_rpop e2= x @ (rule_rpush e2)")
   apply(rename_tac x c ca cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac x c ca cb xa)(*strict*)
   apply(subgoal_tac "butlast_if_match (c @ [parser_bottom G]) (parser_bottom G)=c")
    apply(rename_tac x c ca cb xa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "cb=[]")
     apply(rename_tac x c ca cb xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac x c ca cb xa)(*strict*)
    apply(subgoal_tac "valid_parser_step_label G e2")
     apply(rename_tac x c ca cb xa)(*strict*)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac x c ca cb xa k w)(*strict*)
     apply(simp add: kPrefix_def)
     apply(case_tac "k-length w")
      apply(rename_tac x c ca cb xa k w)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "parser_bottom G \<in> set w")
       apply(rename_tac x c ca cb xa k w)(*strict*)
       apply(force)
      apply(rename_tac x c ca cb xa k w)(*strict*)
      apply (metis kPrefix_def take_reflects_mem)
     apply(rename_tac x c ca cb xa k w nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac x c ca cb xa k w nat xb)(*strict*)
     apply(case_tac cb)
      apply(rename_tac x c ca cb xa k w nat xb)(*strict*)
      apply(clarsimp)
     apply(rename_tac x c ca cb xa k w nat xb a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
      apply(rename_tac x c ca cb xa k w nat xb a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac x c ca cb xa k w nat xb a list)(*strict*)
     apply(thin_tac "cb = a # list")
     apply(clarsimp)
    apply(rename_tac x c ca cb xa)(*strict*)
    apply(simp add: valid_parser_def)
   apply(rename_tac x c ca cb xa)(*strict*)
   apply (metis butlast_if_match_direct)
  apply(rename_tac x c ca cb)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac x c ca cb)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x c ca cb k w xb)(*strict*)
   apply(rule_tac
      x="xb"
      in exI)
   apply(force)
  apply(rename_tac x c ca cb)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma parserHF_step_preserved_under_context_switch_with_minimal_requirements2: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> c' \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> c2 \<in> parserHF_configurations G
  \<Longrightarrow> parserHFS_step_relation G c' e1 c1'
  \<Longrightarrow> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c
  \<Longrightarrow> parserHFvHFS_Lin2BraConf c' = c
  \<Longrightarrow> \<exists>c2'. parserHFS_step_relation G c' e2 c2'"
  apply(rule parserHFS_minimal_step_prefix_closureondition)
      apply(force)
     apply(simp add: parserHF_step_relation_def)
    apply(force)
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa xb xc y)(*strict*)
   apply(simp add: suffix_def prefix_def parserHFvHFS_Lin2BraConf_def)
   apply(clarsimp)
   apply(rename_tac x xa xc y c)(*strict*)
   apply(metis)
  apply(subgoal_tac "\<exists>x. rule_rpop e1 = x @ (rule_rpush e1)")
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e1")
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac k w xa)(*strict*)
    apply(metis)
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(subgoal_tac "\<exists>x. rule_rpop e2 = x @ (rule_rpush e2)")
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x k w xb)(*strict*)
    apply(metis)
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(rule_tac
      y="parserHFS_conf_fixed c'"
      in prefix_transitive)
   apply(rule_tac
      t="parserHFS_conf_fixed c'"
      and s="parserHF_conf_fixed c"
      in ssubst)
    apply(simp add: parserHF_step_relation_def parserHFvHFS_Lin2BraConf_def parserHF_configurations_def)
    apply(clarsimp)
   apply(rule not_extendable_implies_pop_prefix_closureeeds_fixed)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: parserHFS_configurations_def parserHFvHFS_Lin2BraConf_def)
  apply(clarsimp)
  done

lemma parserHFS2HF_FEdetermHist_hlp2: "
  valid_parser G
  \<Longrightarrow> \<forall>c\<in> parserHFS.get_accessible_configurations G. \<forall>c1 c2 e1 e2. parserHFS_step_relation G c e1 c1 \<and> parserHFS_step_relation G c e2 c2 \<longrightarrow> e1 = e2
  \<Longrightarrow> parserHF.derivation_initial G d
  \<Longrightarrow> get_configuration (d n) = Some c
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c
  \<Longrightarrow> e1 = e2"
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option)(*strict*)
  apply(subgoal_tac "c \<in> parserHF_configurations G")
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in parserHF.belongs_configurations)
    apply(rename_tac option)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac option)(*strict*)
   apply (metis parserHF.derivation_initial_belongs)
  apply(rename_tac option)(*strict*)
  apply(subgoal_tac "c1 \<in> parserHF_configurations G")
   apply(rename_tac option)(*strict*)
   prefer 2
   apply (metis parserHF.AX_step_relation_preserves_belongsC)
  apply(rename_tac option)(*strict*)
  apply(subgoal_tac "c2 \<in> parserHF_configurations G")
   apply(rename_tac option)(*strict*)
   prefer 2
   apply (metis parserHF.AX_step_relation_preserves_belongsC)
  apply(rename_tac option)(*strict*)
  apply(subgoal_tac "parserHFS.derivation_initial G (parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n))")
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(simp add: parserHFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac option)(*strict*)
    apply(rule parserHF_vs_parserHFS.Bra2LinDer_preserves_derivation)
       apply(rename_tac option)(*strict*)
       apply(force)
      apply(rename_tac option)(*strict*)
      apply(rule parserHF.derivation_append_preserves_derivation)
        apply(rename_tac option)(*strict*)
        apply (metis parserHF.derivation_initial_is_derivation)
       apply(rename_tac option)(*strict*)
       apply(rule parserHF.der2_is_derivation)
       apply(force)
      apply(rename_tac option)(*strict*)
      apply(clarsimp)
      apply(simp add: der2_def)
     apply(rename_tac option)(*strict*)
     apply(rule parserHF.derivation_append_preserves_belongs)
       apply(rename_tac option)(*strict*)
       apply(force)
      apply(rename_tac option)(*strict*)
      apply (metis parserHF.derivation_initial_belongs)
     apply(rename_tac option)(*strict*)
     apply(rule parserHF.derivation_append_preserves_derivation)
       apply(rename_tac option)(*strict*)
       apply (metis parserHF.derivation_initial_is_derivation)
      apply(rename_tac option)(*strict*)
      apply(rule parserHF.der2_is_derivation)
      apply(force)
     apply(rename_tac option)(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def)
    apply(rename_tac option)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option)(*strict*)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(rename_tac option)(*strict*)
    prefer 2
    apply (metis parserHF.derivation_initial_is_derivation parserHF.some_position_has_details_at_0)
   apply(rename_tac option)(*strict*)
   apply(clarsimp)
   apply(rename_tac option ca)(*strict*)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) 0")
    apply(rename_tac option ca)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option ca a)(*strict*)
   apply(case_tac a)
   apply(rename_tac option ca a optiona b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option ca optiona b)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
   apply(rule_tac
      t="b"
      and s="parserHFvHFS_Bra2LinConf ca (parserHF_vs_parserHFS.Bra2LinDer' G (\<lambda>x. if x \<le> n then d x else if x - n = 0 then Some (pair None c) else if x - n = Suc 0 then Some (pair (Some e1) c1) else None) (Suc n) 0 @ (if parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed c1 else parserHF_conf_fixed c1 @ [parser_bottom G]))"
      in ssubst)
    apply(rename_tac option ca optiona b)(*strict*)
    apply(force)
   apply(rename_tac option ca optiona b)(*strict*)
   apply(rule parserHF_vs_parserHFS.AX_Bra2LinConf_preserves_initiality)
     apply(rename_tac option ca optiona b)(*strict*)
     apply(force)
    apply(rename_tac option ca optiona b)(*strict*)
    apply(subgoal_tac " parserHF_vs_parserHFS.Bra2LinDer' SSG (derivation_append d (der2 c e1 c1) n) (Suc n) 0 \<in> parser_scheduler_fragments SSG" for SSG)
     apply(rename_tac option ca optiona b)(*strict*)
     prefer 2
     apply(rule parserHF_vs_parserHFS.Bra2LinDer_prime_closed)
         apply(rename_tac option ca optiona b)(*strict*)
         apply(force)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(rule parserHF.derivation_append_preserves_derivation)
          apply(rename_tac option ca optiona b)(*strict*)
          apply (metis parserHF.derivation_initial_is_derivation)
         apply(rename_tac option ca optiona b)(*strict*)
         apply(rule parserHF.der2_is_derivation)
         apply(force)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(clarsimp)
        apply(rename_tac option ca)(*strict*)
        apply(simp add: der2_def)
       apply(rename_tac option ca optiona b)(*strict*)
       apply (rule parserHF.derivation_initial_belongs)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(force)
       apply(rename_tac option ca optiona b)(*strict*)
       apply(rule parserHF.derivation_append_preserves_derivation_initial)
         apply(rename_tac option ca optiona b)(*strict*)
         apply(force)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(force)
       apply(rename_tac option ca optiona b)(*strict*)
       apply(rule parserHF.derivation_append_preserves_derivation)
         apply(rename_tac option ca optiona b)(*strict*)
         apply (metis parserHF.derivation_initial_is_derivation)
        apply(rename_tac option ca optiona b)(*strict*)
        apply(rule parserHF.der2_is_derivation)
        apply(force)
       apply(rename_tac option ca optiona b)(*strict*)
       apply(clarsimp)
       apply(rename_tac option ca)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac option ca optiona b)(*strict*)
      apply(simp add: derivation_append_def der2_def)
     apply(rename_tac option ca optiona b)(*strict*)
     apply(force)
    apply(rename_tac option ca optiona b)(*strict*)
    apply(simp add: parser_scheduler_fragments_def parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac option ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac option ca)(*strict*)
     apply(clarsimp)
     apply(simp add: suffix_def)
     apply(clarsimp)
     apply(rename_tac option ca caa cb)(*strict*)
     apply(simp add: derivation_append_def der2_def)
     apply(simp add: parserHF_configurations_def)
     apply(clarsimp)
    apply(rename_tac option ca)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def der2_def)
    apply(simp add: parserHF_configurations_def)
    apply(clarsimp)
    apply(rename_tac option c f fb h l la lb w)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac option ca optiona b)(*strict*)
   apply(simp add: parserHF.derivation_initial_def)
  apply(rename_tac option)(*strict*)
  apply(erule_tac
      x="the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n))"
      in ballE)
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(simp add: parserHFS.get_accessible_configurations_def)
   apply(subgoal_tac "False")
    apply(rename_tac option)(*strict*)
    apply(force)
   apply(rename_tac option)(*strict*)
   apply(erule_tac
      x="parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n)"
      in allE)
   apply(rename_tac option)(*strict*)
   apply(erule impE)
    apply(rename_tac option)(*strict*)
    apply(force)
   apply(rename_tac option)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
    apply(rename_tac option)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac option a optiona b)(*strict*)
   apply(clarsimp)
  apply(rename_tac option)(*strict*)
  apply(erule_tac
      x="the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) (Suc n)))"
      in allE)
  apply(erule_tac
      x="THE c2. parserHFS_step_relation G (the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n))) e2 c2"
      in allE)
  apply(rename_tac option)(*strict*)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule impE)
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac option)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac option)(*strict*)
   apply(rule_tac
      d="parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n)"
      and n="n"
      and ?e1.0="option"
      in parserHFS.position_change_due_to_step_relation)
     apply(rename_tac option)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac option)(*strict*)
    apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
     apply(rename_tac option)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac option a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac option a optiona b)(*strict*)
    apply(simp add: get_configuration_def)
    apply(clarsimp)
    apply(rename_tac option optiona b)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option)(*strict*)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) (Suc n)")
    apply(rename_tac option)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac option a optiona b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac option optiona b)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac option)(*strict*)
  apply(rule HOL.theI')
  apply(rule parserHFS_unique_step)
   apply(rename_tac option)(*strict*)
   apply(force)
  apply(rename_tac option)(*strict*)
  apply(rule parserHF_step_preserved_under_context_switch_with_minimal_requirements2)
             apply(rename_tac option)(*strict*)
             apply(force)
            apply(rename_tac option)(*strict*)
            prefer 3
            apply(force)
           apply(rename_tac option)(*strict*)
           apply(force)
          apply(rename_tac option)(*strict*)
          apply(force)
         apply(rename_tac option)(*strict*)
         prefer 2
         apply(force)
        apply(rename_tac option)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac option)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac option)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac option)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac option)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac option)(*strict*)
   prefer 2
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
    apply(rename_tac option)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac option a)(*strict*)
   apply(case_tac a)
   apply(rename_tac option a optiona b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option optiona b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: parserHFvHFS_Lin2BraConf_def)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
   apply(rename_tac optiona)(*strict*)
   apply(rule conjI)
    apply(rename_tac optiona)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer'_def)
    apply(subgoal_tac "nat_seq n n=[n]")
     apply(rename_tac optiona)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "nat_seq (Suc n) n=[]")
      apply(rename_tac optiona)(*strict*)
      apply(clarsimp)
      apply(simp add: parserHFvHFS_Bra2LinStep_def)
      apply(simp add: parserHFvHFS_Bra2LinConf_def)
     apply(rename_tac optiona)(*strict*)
     apply (metis lessI nat_seqEmpty)
    apply(rename_tac optiona)(*strict*)
    apply (metis natUptTo_n_n)
   apply(rename_tac optiona)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer'_def)
   apply(subgoal_tac "nat_seq n n=[n]")
    apply(rename_tac optiona)(*strict*)
    apply(subgoal_tac "nat_seq (Suc n) n=[]")
     apply(rename_tac optiona)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHFvHFS_Bra2LinStep_def)
     apply(simp add: parserHFvHFS_Bra2LinConf_def)
    apply(rename_tac optiona)(*strict*)
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac optiona)(*strict*)
   apply (metis natUptTo_n_n)
  apply(rename_tac option)(*strict*)
  apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
   apply(rename_tac option)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac option a)(*strict*)
  apply(case_tac a)
  apply(rename_tac option a optiona b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option optiona b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule parserHFS.belongs_configurations)
   apply(rename_tac option optiona b)(*strict*)
   apply(rule parserHFS.derivation_initial_belongs)
    apply(rename_tac option optiona b)(*strict*)
    apply(force)
   apply(rename_tac option optiona b)(*strict*)
   apply(force)
  apply(rename_tac option optiona b)(*strict*)
  apply(force)
  done

lemma no_history_extension_if_already_unextendable: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w2
  \<Longrightarrow> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> w2 = []"
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(simp add: parserHF_step_relation_def prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac ca x)(*strict*)
   apply(erule disjE)
    apply(rename_tac ca x)(*strict*)
    prefer 2
    apply(clarsimp)
    apply(rename_tac ca x caa)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac ca x caa k w xb)(*strict*)
    apply(subgoal_tac "caa=[]")
     apply(rename_tac ca x caa k w xb)(*strict*)
     apply(clarsimp)
     apply(rename_tac ca x k w xb)(*strict*)
     apply (metis Suc_length butlast_if_match_length_le)
    apply(rename_tac ca x caa k w xb)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac ca x caa k w xb)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<in> set w")
      apply(rename_tac ca x caa k w xb)(*strict*)
      apply(force)
     apply(rename_tac ca x caa k w xb)(*strict*)
     apply (metis kPrefix_def take_reflects_mem)
    apply(rename_tac ca x caa k w xb nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac ca x caa k w xb nat xa)(*strict*)
    apply(case_tac caa)
     apply(rename_tac ca x caa k w xb nat xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac ca x caa k w xb nat xa a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. caa = w' @ [x']")
     apply(rename_tac ca x caa k w xb nat xa a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac ca x caa k w xb nat xa a list)(*strict*)
    apply(thin_tac "caa = a # list")
    apply(clarsimp)
   apply(rename_tac ca x)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca x caa)(*strict*)
   apply (metis append_length_inc drop_entire_butlast_if_match drop_eq_Nil length_Suc)
  apply(simp add: valid_parser_def parserHF_step_relation_def)
  done

lemma parserHF_history_in_parser_events_no_bottom: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> set (parserHF_conf_history c) \<subseteq> parser_events G - {parser_bottom G}"
  apply(simp add: parserHF_configurations_def)
  apply(clarsimp)
  apply(rename_tac x f h l)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x f l c)(*strict*)
  apply(erule disjE)
   apply(rename_tac x f l c)(*strict*)
   apply(force)
  apply(rename_tac x f l c)(*strict*)
  apply(force)
  done

lemma parserHF_fixed_in_parser_events: "
  valid_parser G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> set (parserHF_conf_fixed c1) \<subseteq> parser_events G"
  apply(simp add: parserHF_configurations_def prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x f l c)(*strict*)
  apply (metis subsetD)
  done

lemma parserHF_not_bottom_end_then_no_bottom: "
  valid_parser G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parser_bottom G \<notin> set (parserHF_conf_fixed c1)"
  apply(simp add: parserHF_configurations_def prefix_def suffix_def)
  apply(clarsimp)
  done

lemma parserHF_step_not_turning_nonextendable_has_pop_prefix_closureeeding_fixed_appended_with_history_extension: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> c2 \<in> parserHF_configurations G
  \<Longrightarrow> \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w1
  \<Longrightarrow> \<exists>x. rule_rpop e2 = x @ rule_rpush e2
  \<Longrightarrow> rule_rpop e2 \<sqsubseteq> (parserHF_conf_fixed c @ w1)"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa ca)(*strict*)
   apply(rule_tac
      t="drop (length (parserHF_conf_fixed c)) (butlast_if_match (x @ rule_rpush e2) (parser_bottom G))"
      and s="[]"
      in ssubst)
    apply(rename_tac x xa ca)(*strict*)
    apply (metis append_assoc drop_entire_butlast_if_match drop_length_append)
   apply(rename_tac x xa ca)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_configurations_def)
   apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xa ca)(*strict*)
  apply(subgoal_tac "drop (length x + length (rule_rpush e2)) (parserHF_conf_fixed c)=[]")
   apply(rename_tac x xa ca)(*strict*)
   prefer 2
   apply (metis length_append prefix_append prefix_drop_none)
  apply(rename_tac x xa ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (butlast_if_match (x @ rule_rpush e2) (parser_bottom G))=butlast_if_match ca (parser_bottom G)")
   apply(rename_tac x xa ca)(*strict*)
   prefer 2
   apply (metis drop_butlast_if_match_distrib)
  apply(rename_tac x xa ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "butlast_if_match ca (parser_bottom G) = ca")
   apply(rename_tac x xa ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac x xa ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: butlast_if_match_def)
  apply(rename_tac x xa ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac x xa ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xa ca a list)(*strict*)
  apply(thin_tac "ca = a # list")
  apply(clarsimp)
  apply(rename_tac x xa w' x')(*strict*)
  apply(simp add: suffix_def)
  apply(case_tac "x'=parser_bottom G")
   apply(rename_tac x xa w' x')(*strict*)
   prefer 2
   apply (metis butlast_if_match_direct2 rotate_simps)
  apply(rename_tac x xa w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa w')(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac x xa w')(*strict*)
   apply(force)
  apply(rename_tac x xa w')(*strict*)
  apply(thin_tac "length (parserHF_conf_fixed c) \<le> length x + length (rule_rpush e2)")
  apply(subgoal_tac "butlast_if_match (w' @ [parser_bottom G]) (parser_bottom G)=w'")
   apply(rename_tac x xa w')(*strict*)
   prefer 2
   apply (metis butlast_if_match_direct insert_Nil)
  apply(rename_tac x xa w')(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(thin_tac "butlast_if_match (drop (length (parserHF_conf_fixed c)) (butlast_if_match (x @ rule_rpush e2) (parser_bottom G)) @ [parser_bottom G]) (parser_bottom G) = drop (length (parserHF_conf_fixed c)) (butlast_if_match (x @ rule_rpush e2) (parser_bottom G))")
  apply(rename_tac x xa)(*strict*)
  apply(case_tac "rule_rpush e2")
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(rename_tac x xa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_rpush e2 = w' @ [x']")
    apply(rename_tac x xa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x xa a list)(*strict*)
   apply(thin_tac "rule_rpush e2 = a # list")
   apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac xa)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac xa k w)(*strict*)
   apply(erule_tac
      x="parserHF_conf_fixed c @ drop (length (parserHF_conf_fixed c)) (butlast_if_match (kPrefix k (w @ [parser_bottom G])) (parser_bottom G))"
      in allE)
   apply(rename_tac xa k w)(*strict*)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma parserHF_step_fixed_with_modification_prefix_closureeeds_pop: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w1 @ w2
  \<Longrightarrow> w2 \<noteq> []
  \<Longrightarrow> \<exists>x. rule_rpop e1 = x @ rule_rpush e1
  \<Longrightarrow> (parserHF_conf_fixed c @ w1) \<sqsubseteq> rule_rpop e1"
  apply(subgoal_tac "valid_parser_step_label G e1")
   prefer 2
   apply(simp add: parserHF_step_relation_def)
   apply(simp add: valid_parser_def)
  apply(rule_tac
      y="parserHF_conf_fixed c @ w1 @ w2"
      in prefix_transitive)
   apply(simp add: prefix_def)
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa ca)(*strict*)
   apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (butlast_if_match (x @ rule_rpush e1) (parser_bottom G)) = []")
    apply(rename_tac x xa ca)(*strict*)
    prefer 2
    apply (metis concat_asso drop_entire_butlast_if_match drop_length_append)
   apply(rename_tac x xa ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xa ca)(*strict*)
  apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (butlast_if_match (x @ rule_rpush e1) (parser_bottom G)) = butlast_if_match ca (parser_bottom G)")
   apply(rename_tac x xa ca)(*strict*)
   prefer 2
   apply (metis drop_butlast_if_match_distrib)
  apply(rename_tac x xa ca)(*strict*)
  apply(clarsimp)
  apply(thin_tac "drop (length (parserHF_conf_fixed c)) (butlast_if_match (x @ rule_rpush e1) (parser_bottom G)) = butlast_if_match ca (parser_bottom G)")
  apply(rename_tac x xa ca)(*strict*)
  apply(case_tac "suffix ca [parser_bottom G]")
   apply(rename_tac x xa ca)(*strict*)
   apply(rule_tac
      x="[parser_bottom G]"
      in exI)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply (metis butlast_if_match_direct rotate_simps)
  apply(rename_tac x xa ca)(*strict*)
  apply(simp add: suffix_def)
  apply (metis append_Nil2 append_assoc butlast_if_match_reduces)
  done

lemma parserHF_step_preserved_under_context_switch_with_minimal_requirements3: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> c' \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> c2 \<in> parserHF_configurations G
  \<Longrightarrow> parserHFS_step_relation G c' e1 c1'
  \<Longrightarrow> \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w1 @ w2
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w1
  \<Longrightarrow> w2 \<noteq> []
  \<Longrightarrow> parserHFvHFS_Lin2BraConf c' = c
  \<Longrightarrow> \<exists>c2'. parserHFS_step_relation G c' e2 c2'"
  apply(rule parserHFS_minimal_step_prefix_closureondition)
      apply(force)
     apply(simp add: parserHF_step_relation_def)
    apply(force)
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa xb xc y)(*strict*)
   apply(simp add: suffix_def prefix_def parserHFvHFS_Lin2BraConf_def)
   apply(clarsimp)
   apply(rename_tac x xa xc y)(*strict*)
   apply(metis)
  apply(subgoal_tac "\<exists>x. rule_rpop e1 = x @ (rule_rpush e1)")
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e1")
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac k w xa)(*strict*)
    apply(metis)
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(subgoal_tac "\<exists>x. rule_rpop e2 = x @ (rule_rpush e2)")
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x k w xb)(*strict*)
    apply(metis)
   apply(simp add: valid_parser_def parserHF_step_relation_def)
  apply(rule_tac
      y="rule_rpop e1"
      in prefix_transitive)
   defer
   apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def parserHFvHFS_Lin2BraConf_def prefix_def)
   apply(clarsimp)
  apply(rule_tac
      t="parserHFS_conf_fixed c'"
      and s="parserHF_conf_fixed c"
      in ssubst)
   apply(simp add: parserHF_step_relation_def parserHFvHFS_Lin2BraConf_def parserHF_configurations_def)
   apply(clarsimp)
  apply(rule_tac
      y="parserHF_conf_fixed c @ w1"
      in prefix_transitive)
   apply(rule parserHF_step_not_turning_nonextendable_has_pop_prefix_closureeeding_fixed_appended_with_history_extension)
         apply(force)
        apply(force)
       apply(force)
      apply(force)+
  apply(rule parserHF_step_fixed_with_modification_prefix_closureeeds_pop)
        apply(force)+
  done

lemma parserHFS2HF_FEdetermHist_hlp3: "
  valid_parser G
  \<Longrightarrow> parserHFS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> parserHF.derivation_initial G d
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_step_relation G c e2 c2
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ w1
  \<Longrightarrow> parserHF_conf_history c2 = parserHF_conf_history c @ w2
  \<Longrightarrow> w2 \<noteq> w1
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> c \<in> parserHF_configurations G
  \<Longrightarrow> ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w1
  \<Longrightarrow> \<not> parserHF_get_fixed_scheduler_DB G (derivation_append d (der2 c e2 c2) n) (Suc n) \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> e1 = e2"
  apply(subgoal_tac "c1 \<in> parserHF_configurations G")
   prefer 2
   apply (metis parserHF.AX_step_relation_preserves_belongsC)
  apply(subgoal_tac "c2 \<in> parserHF_configurations G")
   prefer 2
   apply (metis parserHF.AX_step_relation_preserves_belongsC)
  apply(subgoal_tac "prefix w2 w1")
   prefer 2
   apply(subgoal_tac "ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w1 = prefix w2 w1")
    apply(force)
   apply(rule order_antisym) prefer 2
    apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(subgoal_tac "w2 \<in> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}")
    apply(force)
   apply(rule_tac
      A="{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}"
      in set_mp)
    apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(clarsimp)
   apply(simp add: parser_markers_def)
   apply(rule_tac
      B="set (parserHF_conf_history c2)"
      in subset_trans)
    apply(force)
   apply(rule_tac
      B="parser_events G - {parser_bottom G}"
      in subset_trans)
    apply(rule parserHF_history_in_parser_events_no_bottom)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w1")
  apply(subgoal_tac "\<exists>x. w2@x=w1 \<and> x\<noteq>[]")
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(thin_tac "prefix w2 w1")
  apply(thin_tac "w2\<noteq>w1")
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rename_tac w1)
  apply(rename_tac w1)(*strict*)
  apply(subgoal_tac "\<not> suffix (parserHF_conf_fixed c2) [parser_bottom G]")
   apply(rename_tac w1)(*strict*)
   prefer 2
   apply(simp add: parserHF_get_fixed_scheduler_DB_def derivation_append_def der2_def get_configuration_def)
  apply(rename_tac w1)(*strict*)
  apply(thin_tac "\<not> parserHF_get_fixed_scheduler_DB G (derivation_append d (der2 c e2 c2) n) (Suc n) \<sqsupseteq> [parser_bottom G]")
  apply(rename_tac w1)(*strict*)
  apply(simp add: parserHFS.is_forward_edge_deterministic_accessible_def)
  apply(subgoal_tac "parserHFS.derivation_initial G (parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n))")
   apply(rename_tac w1)(*strict*)
   prefer 2
   apply(simp add: parserHFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac w1)(*strict*)
    apply(rule parserHF_vs_parserHFS.Bra2LinDer_preserves_derivation)
       apply(rename_tac w1)(*strict*)
       apply(force)
      apply(rename_tac w1)(*strict*)
      apply(rule parserHF.derivation_append_preserves_derivation)
        apply(rename_tac w1)(*strict*)
        apply (metis parserHF.derivation_initial_is_derivation)
       apply(rename_tac w1)(*strict*)
       apply(rule parserHF.der2_is_derivation)
       apply(force)
      apply(rename_tac w1)(*strict*)
      apply(clarsimp)
      apply(simp add: der2_def)
     apply(rename_tac w1)(*strict*)
     apply(rule parserHF.derivation_append_preserves_belongs)
       apply(rename_tac w1)(*strict*)
       apply(force)
      apply(rename_tac w1)(*strict*)
      apply (metis parserHF.derivation_initial_belongs)
     apply(rename_tac w1)(*strict*)
     apply(rule parserHF.derivation_append_preserves_derivation)
       apply(rename_tac w1)(*strict*)
       apply (metis parserHF.derivation_initial_is_derivation)
      apply(rename_tac w1)(*strict*)
      apply(rule parserHF.der2_is_derivation)
      apply(force)
     apply(rename_tac w1)(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def)
    apply(rename_tac w1)(*strict*)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac w1)(*strict*)
   apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
    apply(rename_tac w1)(*strict*)
    prefer 2
    apply (metis parserHF.derivation_initial_is_derivation parserHF.some_position_has_details_at_0)
   apply(rename_tac w1)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 ca)(*strict*)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) 0")
    apply(rename_tac w1 ca)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac w1 ca a)(*strict*)
   apply(case_tac a)
   apply(rename_tac w1 ca a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 ca option b)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
   apply(rule_tac
      t="b"
      and s="parserHFvHFS_Bra2LinConf ca (parserHF_vs_parserHFS.Bra2LinDer' G (\<lambda>x. if x \<le> n then d x else if x - n = 0 then Some (pair None c) else if x - n = Suc 0 then Some (pair (Some e1) c1) else None) (Suc n) 0 @ (if parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] then parserHF_conf_fixed c1 else parserHF_conf_fixed c1 @ [parser_bottom G]))"
      in ssubst)
    apply(rename_tac w1 ca option b)(*strict*)
    apply(force)
   apply(rename_tac w1 ca option b)(*strict*)
   apply(rule parserHF_vs_parserHFS.AX_Bra2LinConf_preserves_initiality)
     apply(rename_tac w1 ca option b)(*strict*)
     apply(force)
    apply(rename_tac w1 ca option b)(*strict*)
    apply(subgoal_tac " parserHF_vs_parserHFS.Bra2LinDer' SSG (derivation_append d (der2 c e1 c1) n) (Suc n) 0 \<in> parser_scheduler_fragments SSG" for SSG)
     apply(rename_tac w1 ca option b)(*strict*)
     prefer 2
     apply(rule parserHF_vs_parserHFS.Bra2LinDer_prime_closed)
         apply(rename_tac w1 ca option b)(*strict*)
         apply(force)
        apply(rename_tac w1 ca option b)(*strict*)
        apply(rule parserHF.derivation_append_preserves_derivation)
          apply(rename_tac w1 ca option b)(*strict*)
          apply (metis parserHF.derivation_initial_is_derivation)
         apply(rename_tac w1 ca option b)(*strict*)
         apply(rule parserHF.der2_is_derivation)
         apply(force)
        apply(rename_tac w1 ca option b)(*strict*)
        apply(clarsimp)
        apply(rename_tac w1 ca)(*strict*)
        apply(simp add: der2_def)
       apply(rename_tac w1 ca option b)(*strict*)
       apply (rule parserHF.derivation_initial_belongs)
        apply(rename_tac w1 ca option b)(*strict*)
        apply(force)
       apply(rename_tac w1 ca option b)(*strict*)
       apply(rule parserHF.derivation_append_preserves_derivation_initial)
         apply(rename_tac w1 ca option b)(*strict*)
         apply(force)
        apply(rename_tac w1 ca option b)(*strict*)
        apply(force)
       apply(rename_tac w1 ca option b)(*strict*)
       apply(rule parserHF.derivation_append_preserves_derivation)
         apply(rename_tac w1 ca option b)(*strict*)
         apply (metis parserHF.derivation_initial_is_derivation)
        apply(rename_tac w1 ca option b)(*strict*)
        apply(rule parserHF.der2_is_derivation)
        apply(force)
       apply(rename_tac w1 ca option b)(*strict*)
       apply(clarsimp)
       apply(rename_tac w1 ca)(*strict*)
       apply(simp add: der2_def)
      apply(rename_tac w1 ca option b)(*strict*)
      apply(simp add: derivation_append_def der2_def)
     apply(rename_tac w1 ca option b)(*strict*)
     apply(force)
    apply(rename_tac w1 ca option b)(*strict*)
    apply(simp add: parser_scheduler_fragments_def parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac w1 ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac w1 ca)(*strict*)
     apply(clarsimp)
     apply(simp add: suffix_def)
     apply(clarsimp)
     apply(rename_tac w1 ca caa)(*strict*)
     apply(simp add: derivation_append_def der2_def)
     apply(simp add: parserHF_configurations_def)
     apply(clarsimp)
    apply(rename_tac w1 ca)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_append_def der2_def)
    apply(simp add: parserHF_configurations_def)
    apply(clarsimp)
    apply(rename_tac w1 c f fb h l la lb w)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac w1 ca option b)(*strict*)
   apply(simp add: parserHF.derivation_initial_def)
  apply(rename_tac w1)(*strict*)
  apply(erule_tac
      x="the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n))"
      in ballE)
   apply(rename_tac w1)(*strict*)
   prefer 2
   apply(simp add: parserHFS.get_accessible_configurations_def)
   apply(subgoal_tac "False")
    apply(rename_tac w1)(*strict*)
    apply(force)
   apply(rename_tac w1)(*strict*)
   apply(erule_tac
      x="parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n)"
      in allE)
   apply(rename_tac w1)(*strict*)
   apply(erule impE)
    apply(rename_tac w1)(*strict*)
    apply(force)
   apply(rename_tac w1)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
    apply(rename_tac w1)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac w1 a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac a)
   apply(rename_tac w1 a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac w1)(*strict*)
  apply(erule_tac
      x="the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) (Suc n)))"
      in allE)
  apply(erule_tac
      x="THE c2. parserHFS_step_relation G (the(get_configuration(parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n))) e2 c2"
      in allE)
  apply(rename_tac w1)(*strict*)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule impE)
   apply(rename_tac w1)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w1)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac w1)(*strict*)
   apply(rule_tac
      d="parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n)"
      and n="n"
      and ?e1.0="e"
      in parserHFS.position_change_due_to_step_relation)
     apply(rename_tac w1)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac w1)(*strict*)
    apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
     apply(rename_tac w1)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
     apply(simp add: derivation_append_def der2_def)
    apply(rename_tac w1 a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac w1 a option b)(*strict*)
    apply(simp add: get_configuration_def)
    apply(clarsimp)
    apply(rename_tac w1 option b)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac w1)(*strict*)
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) (Suc n)")
    apply(rename_tac w1)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac w1 a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac w1 a option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac w1 option b)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac w1)(*strict*)
  apply(rule HOL.theI')
  apply(rule parserHFS_unique_step)
   apply(rename_tac w1)(*strict*)
   apply(force)
  apply(rename_tac w1)(*strict*)
  apply(rule parserHF_step_preserved_under_context_switch_with_minimal_requirements3)
              apply(rename_tac w1)(*strict*)
              apply(force)
             apply(rename_tac w1)(*strict*)
             prefer 3
             apply(force)
            apply(rename_tac w1)(*strict*)
            apply(force)
           apply(rename_tac w1)(*strict*)
           apply(force)
          apply(rename_tac w1)(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac w1)(*strict*)
         prefer 2
         apply(force)
        apply(rename_tac w1)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac w1)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac w1)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac w1)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w1)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w1)(*strict*)
   prefer 2
   apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
    apply(rename_tac w1)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
    apply(simp add: derivation_append_def der2_def)
   apply(rename_tac w1 a)(*strict*)
   apply(case_tac a)
   apply(rename_tac w1 a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w1 option b)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: parserHFvHFS_Lin2BraConf_def)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
   apply(clarsimp)
   apply(rename_tac w1)(*strict*)
   apply(rule conjI)
    apply(rename_tac w1)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer'_def)
    apply(subgoal_tac "nat_seq n n=[n]")
     apply(rename_tac w1)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "nat_seq (Suc n) n=[]")
      apply(rename_tac w1)(*strict*)
      apply(clarsimp)
      apply(simp add: parserHFvHFS_Bra2LinStep_def)
      apply(simp add: parserHFvHFS_Bra2LinConf_def)
     apply(rename_tac w1)(*strict*)
     apply (metis lessI nat_seqEmpty)
    apply(rename_tac w1)(*strict*)
    apply (metis natUptTo_n_n)
   apply(rename_tac w1)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer'_def)
   apply(subgoal_tac "nat_seq n n=[n]")
    apply(rename_tac w1)(*strict*)
    apply(subgoal_tac "nat_seq (Suc n) n=[]")
     apply(rename_tac w1)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHFvHFS_Bra2LinStep_def)
     apply(simp add: parserHFvHFS_Bra2LinConf_def)
    apply(rename_tac w1)(*strict*)
    apply (metis lessI nat_seqEmpty)
   apply(rename_tac w1)(*strict*)
   apply (metis natUptTo_n_n)
  apply(rename_tac w1)(*strict*)
  apply(case_tac "parserHF_vs_parserHFS.Bra2LinDer G (derivation_append d (der2 c e1 c1) n) (Suc n) n")
   apply(rename_tac w1)(*strict*)
   apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def)
   apply(simp add: derivation_append_def der2_def)
  apply(rename_tac w1 a)(*strict*)
  apply(case_tac a)
  apply(rename_tac w1 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rule parserHFS.belongs_configurations)
   apply(rename_tac w1 option b)(*strict*)
   apply(rule parserHFS.derivation_initial_belongs)
    apply(rename_tac w1 option b)(*strict*)
    apply(force)
   apply(rename_tac w1 option b)(*strict*)
   apply(force)
  apply(rename_tac w1 option b)(*strict*)
  apply(force)
  done

lemma parserHFS_step_relation_slim_step_intro2: "
  valid_parser G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> e \<in> parser_step_labels G
  \<Longrightarrow> suffix (parserHFS_conf_stack c1) (rule_lpop e)
  \<Longrightarrow> prefix (rule_rpop e) (parserHFS_conf_scheduler c1)
  \<Longrightarrow> \<exists>c2. parserHFS_step_relation G c1 e c2"
  apply(simp add: parserHFS_step_relation_def)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac c ca)(*strict*)
  apply(simp add: parser_step_labels_def)
  apply(rule_tac x="\<lparr>parserHFS_conf_fixed = rule_rpush e @
           drop (length (rule_rpop e)) (parserHFS_conf_fixed c1),
    parserHFS_conf_history = parserHFS_conf_history c1 @
           drop (length (parserHFS_conf_fixed c1))
            (butlast_if_match (rule_rpop e) (parser_bottom G)),
    parserHFS_conf_stack = c @ rule_lpush e,
    parserHFS_conf_scheduler = SSr\<rparr> " for SSr in exI)
  apply(clarsimp)
  apply(rule_tac x="ca" in exI)
  apply(rule conjI)
   apply(rename_tac c ca)(*strict*)
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac c ca)(*strict*)
   apply(force)
  apply(rename_tac c ca)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac c ca f h w)(*strict*)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac x="e" in ballE)
   apply(rename_tac c ca f h w)(*strict*)
   prefer 2
   apply(simp add: parser_step_labels_def)
  apply(rename_tac c ca f h w)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac c ca f w cb cc k wa xa)(*strict*)
  apply(rule_tac xs="ca" in rev_cases)
   apply(rename_tac c ca f w cb cc k wa xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac c f w cb cc k wa xa x)(*strict*)
   apply(rule_tac xs="rule_rpush e" in rev_cases)
    apply(rename_tac c f w cb cc k wa xa x)(*strict*)
    apply(clarsimp)
   apply(rename_tac c f w cb cc k wa xa x ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac c ca f w cb cc k wa xa ys y)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_extension_empty: "
  valid_parser G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> rule_rpop e1 = x @ rule_rpush e1
  \<Longrightarrow> prefix (rule_rpop e1) (parserHF_conf_fixed c)
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ hf2
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> hf2=[]"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(case_tac c1)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHF_conf_fixedaa parserHF_conf_historyaa parserHF_conf_stackaa)(*strict*)
  apply(case_tac e1)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHF_conf_fixedaa parserHF_conf_historyaa parserHF_conf_stackaa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac parserHF_conf_fixed rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(rename_tac f lp lpu rpu)
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac lp lpu rpu c)(*strict*)
  apply(rule_tac xs="c" in rev_cases)
   apply(rename_tac lp lpu rpu c)(*strict*)
   apply(clarsimp)
   apply(rename_tac lp lpu rpu)(*strict*)
   apply(rule_tac xs="rpu" in rev_cases)
    apply(rename_tac lp lpu rpu)(*strict*)
    apply(clarsimp)
    apply(rename_tac lp lpu)(*strict*)
    apply(rule_tac xs="x" in rev_cases)
     apply(rename_tac lp lpu)(*strict*)
     apply(clarsimp)
     apply(simp add: butlast_if_match_def)
    apply(rename_tac lp lpu ys y)(*strict*)
    apply(clarsimp)
    apply(simp add: suffix_def)
    apply(subgoal_tac "butlast_if_match (ys @ [y]) (parser_bottom G) = ys@[y]")
     apply(rename_tac lp lpu ys y)(*strict*)
     prefer 2
     apply (metis butlast_if_match_direct2)
    apply(rename_tac lp lpu ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac lp lpu rpu ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac lp lpu ys y)(*strict*)
   apply(subgoal_tac "butlast_if_match ((x@ys) @ [y]) (parser_bottom G) = (x@ys)@[y]")
    apply(rename_tac lp lpu ys y)(*strict*)
    prefer 2
    apply(rule butlast_if_match_direct2)
     apply(rename_tac lp lpu ys y)(*strict*)
     apply(force)
    apply(rename_tac lp lpu ys y)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac lp lpu ys y)(*strict*)
   apply(force)
  apply(rename_tac lp lpu rpu c ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac lp lpu rpu ys y)(*strict*)
  apply(subgoal_tac "length (butlast_if_match (x @ rpu) (parser_bottom G)) \<le> SSX" for SSX)
   apply(rename_tac lp lpu rpu ys y)(*strict*)
   prefer 2
   apply(rule butlast_if_match_length_le)
  apply(rename_tac lp lpu rpu ys y)(*strict*)
  apply(force)
  done

lemma parserHF_extension_fixed_and_pop: "
  parserHF_step_relation G c e1 c1
  \<Longrightarrow> prefix (parserHF_conf_fixed c) (rule_rpop e1) \<or> prefix (rule_rpop e1) (parserHF_conf_fixed c)"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  done

lemma parserHF_extension_notempty: "
  valid_parser G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> rule_rpop e1 = x @ rule_rpush e1
  \<Longrightarrow> parserHF_conf_fixed c @ w = rule_rpop e1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ hf2
  \<Longrightarrow> \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> w=hf2"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(case_tac c1)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHF_conf_fixedaa parserHF_conf_historyaa parserHF_conf_stackaa)(*strict*)
  apply(case_tac e1)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHF_conf_fixedaa parserHF_conf_historyaa parserHF_conf_stackaa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac parserHF_conf_fixed rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(rename_tac f lp lpu rpu)
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(case_tac "f \<sqsubseteq> x @ rpu")
   apply(rename_tac f lp lpu rpu)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac f lp lpu rpu c)(*strict*)
  apply(subgoal_tac "w=c")
   apply(rename_tac f lp lpu rpu c)(*strict*)
   prefer 2
   apply (metis drop_prefix_closureise)
  apply(rename_tac f lp lpu rpu c)(*strict*)
  apply(clarsimp)
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(subgoal_tac "drop (length x + length rpu) f = []")
   apply(rename_tac f lp lpu rpu)(*strict*)
   prefer 2
   apply(rule_tac t="length x+length rpu" and s="length (f@w)" in ssubst)
    apply(rename_tac f lp lpu rpu)(*strict*)
    apply(force)
   apply(rename_tac f lp lpu rpu)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(clarsimp)
  apply(rule_tac xs="rpu" in rev_cases)
   apply(rename_tac f lp lpu rpu)(*strict*)
   apply(clarsimp)
   apply(rename_tac f lp lpu)(*strict*)
   apply(rule_tac xs="w" in rev_cases)
    apply(rename_tac f lp lpu)(*strict*)
    apply(clarsimp)
    apply(rule_tac xs="f" in rev_cases)
     apply(rename_tac f lp lpu)(*strict*)
     apply(clarsimp)
     apply(rename_tac lp lpu)(*strict*)
     apply(simp add: butlast_if_match_def)
    apply(rename_tac f lp lpu ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac lp lpu ys y)(*strict*)
    apply(simp add: suffix_def)
    apply(rule_tac t="butlast_if_match (ys @ [y]) (parser_bottom G)" and s="ys @ [y]" in ssubst)
     apply(rename_tac lp lpu ys y)(*strict*)
     apply (metis butlast_if_match_direct2)
    apply(rename_tac lp lpu ys y)(*strict*)
    apply(force)
   apply(rename_tac f lp lpu ys y)(*strict*)
   apply(clarsimp)
   apply(case_tac "y=parser_bottom G")
    apply(rename_tac f lp lpu ys y)(*strict*)
    prefer 2
    apply(rule_tac t="butlast_if_match ((f@ys) @ [y]) (parser_bottom G)" and s="(f@ys) @ [y]" in ssubst)
     apply(rename_tac f lp lpu ys y)(*strict*)
     apply (rule butlast_if_match_direct2)
      apply(rename_tac f lp lpu ys y)(*strict*)
      apply(force)
     apply(rename_tac f lp lpu ys y)(*strict*)
     apply(force)
    apply(rename_tac f lp lpu ys y)(*strict*)
    apply(simp add: valid_parser_def)
    apply(clarsimp)
    apply(erule_tac x="\<lparr>rule_lpop = lp, rule_rpop = f @ ys @ [y], rule_lpush = lpu,
          rule_rpush = []\<rparr>" in ballE)
     apply(rename_tac f lp lpu ys y)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac f lp lpu ys y)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac f lp lpu ys y k w)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac f lp lpu ys y k w)(*strict*)
     apply(clarsimp)
     apply(rule_tac t="butlast_if_match (take k w) (parser_bottom G)" and s="take k w" in ssubst)
      apply(rename_tac f lp lpu ys y k w)(*strict*)
      apply (rule_tac v="f@ys" and y="y" in butlast_if_match_direct2)
       apply(rename_tac f lp lpu ys y k w)(*strict*)
       apply(force)
      apply(rename_tac f lp lpu ys y k w)(*strict*)
      apply(force)
     apply(rename_tac f lp lpu ys y k w)(*strict*)
     apply(rule_tac t="take k w" and s="f @ ys @ [y]" in ssubst)
      apply(rename_tac f lp lpu ys y k w)(*strict*)
      apply(force)
     apply(rename_tac f lp lpu ys y k w)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac f lp lpu ys y k w nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac f lp lpu ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac f lp lpu ys)(*strict*)
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="\<lparr>rule_lpop = lp, rule_rpop = f @ ys @ [parser_bottom G],
          rule_lpush = lpu, rule_rpush = []\<rparr>" in ballE)
    apply(rename_tac f lp lpu ys)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac f lp lpu ys)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac f lp lpu rpu ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac f lp lpu ys y)(*strict*)
  apply(simp add: suffix_def)
  apply(rule_tac t="butlast_if_match (x @ ys @ [y]) (parser_bottom G)" in ssubst)
   apply(rename_tac f lp lpu ys y)(*strict*)
   apply (rule_tac v="x @ ys" and y="y" in butlast_if_match_direct2)
    apply(rename_tac f lp lpu ys y)(*strict*)
    apply(force)
   apply(rename_tac f lp lpu ys y)(*strict*)
   apply(force)
  apply(rename_tac f lp lpu ys y)(*strict*)
  apply(rule_tac t="x@ys@[y]" and s="f @ w" in ssubst)
   apply(rename_tac f lp lpu ys y)(*strict*)
   apply(force)
  apply(rename_tac f lp lpu ys y)(*strict*)
  apply(simp (no_asm))
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step1_hlp1: "
  valid_parser G \<Longrightarrow>
    ATS.derivation_initial parserHF_initial_configurations
     parserHF_step_relation G d \<Longrightarrow>
    parserHF_step_relation G c e1 c1 \<Longrightarrow>
    parserHF_step_relation G c e2 c2 \<Longrightarrow>
    d i = Some (pair e1a c) \<Longrightarrow>
    parserHF_conf_history c1 = parserHF_conf_history c @ hf2 \<Longrightarrow>
    parserHF_conf_history c2 = parserHF_conf_history c @ hf2 @ hf1 \<Longrightarrow>
    hf1 \<noteq> [] \<Longrightarrow>
    hf1 \<in> parser_markers G \<Longrightarrow>
    hf2 \<in> parser_markers G \<Longrightarrow>
    \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
    \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
       parserHFS_conf_history = parserHF_conf_history c,
       parserHFS_conf_stack = parserHF_conf_stack c,
       parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr>
    \<in> parserHFS_configurations G \<Longrightarrow>
    parserHFS_step_relation G
     \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
        parserHFS_conf_history = parserHF_conf_history c,
        parserHFS_conf_stack = parserHF_conf_stack c,
        parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr>
     e2 \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c2,
           parserHFS_conf_history = parserHF_conf_history c @ hf2 @ hf1,
           parserHFS_conf_stack = parserHF_conf_stack c2,
           parserHFS_conf_scheduler =
             wix @ parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr> \<Longrightarrow>
    \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
    Ex (parserHFS_step_relation G
         \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
            parserHFS_conf_history = parserHF_conf_history c,
            parserHFS_conf_stack = parserHF_conf_stack c,
            parserHFS_conf_scheduler =
              wi @ parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr>
         e1)"
  apply(subgoal_tac "parserHF_conf_fixed c \<sqsubseteq>
    wi @ parserHF_conf_fixed c2 @ [parser_bottom G]")
   prefer 2
   apply(simp add: parserHFS_configurations_def)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca)(*strict*)
  apply(rule_tac parserHFS_step_relation_slim_step_intro2)
      apply(rename_tac ca)(*strict*)
      apply(force)
     apply(rename_tac ca)(*strict*)
     apply(force)
    apply(rename_tac ca)(*strict*)
    apply(simp add: parserHF_step_relation_def parser_step_labels_def)
   apply(rename_tac ca)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac ca x xa)(*strict*)
   apply(simp add: prefix_def suffix_def)
  apply(rename_tac ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ca)(*strict*)
   prefer 2
   apply(rule parserHF.AX_fixed_scheduler_extendable_translates_backwards)
      apply(rename_tac ca)(*strict*)
      apply(force)
     apply(rename_tac ca)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac ca)(*strict*)
    apply(rule_tac d="d" in parserHF.belongs_configurations)
     apply(rename_tac ca)(*strict*)
     apply(rule parserHF.derivation_initial_belongs)
      apply(rename_tac ca)(*strict*)
      apply(force)
     apply(rename_tac ca)(*strict*)
     apply(force)
    apply(rename_tac ca)(*strict*)
    apply(force)
   apply(rename_tac ca)(*strict*)
   apply(force)
  apply(rename_tac ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac ca)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="e2" in ballE)
    apply(rename_tac ca)(*strict*)
    prefer 2
    apply(simp add: parserHF_step_relation_def)
   apply(rename_tac ca)(*strict*)
   apply(force)
  apply(rename_tac ca)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(rename_tac ca)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="e1" in ballE)
    apply(rename_tac ca)(*strict*)
    prefer 2
    apply(simp add: parserHF_step_relation_def)
   apply(rename_tac ca)(*strict*)
   apply(force)
  apply(rename_tac ca)(*strict*)
  apply(subgoal_tac "(\<exists>x. x @ rule_rpush e1 = rule_rpop e1)")
   apply(rename_tac ca)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac ca)(*strict*)
  apply(subgoal_tac "(\<exists>x. x @ rule_rpush e2 = rule_rpop e2)")
   apply(rename_tac ca)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca x xa)(*strict*)
  apply(case_tac "prefix (rule_rpop e2) (parserHF_conf_fixed c)")
   apply(rename_tac ca x xa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac ca x xa)(*strict*)
    prefer 2
    apply(rule_tac ?e1.0="e2" and x="xa" in parserHF_extension_empty)
         apply(rename_tac ca x xa)(*strict*)
         apply(force)
        apply(rename_tac ca x xa)(*strict*)
        apply(force)
       apply(rename_tac ca x xa)(*strict*)
       apply(force)
      apply(rename_tac ca x xa)(*strict*)
      apply(force)
     apply(rename_tac ca x xa)(*strict*)
     apply(force)
    apply(rename_tac ca x xa)(*strict*)
    apply(force)
   apply(rename_tac ca x xa)(*strict*)
   apply(force)
  apply(rename_tac ca x xa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ca x xa)(*strict*)
   prefer 2
   apply(rule_tac ?e1.0="e2" in parserHF_extension_fixed_and_pop)
   apply(force)
  apply(rename_tac ca x xa)(*strict*)
  apply(erule disjE)
   apply(rename_tac ca x xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ca x xa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac ca x xa caa)(*strict*)
  apply(rule_tac xs="caa" in rev_cases)
   apply(rename_tac ca x xa caa)(*strict*)
   apply(force)
  apply(rename_tac ca x xa caa ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca x xa ys y)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ca x xa ys y)(*strict*)
   prefer 2
   apply(rule_tac ?e1.0="e1" in parserHF_extension_fixed_and_pop)
   apply(force)
  apply(rename_tac ca x xa ys y)(*strict*)
  apply(erule disjE)
   apply(rename_tac ca x xa ys y)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac ca x xa ys y caa)(*strict*)
   apply(rule_tac t="wi @ parserHF_conf_fixed c2 @ [parser_bottom G]" and s="parserHF_conf_fixed c @ ca" in ssubst)
    apply(rename_tac ca x xa ys y caa)(*strict*)
    apply(force)
   apply(rename_tac ca x xa ys y caa)(*strict*)
   apply(rule_tac t="parserHF_conf_fixed c" and s="rule_rpop e1 @ caa" in ssubst)
    apply(rename_tac ca x xa ys y caa)(*strict*)
    apply(force)
   apply(rename_tac ca x xa ys y caa)(*strict*)
   apply(rule_tac x="caa@ca" in exI)
   apply(simp (no_asm))
  apply(rename_tac ca x xa ys y)(*strict*)
  apply(simp add: prefix_def)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ca x xa ys y)(*strict*)
   prefer 2
   apply(rule_tac x="xa" and ?e1.0="e2" in parserHF_extension_notempty)
         apply(rename_tac ca x xa ys y)(*strict*)
         apply(force)
        apply(rename_tac ca x xa ys y)(*strict*)
        apply(force)
       apply(rename_tac ca x xa ys y)(*strict*)
       apply(force)
      apply(rename_tac ca x xa ys y)(*strict*)
      apply(force)
     apply(rename_tac ca x xa ys y)(*strict*)
     apply(force)
    apply(rename_tac ca x xa ys y)(*strict*)
    apply(force)
   apply(rename_tac ca x xa ys y)(*strict*)
   apply(force)
  apply(rename_tac ca x xa ys y)(*strict*)
  apply(rule_tac xs="hf1" in rev_cases)
   apply(rename_tac ca x xa ys y)(*strict*)
   apply(force)
  apply(rename_tac ca x xa ys y ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca x xa ysa ya caa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac ca x xa ysa ya caa)(*strict*)
   prefer 2
   apply(rule_tac ?e1.0="e1" and x="x" in parserHF_extension_notempty)
         apply(rename_tac ca x xa ysa ya caa)(*strict*)
         apply(force)
        apply(rename_tac ca x xa ysa ya caa)(*strict*)
        apply(force)
       apply(rename_tac ca x xa ysa ya caa)(*strict*)
       apply(force)
      apply(rename_tac ca x xa ysa ya caa)(*strict*)
      apply(force)
     apply(rename_tac ca x xa ysa ya caa)(*strict*)
     apply(force)
    apply(rename_tac ca x xa ysa ya caa)(*strict*)
    apply(force)
   apply(rename_tac ca x xa ysa ya caa)(*strict*)
   apply(force)
  apply(rename_tac ca x xa ysa ya caa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca x xa ysa ya)(*strict*)
  apply(thin_tac "\<forall>ca. rule_rpop e2 @ ca \<noteq> parserHF_conf_fixed c")
  apply(rule_tac xs="ca" in rev_cases)
   apply(rename_tac ca x xa ysa ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac ca x xa ysa ya ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa ysa ya ys)(*strict*)
  apply(subgoal_tac "parserHF_conf_fixed c2 = rule_rpush e2")
   apply(rename_tac x xa ysa ya ys)(*strict*)
   prefer 2
   apply(simp add: parserHF_step_relation_def)
   apply(rule_tac t="rule_rpop e2" and s="parserHF_conf_fixed c @
       drop (length (parserHF_conf_fixed c))
        (butlast_if_match (rule_rpop e2) (parser_bottom G))" in ssubst)
    apply(rename_tac x xa ysa ya ys)(*strict*)
    apply(force)
   apply(rename_tac x xa ysa ya ys)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac x xa ysa ya ys)(*strict*)
  apply(clarsimp)
  apply(rule_tac t="rule_rpop e1" and s="parserHF_conf_fixed c @ hf2" in ssubst)
   apply(rename_tac x xa ysa ya ys)(*strict*)
   apply(force)
  apply(rename_tac x xa ysa ya ys)(*strict*)
  apply(subgoal_tac "\<exists>ca. (parserHF_conf_fixed c @ hf2) @ ca =
            wi @ rule_rpush e2")
   apply(rename_tac x xa ysa ya ys)(*strict*)
   apply(erule exE)+
   apply(rename_tac x xa ysa ya ys ca)(*strict*)
   apply(rule_tac x="ca@[parser_bottom G]" in exI)
   apply(force)
  apply(rename_tac x xa ysa ya ys)(*strict*)
  apply(subgoal_tac "prefix (parserHF_conf_fixed c) wi \<or> SSX" for SSX)
   apply(rename_tac x xa ysa ya ys)(*strict*)
   prefer 2
   apply(rule_tac mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x xa ysa ya ys)(*strict*)
  apply(subgoal_tac "prefix (parserHF_conf_fixed c) xa  \<or> SSX" for SSX)
   apply(rename_tac x xa ysa ya ys)(*strict*)
   prefer 2
   apply(rule_tac b="hf2 @ ysa @ [ya]" and d="rule_rpush e2" in mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x xa ysa ya ys)(*strict*)
  apply(erule disjE)+
    apply(rename_tac x xa ysa ya ys)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x ysa ya ca caa)(*strict*)
    apply(simp add: parserHFS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac x ysa ya ca caa xa xb)(*strict*)
    apply(rule_tac xs="xb" in rev_cases)
     apply(rename_tac x ysa ya ca caa xa xb)(*strict*)
     apply(clarsimp)
    apply(rename_tac x ysa ya ca caa xa xb ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
    apply(subgoal_tac "butlast_if_match (rule_rpop e2) (parser_bottom G) = rule_rpop e2")
     apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
     prefer 2
     apply (metis Nil_is_append_conv butlast_if_match_pull_out drop_butlast_if_match_distrib not_Cons_self2)
    apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (rule_rpop e2) = caa @ rule_rpush e2")
     apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
     prefer 2
     apply (metis same_append_eq)
    apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "prefix hf2 caa \<or> SSX" for SSX)
     apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
     prefer 2
     apply(rule_tac mutual_prefix_prefix)
     apply(force)
    apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
    apply(erule disjE)
     apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac x ysa ya ca xa ys cb)(*strict*)
     apply(rule_tac t="rule_rpop e2" and s="parserHF_conf_fixed c @ hf2 @ cb @ rule_rpush e2" in ssubst)
      apply(rename_tac x ysa ya ca xa ys cb)(*strict*)
      apply(force)
     apply(rename_tac x ysa ya ca xa ys cb)(*strict*)
     apply(rule_tac t="rule_rpop e1" and s="parserHF_conf_fixed c @ hf2" in ssubst)
      apply(rename_tac x ysa ya ca xa ys cb)(*strict*)
      apply(force)
     apply(rename_tac x ysa ya ca xa ys cb)(*strict*)
     apply(rule_tac x="cb @ rule_rpush e2 @ ys" in exI)
     apply(simp (no_asm))
    apply(rename_tac x ysa ya ca caa xa ys)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x ysa ya ca caa xa ys cb)(*strict*)
    apply(rule_tac t="rule_rpop e2" and s="parserHF_conf_fixed c @ caa @ rule_rpush e2" in ssubst)
     apply(rename_tac x ysa ya ca caa xa ys cb)(*strict*)
     apply(force)
    apply(rename_tac x ysa ya ca caa xa ys cb)(*strict*)
    apply(rule_tac t="rule_rpush e2" and s="cb @ ysa @ [ya]" in ssubst)
     apply(rename_tac x ysa ya ca caa xa ys cb)(*strict*)
     apply(force)
    apply(rename_tac x ysa ya ca caa xa ys cb)(*strict*)
    apply(rule_tac t="rule_rpop e1" and s="parserHF_conf_fixed c @ caa @ cb " in ssubst)
     apply(rename_tac x ysa ya ca caa xa ys cb)(*strict*)
     apply(force)
    apply(rename_tac x ysa ya ca caa xa ys cb)(*strict*)
    apply(rule_tac x="ysa @ [ya] @ ys" in exI)
    apply(simp (no_asm))
   apply(rename_tac x xa ysa ya ys)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ca caa)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ca caa xb xc)(*strict*)
   apply(subgoal_tac "butlast_if_match (rule_rpop e2) (parser_bottom G) = rule_rpop e2")
    apply(rename_tac x xa ysa ya ca caa xb xc)(*strict*)
    prefer 2
    apply (metis Nil_is_append_conv butlast_if_match_pull_out drop_butlast_if_match_distrib not_Cons_self2)
   apply(rename_tac x xa ysa ya ca caa xb xc)(*strict*)
   apply(clarsimp)
   apply(rule_tac xs="xc" in rev_cases)
    apply(rename_tac x xa ysa ya ca caa xb xc)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xa ysa ya ca caa xb xc ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ca caa xb ys)(*strict*)
   apply(subgoal_tac "prefix (parserHF_conf_fixed c) (rule_rpop e2) \<or> SSX" for SSX)
    apply(rename_tac x xa ysa ya ca caa xb ys)(*strict*)
    prefer 2
    apply(rule_tac mutual_prefix_prefix)
    apply(force)
   apply(rename_tac x xa ysa ya ca caa xb ys)(*strict*)
   apply(erule disjE)
    apply(rename_tac x xa ysa ya ca caa xb ys)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x xa ysa ya ca caa xb ys cb)(*strict*)
    apply (metis Nil_is_append_conv drop_eq_Nil drop_length_append snoc_eq_iff_butlast)
   apply(rename_tac x xa ysa ya ca caa xb ys)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ca caa xb ys cb)(*strict*)
   apply(subgoal_tac "ca @ rule_rpush e2 = cb @ ys")
    apply(rename_tac x xa ysa ya ca caa xb ys cb)(*strict*)
    prefer 2
    apply (metis drop_append append_assoc)
   apply(rename_tac x xa ysa ya ca caa xb ys cb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "prefix ca cb \<or> SSX" for SSX)
    apply(rename_tac x xa ysa ya ca caa xb ys cb)(*strict*)
    prefer 2
    apply(rule_tac mutual_prefix_prefix)
    apply(force)
   apply(rename_tac x xa ysa ya ca caa xb ys cb)(*strict*)
   apply(erule disjE)
    apply(rename_tac x xa ysa ya ca caa xb ys cb)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x xa ysa ya ca xb cb cc)(*strict*)
    apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (rule_rpop e2) = cb")
     apply(rename_tac x xa ysa ya ca xb cb cc)(*strict*)
     prefer 2
     apply (metis same_append_eq)
    apply(rename_tac x xa ysa ya ca xb cb cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa ysa ya ca xb cc)(*strict*)
    apply(rule_tac t="rule_rpop e2" and s="parserHF_conf_fixed c @ hf2 @ ysa @ [ya]" in ssubst)
     apply(rename_tac x xa ysa ya ca xb cc)(*strict*)
     apply(force)
    apply(rename_tac x xa ysa ya ca xb cc)(*strict*)
    apply(rule_tac t="rule_rpop e1" and s="parserHF_conf_fixed c @ hf2" in ssubst)
     apply(rename_tac x xa ysa ya ca xb cc)(*strict*)
     apply(force)
    apply(rename_tac x xa ysa ya ca xb cc)(*strict*)
    apply(rule_tac x="ysa @ [ya] @ cc @ rule_rpush e2" in exI)
    apply(simp (no_asm))
   apply(rename_tac x xa ysa ya ca caa xb ys cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ca caa xb ys cc)(*strict*)
   apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (rule_rpop e2) = ca@cc")
    apply(rename_tac x xa ysa ya ca caa xb ys cc)(*strict*)
    prefer 2
    apply (metis same_append_eq)
   apply(rename_tac x xa ysa ya ca caa xb ys cc)(*strict*)
   apply(clarsimp)
   apply(thin_tac "drop (length (parserHF_conf_fixed c)) (rule_rpop e2) = ca @ cc")
   apply(thin_tac "butlast_if_match (rule_rpop e2) (parser_bottom G) = rule_rpop e2")
   apply (metis append_eq_append_conv2)
  apply(rename_tac x xa ysa ya ys)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xa ysa ya ys ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa ysa ya ys ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac x ysa ya ys ca caa)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x ysa ya ys ca caa xa xb)(*strict*)
   apply(rule_tac xs="xb" in rev_cases)
    apply(rename_tac x ysa ya ys ca caa xa xb)(*strict*)
    apply(clarsimp)
   apply(rename_tac x ysa ya ys ca caa xa xb ysb y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
   apply(subgoal_tac "butlast_if_match (rule_rpop e2) (parser_bottom G) = rule_rpop e2")
    apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
    prefer 2
    apply (metis Nil_is_append_conv butlast_if_match_pull_out drop_butlast_if_match_distrib not_Cons_self2)
   apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (rule_rpop e2) = caa @ rule_rpush e2")
    apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
    prefer 2
    apply (metis same_append_eq)
   apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "prefix hf2 caa \<or> SSX" for SSX)
    apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
    prefer 2
    apply(rule_tac mutual_prefix_prefix)
    apply(force)
   apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
   apply(erule disjE)
    apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x ysa ya ys ca xa ysb cb)(*strict*)
    apply(rule_tac t="rule_rpop e2" and s="parserHF_conf_fixed c @ hf2 @ cb @ rule_rpush e2" in ssubst)
     apply(rename_tac x ysa ya ys ca xa ysb cb)(*strict*)
     apply(force)
    apply(rename_tac x ysa ya ys ca xa ysb cb)(*strict*)
    apply(rule_tac t="rule_rpop e1" and s="parserHF_conf_fixed c @ hf2" in ssubst)
     apply(rename_tac x ysa ya ys ca xa ysb cb)(*strict*)
     apply(force)
    apply(rename_tac x ysa ya ys ca xa ysb cb)(*strict*)
    apply(rule_tac x="cb @ rule_rpush e2 @ ysb" in exI)
    apply(simp (no_asm))
   apply(rename_tac x ysa ya ys ca caa xa ysb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x ysa ya ys ca caa xa ysb cb)(*strict*)
   apply(rule_tac t="rule_rpop e2" and s="parserHF_conf_fixed c @ caa @ rule_rpush e2" in ssubst)
    apply(rename_tac x ysa ya ys ca caa xa ysb cb)(*strict*)
    apply(force)
   apply(rename_tac x ysa ya ys ca caa xa ysb cb)(*strict*)
   apply(rule_tac t="rule_rpush e2" and s="cb @ ysa @ [ya]" in ssubst)
    apply(rename_tac x ysa ya ys ca caa xa ysb cb)(*strict*)
    apply(force)
   apply(rename_tac x ysa ya ys ca caa xa ysb cb)(*strict*)
   apply(rule_tac t="rule_rpop e1" and s="parserHF_conf_fixed c @ caa @ cb " in ssubst)
    apply(rename_tac x ysa ya ys ca caa xa ysb cb)(*strict*)
    apply(force)
   apply(rename_tac x ysa ya ys ca caa xa ysb cb)(*strict*)
   apply(rule_tac x="ysa @ [ya] @ ysb" in exI)
   apply(simp (no_asm))
  apply(rename_tac x xa ysa ya ys ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa ysa ya ys ca caa)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa ysa ya ys ca caa xb xc)(*strict*)
  apply(subgoal_tac "butlast_if_match (rule_rpop e2) (parser_bottom G) = rule_rpop e2")
   apply(rename_tac x xa ysa ya ys ca caa xb xc)(*strict*)
   prefer 2
   apply (metis Nil_is_append_conv butlast_if_match_pull_out drop_butlast_if_match_distrib not_Cons_self2)
  apply(rename_tac x xa ysa ya ys ca caa xb xc)(*strict*)
  apply(clarsimp)
  apply(rule_tac xs="xc" in rev_cases)
   apply(rename_tac x xa ysa ya ys ca caa xb xc)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa ysa ya ys ca caa xb xc ysb y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa ysa ya ys ca caa xb ysb)(*strict*)
  apply(subgoal_tac "prefix (parserHF_conf_fixed c) (rule_rpop e2) \<or> SSX" for SSX)
   apply(rename_tac x xa ysa ya ys ca caa xb ysb)(*strict*)
   prefer 2
   apply(rule_tac mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x xa ysa ya ys ca caa xb ysb)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa ysa ya ys ca caa xb ysb)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ys ca caa xb ysb cb)(*strict*)
   apply (metis Nil_is_append_conv drop_eq_Nil drop_length_append snoc_eq_iff_butlast)
  apply(rename_tac x xa ysa ya ys ca caa xb ysb)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xa ysa ya ys ca caa xb ysb cb)(*strict*)
  apply(subgoal_tac "prefix wi xa \<or> SSX" for SSX)
   apply(rename_tac x xa ysa ya ys ca caa xb ysb cb)(*strict*)
   prefer 2
   apply(rule_tac b="ca" and d="caa" in mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x xa ysa ya ys ca caa xb ysb cb)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa ysa ya ys ca caa xb ysb cb)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ys ca caa xb ysb cb cc)(*strict*)
   apply(subgoal_tac "caa=cc@ca")
    apply(rename_tac x xa ysa ya ys ca caa xb ysb cb cc)(*strict*)
    prefer 2
    apply (metis same_append_eq)
   apply(rename_tac x xa ysa ya ys ca caa xb ysb cb cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ys ca xb ysb cb cc)(*strict*)
   apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (rule_rpop e2) = cb")
    apply(rename_tac x xa ysa ya ys ca xb ysb cb cc)(*strict*)
    prefer 2
    apply (metis same_append_eq)
   apply(rename_tac x xa ysa ya ys ca xb ysb cb cc)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa ysa ya ys ca xb ysb cc)(*strict*)
   apply(rule_tac t="rule_rpop e2" and s="parserHF_conf_fixed c @ hf2 @ ysa @ [ya]" in ssubst)
    apply(rename_tac x xa ysa ya ys ca xb ysb cc)(*strict*)
    apply(force)
   apply(rename_tac x xa ysa ya ys ca xb ysb cc)(*strict*)
   apply(rule_tac t="rule_rpop e1" and s="parserHF_conf_fixed c @ hf2" in ssubst)
    apply(rename_tac x xa ysa ya ys ca xb ysb cc)(*strict*)
    apply(force)
   apply(rename_tac x xa ysa ya ys ca xb ysb cc)(*strict*)
   apply(rule_tac x="ysa @ [ya] @ ysb" in exI)
   apply(simp (no_asm))
  apply(rename_tac x xa ysa ya ys ca caa xb ysb cb)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x ysa ya ys ca caa xb ysb cb cc)(*strict*)
  apply(subgoal_tac "ca=cc@caa")
   apply(rename_tac x ysa ya ys ca caa xb ysb cb cc)(*strict*)
   prefer 2
   apply (metis same_append_eq)
  apply(rename_tac x ysa ya ys ca caa xb ysb cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac x ysa ya ys ca xb ysb cb cc)(*strict*)
  apply(subgoal_tac "drop (length (parserHF_conf_fixed c)) (rule_rpop e2) = cb")
   apply(rename_tac x ysa ya ys ca xb ysb cb cc)(*strict*)
   prefer 2
   apply (metis same_append_eq)
  apply(rename_tac x ysa ya ys ca xb ysb cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac x ysa ya ys ca xb ysb cc)(*strict*)
  apply(rule_tac t="rule_rpop e2" and s="parserHF_conf_fixed c @ hf2 @ ysa @ [ya]" in ssubst)
   apply(rename_tac x ysa ya ys ca xb ysb cc)(*strict*)
   apply(force)
  apply(rename_tac x ysa ya ys ca xb ysb cc)(*strict*)
  apply(rule_tac t="rule_rpop e1" and s="parserHF_conf_fixed c @ hf2" in ssubst)
   apply(rename_tac x ysa ya ys ca xb ysb cc)(*strict*)
   apply(force)
  apply(rename_tac x ysa ya ys ca xb ysb cc)(*strict*)
  apply(rule_tac x="ysa @ [ya] @ ysb" in exI)
  apply(simp (no_asm))
  done

lemma parserHF_extension_notempty_fixed_scheduler: "
  valid_parser G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> rule_rpop e1 = x @ rule_rpush e1
  \<Longrightarrow> parserHF_conf_fixed c @ w = rule_rpop e1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c @ hf2
  \<Longrightarrow> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<exists>v. w=v@[parser_bottom G] \<and> v=hf2"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(case_tac c1)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHF_conf_fixedaa parserHF_conf_historyaa parserHF_conf_stackaa)(*strict*)
  apply(case_tac e1)
  apply(rename_tac xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHF_conf_fixedaa parserHF_conf_historyaa parserHF_conf_stackaa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac parserHF_conf_fixed rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(rename_tac f lp lpu rpu)
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(case_tac "f \<sqsubseteq> x @ rpu")
   apply(rename_tac f lp lpu rpu)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac f lp lpu rpu c)(*strict*)
  apply(subgoal_tac "w=c")
   apply(rename_tac f lp lpu rpu c)(*strict*)
   prefer 2
   apply (metis drop_prefix_closureise)
  apply(rename_tac f lp lpu rpu c)(*strict*)
  apply(clarsimp)
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(subgoal_tac "drop (length x + length rpu) f = []")
   apply(rename_tac f lp lpu rpu)(*strict*)
   prefer 2
   apply(rule_tac t="length x+length rpu" and s="length (f@w)" in ssubst)
    apply(rename_tac f lp lpu rpu)(*strict*)
    apply(force)
   apply(rename_tac f lp lpu rpu)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac f lp lpu rpu)(*strict*)
  apply(clarsimp)
  apply(rule_tac xs="rpu" in rev_cases)
   apply(rename_tac f lp lpu rpu)(*strict*)
   apply(clarsimp)
   apply(rename_tac f lp lpu)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac f lp lpu rpu ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac f lp lpu ys y)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac f lp lpu ys)(*strict*)
  apply(rule_tac xs="w" in rev_cases)
   apply(rename_tac f lp lpu ys)(*strict*)
   apply(force)
  apply(rename_tac f lp lpu ys ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac f lp lpu ys ysa)(*strict*)
  apply(rule_tac t="butlast_if_match (x @ ys @ [parser_bottom G]) (parser_bottom G)" and s="x@ys" in ssubst)
   apply(rename_tac f lp lpu ys ysa)(*strict*)
   apply(rule_tac t="x @ ys @ [parser_bottom G]" and s="(x @ ys) @ [parser_bottom G]" in ssubst)
    apply(rename_tac f lp lpu ys ysa)(*strict*)
    apply(force)
   apply(rename_tac f lp lpu ys ysa)(*strict*)
   apply (rule_tac butlast_if_match_direct)
   apply(force)
  apply(rename_tac f lp lpu ys ysa)(*strict*)
  apply(rule_tac t="x@ys" and s="f @ ysa" in ssubst)
   apply(rename_tac f lp lpu ys ysa)(*strict*)
   apply(force)
  apply(rename_tac f lp lpu ys ysa)(*strict*)
  apply(simp (no_asm))
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step1_hlp2: "
valid_parser G \<Longrightarrow>
    ATS.derivation_initial parserHF_initial_configurations
     parserHF_step_relation G d \<Longrightarrow>
    parserHF_step_relation G c e1 c1 \<Longrightarrow>
    parserHF_step_relation G c e2 c2 \<Longrightarrow>
    d i = Some (pair e1a c) \<Longrightarrow>
    parserHF_conf_history c1 = parserHF_conf_history c @ hf2 \<Longrightarrow>
    parserHF_conf_history c2 = parserHF_conf_history c @ hf2 @ hf1 \<Longrightarrow>
    hf1 \<noteq> [] \<Longrightarrow>
    hf1 \<in> parser_markers G \<Longrightarrow>
    hf2 \<in> parser_markers G \<Longrightarrow>
    \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
    \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
       parserHFS_conf_history = parserHF_conf_history c,
       parserHFS_conf_stack = parserHF_conf_stack c,
       parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2\<rparr>
    \<in> parserHFS_configurations G \<Longrightarrow>
    parserHFS_step_relation G
     \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
        parserHFS_conf_history = parserHF_conf_history c,
        parserHFS_conf_stack = parserHF_conf_stack c,
        parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2\<rparr>
     e2 \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c2,
           parserHFS_conf_history = parserHF_conf_history c @ hf2 @ hf1,
           parserHFS_conf_stack = parserHF_conf_stack c2,
           parserHFS_conf_scheduler = wix @ parserHF_conf_fixed c2\<rparr> \<Longrightarrow>
    parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
    Ex (parserHFS_step_relation G
         \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
            parserHFS_conf_history = parserHF_conf_history c,
            parserHFS_conf_stack = parserHF_conf_stack c,
            parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2\<rparr>
         e1)"
  apply(rule_tac parserHFS_step_relation_slim_step_intro2)
      apply(force)
     apply(force)
    apply(simp add: parserHF_step_relation_def parser_step_labels_def)
   apply(clarsimp)
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule parserHF.AX_fixed_scheduler_extendable_translates_backwards)
      apply(force)
     prefer 2
     apply(force)
    apply(rule_tac d="d" in parserHF.belongs_configurations)
     apply(rule parserHF.derivation_initial_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label G e2")
   prefer 2
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="e2" in ballE)
    prefer 2
    apply(simp add: parserHF_step_relation_def)
   apply(force)
  apply(subgoal_tac "valid_parser_step_label G e1")
   prefer 2
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="e1" in ballE)
    prefer 2
    apply(simp add: parserHF_step_relation_def)
   apply(force)
  apply(subgoal_tac "(\<exists>x. x @ rule_rpush e1 = rule_rpop e1)")
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(subgoal_tac "(\<exists>x. x @ rule_rpush e2 = rule_rpop e2)")
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(case_tac "prefix (rule_rpop e2) (parserHF_conf_fixed c)")
   apply(rename_tac x xa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(rule_tac ?e1.0="e2" and x="xa" in parserHF_extension_empty)
         apply(rename_tac x xa)(*strict*)
         apply(force)
        apply(rename_tac x xa)(*strict*)
        apply(force)
       apply(rename_tac x xa)(*strict*)
       apply(force)
      apply(rename_tac x xa)(*strict*)
      apply(force)
     apply(rename_tac x xa)(*strict*)
     apply(force)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(rule_tac ?e1.0="e2" in parserHF_extension_fixed_and_pop)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xa ca)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x xa ca)(*strict*)
   prefer 2
   apply(rule_tac ?e1.0="e2" and x="xa" in parserHF_extension_notempty_fixed_scheduler)
         apply(rename_tac x xa ca)(*strict*)
         apply(force)
        apply(rename_tac x xa ca)(*strict*)
        apply(force)
       apply(rename_tac x xa ca)(*strict*)
       apply(force)
      apply(rename_tac x xa ca)(*strict*)
      apply(force)
     apply(rename_tac x xa ca)(*strict*)
     apply(force)
    apply(rename_tac x xa ca)(*strict*)
    apply(force)
   apply(rename_tac x xa ca)(*strict*)
   apply(force)
  apply(rename_tac x xa ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: parserHFS_step_relation_def parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa xb xc xd y)(*strict*)
  apply(case_tac c)
  apply(rename_tac x xa xb xc xd y parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f h l)
  apply(rename_tac x xa xb xc xd y f h l)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xa xb xc xd y f h l parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f1 h1 l1)
  apply(rename_tac x xa xb xc xd y f h l f1 h1 l1)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xa xb xc xd y f h l f1 h1 l1 parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f2 h2 l2)
  apply(rename_tac x xa xb xc xd y f h l f1 h1 l1 f2 h2 l2)(*strict*)
  apply(case_tac e1)
  apply(rename_tac x xa xb xc xd y f h l f1 h1 l1 f2 h2 cons_l2 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac lpo1 rpo1 lpu1 rpu1)
  apply(rename_tac x xa xb xc xd y f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1)(*strict*)
  apply(case_tac e2)
  apply(rename_tac x xa xb xc xd y f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac lpo2 rpo2 lpu2 rpu2)
  apply(rename_tac x xa xb xc xd y f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 lpo2 rpo2 lpu2 rpu2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa xb xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
  apply(rule_tac xs="xb" in rev_cases)
   apply(rename_tac x xa xb xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
   prefer 2
   apply(rename_tac x xa xb xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_bottom G \<in> set w")
     apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa)(*strict*)
     apply(blast)
    apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa)(*strict*)
    apply(rule_tac A="set(take k w)" in set_mp)
     apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa)(*strict*)
     apply(rule set_take_subset2)
     apply(force)
    apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa)(*strict*)
    apply(rule_tac t="take k w" and s="f @
       drop (length f)
        (butlast_if_match
          (take ka wa @ take (ka - length wa) [parser_bottom G])
          (parser_bottom G)) @
       hf1 @ [parser_bottom G]" in ssubst)
     apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa)(*strict*)
     apply(force)
    apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ys k w ka wa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa xc xd f h lpo1 lpu1 rpu1 lpo2 lpu2 ys k ka wa nat xb)(*strict*)
   apply(simp add: parserHFS_configurations_def)
  apply(rename_tac x xa xb xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
  apply(rule_tac xs="drop (Suc (length xa + length y)) f" in rev_cases)
   apply(rename_tac x xa xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
   apply(subgoal_tac "butlast_if_match ((wi @ y) @ [parser_bottom G])
          (parser_bottom G) = wi @ y")
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
    prefer 2
    apply (metis append_assoc butlast_if_match_direct)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
   apply(clarsimp)
   apply(thin_tac "butlast_if_match (wi @ y @ [parser_bottom G]) (parser_bottom G) =
       wi @ y")
   apply(case_tac "wi @ y @ [parser_bottom G] = f")
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
    apply(force)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
   apply(erule_tac P="wi @ y @ [parser_bottom G] \<sqsubseteq> f" in disjE)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2)(*strict*)
   apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_bottom G \<in> set w")
     apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c)(*strict*)
     apply(blast)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c)(*strict*)
    apply(rule_tac A="set(take k w)" in set_mp)
     apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c)(*strict*)
     apply(rule set_take_subset2)
     apply(force)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c)(*strict*)
    apply(rule_tac t="take k w" and s="wi @ y @ [parser_bottom G]" in ssubst)
     apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c)(*strict*)
     apply(force)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k w ka wa c nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k ka wa nat)(*strict*)
   apply(subgoal_tac "k
        =
       Suc nat+(length f +
        (length wi - length f + (length y - (length f - length wi))))")
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k ka wa nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 k ka wa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa)(*strict*)
   apply(subgoal_tac "prefix f wi \<or> SSX" for SSX)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa)(*strict*)
    prefer 2
    apply(rule_tac d="y" in mutual_prefix_prefix)
    apply(force)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa)(*strict*)
   apply(erule_tac P="prefix f wi" in disjE)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c)(*strict*)
    apply(erule disjE)
     apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c)(*strict*)
     apply(clarsimp)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
    apply(case_tac "ka - length wa")
     apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "butlast_if_match (take ka wa) (parser_bottom G) = take ka wa")
      apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
      prefer 2
      apply (metis butlast_if_match_reduces parser_bottom_take_end)
     apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(subgoal_tac "prefix f x \<or> SSX" for SSX)
      apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
      prefer 2
      apply(rule_tac b="ca" and d="rpu1" in mutual_prefix_prefix)
      apply(force)
     apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(erule_tac P="prefix f x" in disjE)
      apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
      apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
      apply(clarsimp)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
      apply(subgoal_tac "ca=cb @ rpu1")
       apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
       prefer 2
       apply (metis same_append_eq)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
      apply(clarsimp)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
      apply(subgoal_tac "drop (length f) (take ka wa) = cb @ rpu1")
       apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
       prefer 2
       apply (metis drop_append)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "prefix c cb \<or> SSX" for SSX)
       apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
       prefer 2
       apply(rule_tac d="rpu1 @ hf1" and b="y" in mutual_prefix_prefix)
       apply(force)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
      apply(erule_tac P="prefix c cb" in disjE)
       apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
       apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
       apply(clarsimp)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
      apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
      apply(clarsimp)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
      apply(subgoal_tac "prefix rpu1 ca \<or> SSX" for SSX)
       apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
       prefer 2
       apply(rule_tac b="hf1" and d="y" in mutual_prefix_prefix)
       apply(force)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
      apply(erule_tac P="prefix rpu1 ca" in disjE)
       apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
       apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
       apply(clarsimp)
      apply(rename_tac xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
      apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
      apply(clarsimp)
     apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
     apply(subgoal_tac "rpu1 = cb @ ca")
      apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
      prefer 2
      apply (metis same_append_eq)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
     apply(subgoal_tac "drop (length x + length cb) (take ka wa) = ca")
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
      prefer 2
      apply (metis append_assoc append_eq_conv_conj length_append)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c cb)(*strict*)
     apply(subgoal_tac "prefix (drop (length x + length cb) (take ka wa)) c \<or> SSX" for SSX)
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c cb)(*strict*)
      prefer 2
      apply(rule_tac mutual_prefix_prefix)
      apply(force)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c cb)(*strict*)
     apply(erule_tac P="prefix (drop (length x + length cb) (take ka wa)) c" in disjE)
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c cb)(*strict*)
      apply(simp add: prefix_def valid_parser_step_label_def)
      apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c cb)(*strict*)
     apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c cb ca)(*strict*)
     apply(subgoal_tac "y=ca@hf1")
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c cb ca)(*strict*)
      prefer 2
      apply (metis append_assoc same_append_eq)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c cb ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xc xd h lpo1 lpu1 lpo2 lpu2 ka wa c cb ca)(*strict*)
     apply(rule_tac x="hf1 @ [parser_bottom G]" in exI)
     apply(force)
    apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 ka c ca nat xa)(*strict*)
    apply(subgoal_tac "ka = Suc nat + (length x + length xa)")
     apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 ka c ca nat xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 ka c ca nat xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    apply(subgoal_tac "butlast_if_match ((x @ xa) @ [parser_bottom G]) (parser_bottom G) = x@xa")
     apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
     prefer 2
     apply (metis append_assoc butlast_if_match_direct)
    apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "prefix f x \<or> SSX" for SSX)
     apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
     prefer 2
     apply(rule_tac mutual_prefix_prefix)
     apply(force)
    apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    apply(erule_tac P="prefix f x" in disjE)
     apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
     apply(simp add: prefix_def valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac xc xd y f h lpo1 lpu1 lpo2 lpu2 c xa cb)(*strict*)
     apply(subgoal_tac "prefix cb c \<or> SSX" for SSX)
      apply(rename_tac xc xd y f h lpo1 lpu1 lpo2 lpu2 c xa cb)(*strict*)
      prefer 2
      apply(rule_tac mutual_prefix_prefix)
      apply(force)
     apply(rename_tac xc xd y f h lpo1 lpu1 lpo2 lpu2 c xa cb)(*strict*)
     apply(simp add: prefix_def valid_parser_step_label_def suffix_def)
    apply(rename_tac x xc xd y f h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
    apply(subgoal_tac "prefix cb xa \<or> SSX" for SSX)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
     prefer 2
     apply(rule_tac mutual_prefix_prefix)
     apply(force)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
    apply(erule_tac P="prefix cb xa" in disjE)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
     apply(simp add: prefix_def valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c cb cc)(*strict*)
     apply(simp add: suffix_def)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
    apply(simp add: prefix_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cc)(*strict*)
    apply(rule_tac xs="ca" in rev_cases)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cc)(*strict*)
     prefer 2
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cc ys ya)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c xa)(*strict*)
     apply(simp add: suffix_def)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cc)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c)(*strict*)
   apply(erule disjE)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
    apply(rule_tac x="ca@drop (length c) y @ [parser_bottom G]" in exI)
    apply(rule_tac t="wi @ c @ drop (length c) y @ [parser_bottom G]" and s="(wi @ c) @ drop (length c) y @ [parser_bottom G]" in ssubst)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(force)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
    apply(rule_tac t="wi@c" and s="x @ rpu1 @ ca" in ssubst)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(force)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
   apply(case_tac "ka - length wa")
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (take ka wa) (parser_bottom G) = take ka wa")
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     prefer 2
     apply (metis butlast_if_match_reduces parser_bottom_take_end)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "prefix (wi@c) x \<or> SSX" for SSX)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     prefer 2
     apply(rule_tac b="ca" and d="rpu1" in mutual_prefix_prefix)
     apply(force)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
    apply(erule_tac P="prefix (wi@c) x" in disjE)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
     apply(clarsimp)
     apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
     apply(subgoal_tac "ca=cb @ rpu1")
      apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
      prefer 2
      apply (metis same_append_eq)
     apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
     apply(subgoal_tac "drop (length wi + length c) (take ka wa) = cb @ rpu1")
      apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
      prefer 2
      apply(rule_tac t="take ka wa" and s="wi @ c @ cb @ rpu1" in ssubst)
       apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
       apply(force)
      apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
     apply(clarsimp)
     apply(rule_tac x="hf1 @[parser_bottom G]" in exI)
     apply(force)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
    apply(subgoal_tac "drop (length wi + length c) (take ka wa) = ca")
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
     prefer 2
     apply(rule_tac t="take ka wa" and s="wi @ c @ ca" in ssubst)
      apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
      apply(force)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
    apply(subgoal_tac "prefix x wi \<or> SSX" for SSX)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
     prefer 2
     apply(rule_tac mutual_prefix_prefix)
     apply(force)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
    apply(erule_tac P="prefix x wi" in disjE)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
     apply(simp add: prefix_def valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(subgoal_tac "rpu1=ca @ c @ drop (length x + length ca + length c) (take ka wa)")
      apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
      prefer 2
      apply (metis same_append_eq)
     apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa c ca)(*strict*)
     apply(rule_tac x="hf1@[parser_bottom G]" in exI)
     apply(force)
    apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c cb)(*strict*)
    apply(simp add: prefix_def valid_parser_step_label_def parserHFS_configurations_def)
    apply(clarsimp)
    apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
    apply(subgoal_tac "rpu1=cb @ drop (length wi + (length ca + length  cb)) (take ka wa)")
     apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
     prefer 2
     apply (metis same_append_eq)
    apply(rename_tac xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 ka wa cb ca)(*strict*)
    apply(rule_tac x="hf1@[parser_bottom G]" in exI)
    apply(force)
   apply(rename_tac x xc xd y h lpo1 lpu1 rpu1 lpo2 lpu2 ka wa c ca nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka c ca nat xa)(*strict*)
   apply(subgoal_tac "ka = Suc nat+(length x + length xa)")
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka c ca nat xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 ka c ca nat xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
   apply(subgoal_tac "butlast_if_match ((x @ xa) @ [parser_bottom G]) (parser_bottom G) = (x @ xa)")
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    prefer 2
    apply (metis append_assoc butlast_if_match_direct)
   apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
   apply(clarsimp)
   apply(rule_tac x="[]" in exI)
   apply(clarsimp)
   apply(subgoal_tac "prefix wi x \<or> SSX" for SSX)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    prefer 2
    apply(rule_tac mutual_prefix_prefix)
    apply(force)
   apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
   apply(erule_tac P="prefix wi x" in disjE)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    prefer 2
    apply(simp add: prefix_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
    apply(subgoal_tac "prefix cb xa \<or> SSX" for SSX)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
     prefer 2
     apply(rule_tac mutual_prefix_prefix)
     apply(force)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
    apply(erule_tac P="prefix cb xa" in disjE)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
     prefer 2
     apply(simp add: prefix_def valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cc)(*strict*)
     apply(rule_tac xs="ca" in rev_cases)
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cc)(*strict*)
      prefer 2
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cc ys ya)(*strict*)
      apply(clarsimp)
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 xa)(*strict*)
      apply(simp add: suffix_def)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cc)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c xa cc)(*strict*)
     apply(rule_tac xs="c" in rev_cases)
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c xa cc)(*strict*)
      prefer 2
      apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c xa cc ys ya)(*strict*)
      apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c xa cc)(*strict*)
     apply(simp add: suffix_def)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca cb cc)(*strict*)
    apply(rule_tac xs="ca" in rev_cases)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca cb cc)(*strict*)
     prefer 2
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca cb cc ys ya)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c cb ys)(*strict*)
     apply(simp add: suffix_def)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca cb cc)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
   apply(simp add: prefix_def)
   apply(subgoal_tac "prefix wi x \<or> SSX" for SSX)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    prefer 2
    apply(rule_tac b="c @ ca" in mutual_prefix_prefix)
    apply(force)
   apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
   apply(erule_tac P="prefix wi x" in disjE)
    apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    prefer 2
    apply(simp add: prefix_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
    apply(rule_tac xs="ca" in rev_cases)
     apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa ys ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ys)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac x xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
   apply(simp add: prefix_def)
   apply(subgoal_tac "prefix c cb \<or> SSX" for SSX)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
    prefer 2
    apply(rule_tac mutual_prefix_prefix)
    apply(force)
   apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
   apply(erule_tac P="prefix c cb" in disjE)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
    prefer 2
    apply(simp add: prefix_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 ca xa cb cc)(*strict*)
    apply(rule_tac xs="ca" in rev_cases)
     apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 ca xa cb cc)(*strict*)
     apply(clarsimp)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 ca xa cb cc ys ya)(*strict*)
    apply(clarsimp)
    apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 cb cc ys)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c ca xa cb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac xc xd y h lpo1 lpu1 lpo2 lpu2 c xa cc)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac x xa xc xd y f h lpo1 lpu1 rpu1 lpo2 lpu2 ys ya)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step1_hlp: "
              valid_parser G \<Longrightarrow>
       ATS.derivation_initial parserHF_initial_configurations
        parserHF_step_relation G d \<Longrightarrow>
       parserHF_step_relation G c e1 c1 \<Longrightarrow>
       parserHF_step_relation G c e2 c2 \<Longrightarrow>
       d i = Some (pair e1a c) \<Longrightarrow>
       parserHF_conf_history c1 = parserHF_conf_history c @ hf2 \<Longrightarrow>
       parserHF_conf_history c2 = parserHF_conf_history c @ hf2 @ hf1 \<Longrightarrow>
       hf1\<noteq>[] \<Longrightarrow>
       hf1 \<in> parser_markers G \<Longrightarrow>
       hf2 \<in> parser_markers G \<Longrightarrow>
       \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
       \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
          parserHFS_conf_history = parserHF_conf_history c,
          parserHFS_conf_stack = parserHF_conf_stack c,
          parserHFS_conf_scheduler =
            wi @
            (if parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
             then parserHF_conf_fixed c2
             else parserHF_conf_fixed c2 @ [parser_bottom G])\<rparr>
       \<in> parserHFS_configurations G \<Longrightarrow>
       parserHFS_step_relation G
        \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
           parserHFS_conf_history = parserHF_conf_history c,
           parserHFS_conf_stack = parserHF_conf_stack c,
           parserHFS_conf_scheduler =
             wi @
             (if parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
              then parserHF_conf_fixed c2
              else parserHF_conf_fixed c2 @ [parser_bottom G])\<rparr>
        e2
        \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c2,
           parserHFS_conf_history = parserHF_conf_history c @ hf2 @ hf1,
           parserHFS_conf_stack = parserHF_conf_stack c2,
           parserHFS_conf_scheduler =
             wix @
             (if parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
              then parserHF_conf_fixed c2
              else parserHF_conf_fixed c2 @ [parser_bottom G])\<rparr> \<Longrightarrow>
       (parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
        Ex (parserHFS_step_relation G
             \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
                parserHFS_conf_history = parserHF_conf_history c,
                parserHFS_conf_stack = parserHF_conf_stack c,
                parserHFS_conf_scheduler =
                  wi @
                  parserHF_conf_fixed c2\<rparr>
             e1)) \<and>
       (\<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
        Ex (parserHFS_step_relation G
             \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
                parserHFS_conf_history = parserHF_conf_history c,
                parserHFS_conf_stack = parserHF_conf_stack c,
                parserHFS_conf_scheduler =
                  wi @
                  parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr>
             e1))"
  apply(rule conjI)
   apply(clarsimp)
   prefer 2
   apply(clarsimp)
   apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step1_hlp1)
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
    apply(force)
   apply(force)
  apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step1_hlp2)
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
   apply(force)
  apply(force)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step1: "
   (\<forall>G. valid_parser G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial parserHF_initial_configurations
               parserHF_step_relation G d \<longrightarrow>
              (\<forall>c e1 c1.
                  parserHF_step_relation G c e1 c1 \<longrightarrow>
                  (\<forall>e2 c2.
                      parserHF_step_relation G c e2 c2 \<longrightarrow>
                      (\<forall>i. (\<exists>ei. d i = Some (pair ei c)) \<longrightarrow>
                           (\<forall>hf2. parserHF_conf_history c1 =
                                  parserHF_conf_history c @ hf2 \<longrightarrow>
                                  (\<forall>hf1.
parserHF_conf_history c2 = parserHF_conf_history c @ hf2 @ hf1 \<longrightarrow>
hf1 \<noteq> [] \<longrightarrow>
ATS.derivation_initial parserHFS_initial_configurations
 parserHFS_step_relation G
 (ATS_Branching_Versus_Linear1.Bra2LinDer parser_empty_scheduler_fragment
   (@) (@) parserHF_conf_fixed parserHFvHFS_Bra2LinConf
   parserHFvHFS_Bra2LinStep
   (\<lambda>G w. if w \<sqsupseteq> [parser_bottom G] then w else w @ [parser_bottom G]) G
   (derivation_append d (der2 c e2 c2) i) (Suc i)) \<longrightarrow>
hf1 \<in> parser_markers G \<longrightarrow>
hf2 \<in> parser_markers G \<longrightarrow>
\<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
Ex (parserHFS_step_relation G
     (the (get_configuration
            (ATS_Branching_Versus_Linear1.Bra2LinDer
              parser_empty_scheduler_fragment (@) (@) parserHF_conf_fixed
              parserHFvHFS_Bra2LinConf parserHFvHFS_Bra2LinStep
              (\<lambda>G w. if w \<sqsupseteq> [parser_bottom G] then w
                     else w @ [parser_bottom G])
              G (derivation_append d (der2 c e2 c2) i) (Suc i) i)))
     e1))))))))"
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. SSd SSn = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1)(*strict*)
   prefer 2
   apply(rule_tac
      d="parserHF_vs_parserHFS.Bra2LinDer
          G (derivation_append d (der2 c e2 c2) i) (Suc i)"
      and n="i" and
      m="Suc i"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def derivation_append_def der2_def get_configuration_def parserHFvHFS_Bra2LinConf_def parserHF_vs_parserHFS.Bra2LinDer'_def parserHFvHFS_Bra2LinStep_def parser_empty_scheduler_fragment_def)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1)(*strict*)
   apply(force)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1)(*strict*)
  apply(erule exE)+
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1 e1a e2a c1a c2a)(*strict*)
  apply(subgoal_tac "c1a \<in> parserHFS_configurations G")
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1 e1a e2a c1a c2a)(*strict*)
   prefer 2
   apply(rule_tac e="e1a" and i="i" in parserHFS.belongs_configurations)
    apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1 e1a e2a c1a c2a)(*strict*)
    apply(rule parserHFS.derivation_initial_belongs)
     apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1 e1a e2a c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1 e1a e2a c1a c2a)(*strict*)
    apply(force)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1 e1a e2a c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf2 hf1 e1a e2a c1a c2a)(*strict*)
  apply(thin_tac "parserHFS.derivation_initial G
        (parserHF_vs_parserHFS.Bra2LinDer
          G (derivation_append d (der2 c e2 c2) i) (Suc i))")
  apply(simp only: parserHF_vs_parserHFS.Bra2LinDer_def get_configuration_def derivation_append_def der2_def)
  apply(simp add: parserHFvHFS_Bra2LinConf_def)
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
  apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step1_hlp)
              apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
              apply(force)
             apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
             apply(force)
            apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
            apply(force)
           apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
           apply(force)
          apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
          apply(force)
         apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
         apply(force)
        apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
        apply(force)
       apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
       apply(force)
      apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
      apply(force)
     apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
     apply(force)
    apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
    apply(force)
   apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
   apply(force)
  apply(rename_tac G d c e1 c1 c2 i hf2 hf1 e1a e2a)(*strict*)
  apply(force)
  done

lemma butlast_if_match_length_min: "
  length x \<le> length (butlast_if_match (x @ [y]) (parser_bottom G))"
  apply (metis butlast_if_match_pull_out drop_length_append list.distinct(1))
  done

lemma parserHF_extension_empty_prefix_of_fixed_scheduler_with_bottom: "
  valid_parser G
  \<Longrightarrow> parserHF_step_relation G c e1 c1
  \<Longrightarrow> parserHF_conf_history c1 = parserHF_conf_history c
  \<Longrightarrow> prefix (rule_rpop e1) (parserHF_conf_fixed c @ [parser_bottom G])"
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(case_tac c)
  apply(rename_tac x parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHF_conf_fixedaa parserHF_conf_historyaa parserHF_conf_stackaa)(*strict*)
  apply(case_tac e1)
  apply(rename_tac x parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka parserHF_conf_fixedaa parserHF_conf_historyaa parserHF_conf_stackaa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac parserHF_conf_fixed rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
  apply(rename_tac f lp rp lpu rpu)
  apply(rename_tac f lp rp lpu rpu)(*strict*)
  apply(erule disjE)
   apply(rename_tac f lp rp lpu rpu)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac f lp rp lpu rpu)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac f lp lpu rpu c)(*strict*)
  apply(rule_tac xs="c" in rev_cases)
   apply(rename_tac f lp lpu rpu c)(*strict*)
   apply(clarsimp)
  apply(rename_tac f lp lpu rpu c ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac f lp lpu rpu ys y)(*strict*)
  apply(case_tac "y=parser_bottom G")
   apply(rename_tac f lp lpu rpu ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac f lp lpu rpu ys)(*strict*)
   apply(rule_tac x="[]" in exI)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac f lp lpu rpu ys)(*strict*)
    prefer 2
    apply(rule_tac x="f@ys" and y="parser_bottom G" and G="G" in  butlast_if_match_length_min)
   apply(rename_tac f lp lpu rpu ys)(*strict*)
   apply(clarsimp)
   apply (metis butlast_if_match_direct drop_butlast_if_match_distrib drop_eq_Nil)
  apply(rename_tac f lp lpu rpu ys y)(*strict*)
  apply(subgoal_tac "butlast_if_match ((f @ ys) @ [y]) (parser_bottom G) = f@ys")
   apply(rename_tac f lp lpu rpu ys y)(*strict*)
   prefer 2
   apply (metis NotemptyString butlast_if_match_direct2 drop_butlast_if_match_distrib drop_eq_Nil)
  apply(rename_tac f lp lpu rpu ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac f lp lpu rpu y)(*strict*)
  apply(subgoal_tac "butlast_if_match (f @ [y]) (parser_bottom G) = f@[y]")
   apply(rename_tac f lp lpu rpu y)(*strict*)
   apply(force)
  apply(rename_tac f lp lpu rpu y)(*strict*)
  apply (metis butlast_if_match_reduces snoc_eq_iff_butlast)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step2_hlp1: "
   valid_parser G \<Longrightarrow>
    ATS.derivation_initial parserHF_initial_configurations
     parserHF_step_relation G d \<Longrightarrow>
    parserHF_step_relation G c e1 c1 \<Longrightarrow>
    parserHF_step_relation G c e2 c2 \<Longrightarrow>
 \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
       \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
    d i = Some (pair e1a c) \<Longrightarrow>
    parserHF_conf_history c1 = parserHF_conf_history c @ hf2 \<Longrightarrow>
    parserHF_conf_history c2 = parserHF_conf_history c @ hf2 \<Longrightarrow>
    hf2 \<in> parser_markers G \<Longrightarrow>
    \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
       parserHFS_conf_history = parserHF_conf_history c,
       parserHFS_conf_stack = parserHF_conf_stack c,
       parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr>
    \<in> parserHFS_configurations G \<Longrightarrow>
    parserHFS_step_relation G
     \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
        parserHFS_conf_history = parserHF_conf_history c,
        parserHFS_conf_stack = parserHF_conf_stack c,
        parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr>
     e2 \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c2,
           parserHFS_conf_history = parserHF_conf_history c @ hf2,
           parserHFS_conf_stack = parserHF_conf_stack c2,
           parserHFS_conf_scheduler =
             wiX @ parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr> \<Longrightarrow>
    \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
    Ex (parserHFS_step_relation G
         \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
            parserHFS_conf_history = parserHF_conf_history c,
            parserHFS_conf_stack = parserHF_conf_stack c,
            parserHFS_conf_scheduler =
              wi @ parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr>
         e1)"
  apply(rule_tac parserHFS_step_relation_slim_step_intro2)
      apply(force)
     apply(force)
    apply(simp add: parserHF_step_relation_def parser_step_labels_def)
   apply(clarsimp)
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac e="e2" in parserHF.AX_fixed_scheduler_extendable_translates_backwards)
      apply(force)
     prefer 2
     apply(force)
    apply(rule_tac d="d" in parserHF.belongs_configurations)
     apply(rule parserHF.derivation_initial_belongs)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label G e2")
   prefer 2
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="e2" in ballE)
    prefer 2
    apply(simp add: parserHF_step_relation_def)
   apply(force)
  apply(subgoal_tac "valid_parser_step_label G e1")
   prefer 2
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="e1" in ballE)
    prefer 2
    apply(simp add: parserHF_step_relation_def)
   apply(force)
  apply(subgoal_tac "(\<exists>x. x @ rule_rpush e1 = rule_rpop e1)")
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(subgoal_tac "(\<exists>x. x @ rule_rpush e2 = rule_rpop e2)")
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(case_tac "prefix (rule_rpop e2) (parserHF_conf_fixed c)")
   apply(rename_tac x xa)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(rule_tac ?e1.0="e2" and x="xa" in parserHF_extension_empty)
         apply(rename_tac x xa)(*strict*)
         apply(force)
        apply(rename_tac x xa)(*strict*)
        apply(force)
       apply(rename_tac x xa)(*strict*)
       apply(force)
      apply(rename_tac x xa)(*strict*)
      apply(force)
     apply(rename_tac x xa)(*strict*)
     apply(force)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(rule_tac ?e1.0="e1" in parserHF_extension_empty_prefix_of_fixed_scheduler_with_bottom)
      apply(rename_tac x xa)(*strict*)
      apply(force)
     apply(rename_tac x xa)(*strict*)
     apply(force)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa ca caa)(*strict*)
   apply(rule_tac xs="caa" in rev_cases)
    apply(rename_tac x xa ca caa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa ca)(*strict*)
    apply(rule_tac x="[]" in exI)
    apply(clarsimp)
    apply(simp add: parserHF_step_relation_def parserHFS_step_relation_def prefix_def parserHFS_configurations_def valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi)(*strict*)
    apply(case_tac c)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
    apply(rename_tac f h l)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l)(*strict*)
    apply(case_tac c1)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
    apply(rename_tac f1 h1 l1)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l f1 h1 l1)(*strict*)
    apply(case_tac c2)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l f1 h1 l1 parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
    apply(rename_tac f2 h2 l2)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l f1 h1 l1 f2 h2 l2)(*strict*)
    apply(case_tac e1)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l f1 h1 l1 f2 h2 cons_l2 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(rename_tac lpo1 rpo1 lpu1 rpu1)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1)(*strict*)
    apply(case_tac e2)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(rename_tac lpo2 rpo2 lpu2 rpu2)
    apply(rename_tac x xa ca xb k w ka wa xe xf caa xg xh xi f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 lpo2 rpo2 lpu2 rpu2)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa c k w ka wa xe xf ca xg xh xi h lpo1 lpu1 lpo2 lpu2 rpu2)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac x xa ca caa ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa ca ys)(*strict*)
   apply(simp add: parserHF_step_relation_def parserHFS_step_relation_def prefix_def parserHFS_configurations_def valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh)(*strict*)
   apply(case_tac c)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
   apply(rename_tac f h l)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l)(*strict*)
   apply(case_tac c1)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
   apply(rename_tac f1 h1 l1)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l f1 h1 l1)(*strict*)
   apply(case_tac c2)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l f1 h1 l1 parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
   apply(rename_tac f2 h2 l2)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l f1 h1 l1 f2 h2 l2)(*strict*)
   apply(case_tac e1)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l f1 h1 l1 f2 h2 cons_l2 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(rename_tac lpo1 rpo1 lpu1 rpu1)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1)(*strict*)
   apply(case_tac e2)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(rename_tac lpo2 rpo2 lpu2 rpu2)
   apply(rename_tac x xa ca ys xb k w ka wa xe xf caa xg xh f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 lpo2 rpo2 lpu2 rpu2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
    prefer 2
    apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
   apply(subgoal_tac "min (length w) k = k")
    apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
   apply(clarsimp)
   apply(case_tac "ka-length wa")
    apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
    prefer 2
    apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa c ys k w ka xe xf ca xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb)(*strict*)
    apply(subgoal_tac "ka = Suc nat+(length x + length xb)")
     apply(rename_tac x xa c ys k w ka xe xf ca xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x xa c ys k w ka xe xf ca xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa c ys k w xe xf ca xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb)(*strict*)
    apply(rule_tac xs="ca" in rev_cases)
     apply(rename_tac x xa c ys k w xe xf ca xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb)(*strict*)
     apply(clarsimp)
    apply(rename_tac x xa c ys k w xe xf ca xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb ysa y)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa c ys k w xe xf xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb ysa)(*strict*)
    apply(rule_tac w="x @ xb" and v="ys" and r="take k w" and s="c" and A="parser_bottom G" in elem_in_append_set)
      apply(rename_tac x xa c ys k w xe xf xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb ysa)(*strict*)
      apply(force)
     apply(rename_tac x xa c ys k w xe xf xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb ysa)(*strict*)
     apply (metis in_set_takeD nset_diff)
    apply(rename_tac x xa c ys k w xe xf xg h lpo1 lpu1 lpo2 lpu2 rpu2 nat xb ysa)(*strict*)
    apply(force)
   apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
   apply(clarsimp)
   apply(rule_tac xs="ca" in rev_cases)
    apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xa c ys k w ka wa xe xf ca xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ysa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa c ys k w ka wa xe xf xg xh h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2 ysa)(*strict*)
   apply(thin_tac "valid_parser G")
   apply(thin_tac "parserHF.derivation_initial G d")
   apply(thin_tac "d i = Some (pair e1a \<lparr>parserHF_conf_fixed = take k w @ c, parserHF_conf_history = h, parserHF_conf_stack = xe @ lpo1\<rparr>)")
   apply(thin_tac "[] \<in> parser_markers G")
   apply(thin_tac "\<lparr>rule_lpop = lpo1, rule_rpop = take ka wa, rule_lpush = lpu1, rule_rpush = rpu1\<rparr> \<in> parser_rules G")
   apply(thin_tac "\<lparr>rule_lpop = lpo2, rule_rpop = take k w, rule_lpush = lpu2, rule_rpush = rpu2\<rparr> \<in> parser_rules G")
   apply(thin_tac "set lpo2 \<subseteq> parser_nonterms G")
   apply(thin_tac "length (butlast_if_match (take k w) (parser_bottom G)) \<le> k + length c")
   apply(thin_tac "h \<sqsupseteq> butlast_if_match (take k w @ c) (parser_bottom G)")
   apply(thin_tac "set lpu2 \<subseteq> parser_nonterms G")
   apply(thin_tac "set lpo1 \<subseteq> parser_nonterms G")
   apply(thin_tac "lpo2 \<noteq> []")
   apply(thin_tac "set lpu1 \<subseteq> parser_nonterms G")
   apply(thin_tac "lpu2 \<noteq> []")
   apply(thin_tac "lpo1 \<noteq> []")
   apply(thin_tac "lpu1 \<noteq> []")
   apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take ka wa) \<longrightarrow> (\<exists>x. x @ [parser_bottom G] = rpu1)")
   apply(thin_tac "set h \<subseteq> parser_events G")
   apply(thin_tac "parser_bottom G \<notin> set h")
   apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take k w) \<longrightarrow> (\<exists>x. x @ [parser_bottom G] = rpu2)")
   apply (metis append_assoc)
  apply(rename_tac x xa)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(rule_tac ?e1.0="e2" in parserHF_extension_fixed_and_pop)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(case_tac "rule_rpop e2 = parserHF_conf_fixed c")
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xa ca)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x xa ca)(*strict*)
   prefer 2
   apply(rule_tac ?e1.0="e2" and x="xa" in parserHF_extension_notempty)
         apply(rename_tac x xa ca)(*strict*)
         apply(force)
        apply(rename_tac x xa ca)(*strict*)
        apply(force)
       apply(rename_tac x xa ca)(*strict*)
       apply(force)
      apply(rename_tac x xa ca)(*strict*)
      apply(force)
     apply(rename_tac x xa ca)(*strict*)
     apply(force)
    apply(rename_tac x xa ca)(*strict*)
    apply(force)
   apply(rename_tac x xa ca)(*strict*)
   apply(force)
  apply(rename_tac x xa ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: parserHFS_step_relation_def parserHF_step_relation_def parserHFS_configurations_def valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh)(*strict*)
  apply(case_tac c)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f h l)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f1 h1 l1)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l f1 h1 l1)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l f1 h1 l1 parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f2 h2 l2)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l f1 h1 l1 f2 h2 l2)(*strict*)
  apply(case_tac e1)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l f1 h1 l1 f2 h2 cons_l2 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac lpo1 rpo1 lpu1 rpu1)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1)(*strict*)
  apply(case_tac e2)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac lpo2 rpo2 lpu2 rpu2)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 lpo2 rpo2 lpu2 rpu2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa xb k w ka wa xe xf xg xh f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
  apply(thin_tac "valid_parser G")
  apply(thin_tac "parserHF.derivation_initial G d")
  apply(thin_tac "set lpo2 \<subseteq> parser_nonterms G")
  apply(thin_tac "set lpu2 \<subseteq> parser_nonterms G")
  apply(thin_tac "set lpo1 \<subseteq> parser_nonterms G")
  apply(thin_tac "lpo2 \<noteq> []")
  apply(thin_tac "set lpu1 \<subseteq> parser_nonterms G")
  apply(thin_tac "lpu2 \<noteq> []")
  apply(thin_tac "lpo1 \<noteq> []")
  apply(thin_tac "lpu1 \<noteq> []")
  apply(thin_tac "set h \<subseteq> parser_events G")
  apply(thin_tac "parser_bottom G \<notin> set h")
  apply(thin_tac "d i =
       Some (pair e1a
              \<lparr>parserHF_conf_fixed = f, parserHF_conf_history = h,
                 parserHF_conf_stack = xe @ lpo1\<rparr>)")
  apply(thin_tac "\<lparr>rule_lpop = lpo1, rule_rpop = kPrefix ka (wa @ [parser_bottom G]),
          rule_lpush = lpu1, rule_rpush = rpu1\<rparr>
       \<in> parser_rules G")
  apply(thin_tac "\<lparr>rule_lpop = lpo2, rule_rpop = kPrefix k (w @ [parser_bottom G]),
          rule_lpush = lpu2, rule_rpush = rpu2\<rparr>
       \<in> parser_rules G")
  apply(thin_tac "h \<sqsupseteq> butlast_if_match f (parser_bottom G)")
  apply(thin_tac "xf @ lpo2 = xe @ lpo1")
  apply(simp add: kPrefix_def)
  apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2)(*strict*)
  apply(case_tac "k-length w")
   apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2)(*strict*)
   prefer 2
   apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2 nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2)(*strict*)
  apply(subgoal_tac "min (length w) k = k")
   apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2)(*strict*)
  apply(clarsimp)
  apply(case_tac "ka-length wa")
   apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2)(*strict*)
   prefer 2
   apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2 nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa xb k w ka xe xg f rpu2 nat xc)(*strict*)
   apply(subgoal_tac "ka = Suc nat+(length x + length xc)")
    apply(rename_tac x xa xb k w ka xe xg f rpu2 nat xc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa xb k w ka xe xg f rpu2 nat xc)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa xb k w xe xg f rpu2 nat xc)(*strict*)
   apply(rule_tac xs="xb" in rev_cases)
    apply(rename_tac x xa xb k w xe xg f rpu2 nat xc)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xa xb k w xe xg f rpu2 nat xc ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys c ca)(*strict*)
   apply(rule_tac xs="c" in rev_cases)
    apply(rename_tac x xa k w xe xg f rpu2 nat xc ys c ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys c ca ysa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys ca ysa)(*strict*)
   apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
    apply(rename_tac x xa k w xe xg f rpu2 nat xc ys ca ysa)(*strict*)
    prefer 2
    apply (metis append_Nil2 butlast_if_match_pull_out drop_butlast_if_match_distrib)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys ca ysa)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "ysa=ca@ys")
    apply(rename_tac x xa k w xe xg f rpu2 nat xc ys ca ysa)(*strict*)
    prefer 2
    apply (metis append_assoc same_append_eq)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys ca ysa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys ca)(*strict*)
   apply(subgoal_tac "ca=drop (length f) (take k w)")
    apply(rename_tac x xa k w xe xg f rpu2 nat xc ys ca)(*strict*)
    prefer 2
    apply (metis append_eq_conv_conj)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys)(*strict*)
   apply(subgoal_tac "xa=xg")
    apply(rename_tac x xa k w xe xg f rpu2 nat xc ys)(*strict*)
    prefer 2
    apply (metis append_same_eq)
   apply(rename_tac x xa k w xe xg f rpu2 nat xc ys)(*strict*)
   apply(clarsimp)
   apply(rename_tac x k w xe xg f rpu2 nat xc ys)(*strict*)
   apply(rule_tac x="[]" in exI)
   apply(clarsimp)
   apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take k w) \<longrightarrow>
       (\<exists>x. x @ [parser_bottom G] = rpu2)")
   apply(subgoal_tac "butlast_if_match ((x @ xc) @ [parser_bottom G]) (parser_bottom G) = x@xc")
    apply(rename_tac x k w xe xg f rpu2 nat xc ys)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct)
   apply(rename_tac x k w xe xg f rpu2 nat xc ys)(*strict*)
   apply(clarsimp)
   apply(thin_tac "butlast_if_match (x @ xc @ [parser_bottom G]) (parser_bottom G) =
       x @ xc")
   apply(thin_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
   apply(erule disjE)
    apply(rename_tac x k w xe xg f rpu2 nat xc ys)(*strict*)
    apply(clarsimp)
   apply(rename_tac x k w xe xg f rpu2 nat xc ys)(*strict*)
   apply(clarsimp)
   apply(rename_tac x k w xe xg f rpu2 nat xc ys c)(*strict*)
   apply(rule_tac xs="c" in rev_cases)
    apply(rename_tac x k w xe xg f rpu2 nat xc ys c)(*strict*)
    apply(clarsimp)
   apply(rename_tac x k w xe xg f rpu2 nat xc ys c ysa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x k w xe xg f rpu2 nat xc ys ysa)(*strict*)
   apply(rule_tac ?w1.0="f" and ?v1.0="x" in prefix_alt_apply)
     apply(rename_tac x k w xe xg f rpu2 nat xc ys ysa)(*strict*)
     apply(force)
    apply(rename_tac x k w xe xg f rpu2 nat xc ys ysa)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac k w xe xg f rpu2 xc ys ysa c)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac x k w xe xg f rpu2 nat xc ys ysa)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x k w xe xg rpu2 ys c)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2 c ca)(*strict*)
  apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take ka wa) \<longrightarrow> (\<exists>x. x @ [parser_bottom G] = rpu1)")
  apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take k w) \<longrightarrow> (\<exists>x. x @ [parser_bottom G] = rpu2)")
  apply(rule_tac xs="xb" in rev_cases)
   apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2 c ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa xb k w ka wa xe xg xh f rpu1 rpu2 c ca ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 c ca ys)(*strict*)
  apply(subgoal_tac "c=ca@ys @ [parser_bottom G]")
   apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 c ca ys)(*strict*)
   prefer 2
   apply (metis append_assoc same_append_eq)
  apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 c ca ys)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
  apply(subgoal_tac "butlast_if_match (take ka wa) (parser_bottom G) = take ka wa")
   apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
   prefer 2
   apply (metis butlast_if_match_reduces in_set_conv_decomp in_set_takeD nset_diff)
  apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
  apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
   apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
   prefer 2
   apply (metis append_Nil2 butlast_if_match_pull_out drop_butlast_if_match_distrib)
  apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "xa=xg")
   apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
   prefer 2
   apply (metis append_same_eq)
  apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
  apply(subgoal_tac "x=xh")
   apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
   prefer 2
   apply (metis append_same_eq)
  apply(rename_tac x xa k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
  apply(thin_tac "butlast_if_match (take ka wa) (parser_bottom G) = take ka wa")
  apply(thin_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
  apply(erule disjE)
   apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
   apply(clarsimp)
  apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ca ys)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ca ys c)(*strict*)
  apply(subgoal_tac "ca=drop (length f) (take k w)")
   apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ca ys c)(*strict*)
   prefer 2
   apply (metis append_eq_conv_conj)
  apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ca ys c)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ys c)(*strict*)
  apply(subgoal_tac "c=drop(length f)(take ka wa)")
   apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ys c)(*strict*)
   prefer 2
   apply (metis append_eq_conv_conj)
  apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ys c)(*strict*)
  apply(rule_tac t="take ka wa" and s="f@drop (length f) (take ka wa)" in ssubst)
   apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ys c)(*strict*)
   apply(rule sym)
   apply(blast)
  apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ys c)(*strict*)
  apply(rule_tac t="take k w" and s="f @ drop (length f) (take k w)" in subst)
   apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ys c)(*strict*)
   apply(blast)
  apply(rename_tac k w ka wa xe xg xh f rpu1 rpu2 ys c)(*strict*)
  apply(rule_tac x="ys @ [parser_bottom G]" in exI)
  apply(force)
  done

lemma append_context_empty: "
  w@v@x = v
  \<Longrightarrow> w@x=[]"
  apply(case_tac w)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step2_hlp2: "
 valid_parser G \<Longrightarrow>
    ATS.derivation_initial parserHF_initial_configurations
     parserHF_step_relation G d \<Longrightarrow>
    parserHF_step_relation G c e1 c1 \<Longrightarrow>
    parserHF_step_relation G c e2 c2 \<Longrightarrow>
 \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
       \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
    d i = Some (pair e1a c) \<Longrightarrow>
    parserHF_conf_history c1 = parserHF_conf_history c @ hf2 \<Longrightarrow>
    parserHF_conf_history c2 = parserHF_conf_history c @ hf2 \<Longrightarrow>
    hf2 \<in> parser_markers G \<Longrightarrow>
    \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
       parserHFS_conf_history = parserHF_conf_history c,
       parserHFS_conf_stack = parserHF_conf_stack c,
       parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2\<rparr>
    \<in> parserHFS_configurations G \<Longrightarrow>
    parserHFS_step_relation G
     \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
        parserHFS_conf_history = parserHF_conf_history c,
        parserHFS_conf_stack = parserHF_conf_stack c,
        parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2\<rparr>
     e2 \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c2,
           parserHFS_conf_history = parserHF_conf_history c @ hf2,
           parserHFS_conf_stack = parserHF_conf_stack c2,
           parserHFS_conf_scheduler = wiX @ parserHF_conf_fixed c2\<rparr> \<Longrightarrow>
    parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
    Ex (parserHFS_step_relation G
         \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
            parserHFS_conf_history = parserHF_conf_history c,
            parserHFS_conf_stack = parserHF_conf_stack c,
            parserHFS_conf_scheduler = wi @ parserHF_conf_fixed c2\<rparr>
         e1)"
  apply(thin_tac "\<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
    \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] ")
  apply(rule_tac parserHFS_step_relation_slim_step_intro2)
      apply(force)
     apply(force)
    apply(simp add: parserHF_step_relation_def parser_step_labels_def)
   apply(clarsimp)
   apply(simp add: parserHF_step_relation_def)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label G e2")
   prefer 2
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="e2" in ballE)
    prefer 2
    apply(simp add: parserHF_step_relation_def)
   apply(force)
  apply(subgoal_tac "valid_parser_step_label G e1")
   prefer 2
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac x="e1" in ballE)
    prefer 2
    apply(simp add: parserHF_step_relation_def)
   apply(force)
  apply(subgoal_tac "(\<exists>x. x @ rule_rpush e1 = rule_rpop e1)")
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(subgoal_tac "(\<exists>x. x @ rule_rpush e2 = rule_rpop e2)")
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: parserHF_step_relation_def parserHFS_step_relation_def prefix_def parserHFS_configurations_def valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb)(*strict*)
  apply(case_tac c)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f h l)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f1 h1 l1)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l f1 h1 l1)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l f1 h1 l1 parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f2 h2 l2)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l f1 h1 l1 f2 h2 l2)(*strict*)
  apply(case_tac e1)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l f1 h1 l1 f2 h2 cons_l2 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac lpo1 rpo1 lpu1 rpu1)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1)(*strict*)
  apply(case_tac e2)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac lpo2 rpo2 lpu2 rpu2)
  apply(rename_tac x xa xb k w ka wa xe xf ca y xg xh wb f h l f1 h1 l1 f2 h2 cons_l2 lpo1 rpo1 lpu1 rpu1 lpo2 rpo2 lpu2 rpu2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 lpu1 rpu1 lpo2 lpu2 rpu2)(*strict*)
  apply(thin_tac "valid_parser G")
  apply(thin_tac "parserHF.derivation_initial G d")
  apply(thin_tac "set lpo2 \<subseteq> parser_nonterms G")
  apply(thin_tac "set lpu2 \<subseteq> parser_nonterms G")
  apply(thin_tac "set lpo1 \<subseteq> parser_nonterms G")
  apply(thin_tac "lpo2 \<noteq> []")
  apply(thin_tac "set lpu1 \<subseteq> parser_nonterms G")
  apply(thin_tac "lpu2 \<noteq> []")
  apply(thin_tac "lpo1 \<noteq> []")
  apply(thin_tac "lpu1 \<noteq> []")
  apply(thin_tac "set h \<subseteq> parser_events G")
  apply(thin_tac "parser_bottom G \<notin> set h")
  apply(thin_tac "d i =
       Some
        (pair e1a
          \<lparr>parserHF_conf_fixed = f, parserHF_conf_history = h,
             parserHF_conf_stack = xe @ lpo1\<rparr>)")
  apply(thin_tac "\<lparr>rule_lpop = lpo1, rule_rpop = kPrefix ka (wa @ [parser_bottom G]),
          rule_lpush = lpu1, rule_rpush = rpu1\<rparr>
       \<in> parser_rules G")
  apply(thin_tac "\<lparr>rule_lpop = lpo2, rule_rpop = kPrefix k (w @ [parser_bottom G]),
          rule_lpush = lpu2, rule_rpush = rpu2\<rparr>
       \<in> parser_rules G")
  apply(thin_tac "drop (length f)
        (butlast_if_match (kPrefix k (w @ [parser_bottom G]))
          (parser_bottom G))
       \<in> parser_markers G")
  apply(simp add: kPrefix_def)
  apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 rpu1 lpo2 rpu2)(*strict*)
  apply(case_tac "k-length w")
   apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 rpu1 lpo2 rpu2)(*strict*)
   prefer 2
   apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 rpu1 lpo2 rpu2 nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa xb k ka wa xe xf c y xh f h lpo1 rpu1 lpo2 nat xc)(*strict*)
   apply(subgoal_tac "k = Suc nat + (length xa + length xc)")
    apply(rename_tac x xa xb k ka wa xe xf c y xh f h lpo1 rpu1 lpo2 nat xc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa xb k ka wa xe xf c y xh f h lpo1 rpu1 lpo2 nat xc)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa xb ka wa xe xf c y xh f h lpo1 rpu1 lpo2 nat xc)(*strict*)
   apply(subgoal_tac "min (length xa + length xc)
                (Suc (nat + (length xa + length xc))) = (length xa + length xc)")
    apply(rename_tac x xa xb ka wa xe xf c y xh f h lpo1 rpu1 lpo2 nat xc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa xb ka wa xe xf c y xh f h lpo1 rpu1 lpo2 nat xc)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac x xa xb ka wa xe xf c xh f lpo1 rpu1 lpo2 nat xc ca)(*strict*)
   apply(rule_tac xs="xb" in rev_cases)
    apply(rename_tac x xa xb ka wa xe xf c xh f lpo1 rpu1 lpo2 nat xc ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa ka wa xe xf c xh f lpo1 rpu1 lpo2 nat ca)(*strict*)
    apply(rule_tac xs="c" in rev_cases)
     apply(rename_tac x xa ka wa xe xf c xh f lpo1 rpu1 lpo2 nat ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca cb)(*strict*)
     apply(rule_tac xs="cb" in rev_cases)
      apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca cb)(*strict*)
      apply(clarsimp)
     apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca cb ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca ys y)(*strict*)
     apply(case_tac "ka - length wa")
      apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca ys y)(*strict*)
      apply(clarsimp)
      apply(rule_tac w="xa @ ca" and v="ys @ [y]" and A="parser_bottom G" in elem_in_append_set)
        apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca ys y)(*strict*)
        apply(force)
       apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca ys y)(*strict*)
       apply(force)
      apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca ys y)(*strict*)
      apply (metis in_set_takeD nset_diff)
     apply(rename_tac x xa ka wa xe xf xh lpo1 rpu1 lpo2 nat ca ys y nata)(*strict*)
     apply(clarsimp)
    apply(rename_tac x xa ka wa xe xf c xh f lpo1 rpu1 lpo2 nat ca ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa ka wa xe xf xh f lpo1 rpu1 lpo2 nat ca ys)(*strict*)
    apply(thin_tac "set (drop (Suc (length xa + (length wiX + length ca))) f)
       \<subseteq> parser_events G")
    apply(thin_tac "min (length xa + (length wiX + length ca))
        (Suc (nat + (length xa + (length wiX + length ca)))) =
       length xa + (length wiX + length ca)")
    apply(subgoal_tac "X" for X)
     apply(rename_tac x xa ka wa xe xf xh f lpo1 rpu1 lpo2 nat ca ys)(*strict*)
     prefer 2
     apply(rule_tac v="ca @
       [parser_bottom G]" and w="wiX" in append_context_empty)
     apply(force)
    apply(rename_tac x xa ka wa xe xf xh f lpo1 rpu1 lpo2 nat ca ys)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
    apply(subgoal_tac "x=xh")
     apply(rename_tac x xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
     prefer 2
     apply (metis append_same_eq)
    apply(rename_tac x xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
    apply(thin_tac "length f \<le> Suc (length xa + length ca)")
    apply(subgoal_tac "butlast_if_match ((xa @ ca) @ [parser_bottom G])
          (parser_bottom G) = xa@ca" )
     apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
     prefer 2
     apply (metis butlast_if_match_direct)
    apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
    apply(clarsimp)
    apply(thin_tac "butlast_if_match (xa @ ca @ [parser_bottom G]) (parser_bottom G) =
       xa @ ca")
    apply(case_tac "ka - length wa")
     apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
     apply(subgoal_tac "min (length wa) ka = ka")
      apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "butlast_if_match (take ka wa) (parser_bottom G) =take ka wa")
      apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
      prefer 2
      apply (metis butlast_if_match_reduces parser_bottom_take_end)
     apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
     apply(clarsimp)
     apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take ka wa) \<longrightarrow>
       (\<exists>x. x @ [parser_bottom G] = rpu1)")
     apply(thin_tac "xf @ lpo2 = xe @ lpo1")
     apply(erule disjE)
      apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
      apply(clarsimp)
      apply(rename_tac xa ka wa xe xh rpu1 ca ys c)(*strict*)
      apply(erule disjE)
       apply(rename_tac xa ka wa xe xh rpu1 ca ys c)(*strict*)
       apply(clarsimp)
       apply(rename_tac xa ka wa xe xh rpu1 ca ys c cb)(*strict*)
       apply (metis append_eq_append_conv2)
      apply(rename_tac xa ka wa xe xh rpu1 ca ys c)(*strict*)
      apply(clarsimp)
      apply(rename_tac xa ka wa xe xh rpu1 ca ys c cb)(*strict*)
      apply (metis append_eq_append_conv2)
     apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa ka wa xe xh f rpu1 ca ys c)(*strict*)
     apply(erule disjE)
      apply(rename_tac xa ka wa xe xh f rpu1 ca ys c)(*strict*)
      apply(clarsimp)
     apply(rename_tac xa ka wa xe xh f rpu1 ca ys c)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa ka wa xe xh f rpu1 ca ys c cb)(*strict*)
     apply(subgoal_tac "cb=ys@[parser_bottom G]")
      apply(rename_tac xa ka wa xe xh f rpu1 ca ys c cb)(*strict*)
      prefer 2
      apply (metis drop_append append_assoc)
     apply(rename_tac xa ka wa xe xh f rpu1 ca ys c cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa ka wa xe xh f rpu1 ca ys c)(*strict*)
     apply(rule_tac ?w1.0="f" and ?v1.0="xa" in prefix_alt_apply)
       apply(rename_tac xa ka wa xe xh f rpu1 ca ys c)(*strict*)
       apply(force)
      apply(rename_tac xa ka wa xe xh f rpu1 ca ys c)(*strict*)
      apply(simp add: prefix_def)
      apply(clarsimp)
      apply(rename_tac ka wa xe xh f rpu1 ca c cb)(*strict*)
      apply(subgoal_tac "c=cb @ ca")
       apply(rename_tac ka wa xe xh f rpu1 ca c cb)(*strict*)
       prefer 2
       apply (metis append_eq_conv_conj)
      apply(rename_tac ka wa xe xh f rpu1 ca c cb)(*strict*)
      apply(clarsimp)
      apply(rename_tac ka wa xe xh f rpu1 ca cb)(*strict*)
      apply(rule_tac x=" [parser_bottom G]" in exI)
      apply(force)
     apply(rename_tac xa ka wa xe xh f rpu1 ca ys c)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac xa ka wa xe xh rpu1 c cb)(*strict*)
     apply(thin_tac "set (drop (length xa + length cb) (take ka wa))
       \<subseteq> parser_events G - {parser_bottom G}")
     apply(thin_tac "butlast_if_match (take ka wa) (parser_bottom G) = take ka wa")
     apply(thin_tac "set (drop (length xa + length cb) (take ka wa)) \<subseteq> parser_events G")
     apply(thin_tac "set cb \<subseteq> parser_events G")
     apply(subgoal_tac "c=drop (length xa + length cb) (take ka wa)")
      apply(rename_tac xa ka wa xe xh rpu1 c cb)(*strict*)
      prefer 2
      apply (metis append_assoc append_eq_conv_conj length_append)
     apply(rename_tac xa ka wa xe xh rpu1 c cb)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa ka wa xe xh rpu1 cb)(*strict*)
     apply(rule_tac x=" [parser_bottom G]" in exI)
     apply(force)
    apply(rename_tac xa ka wa xe xf xh f lpo1 rpu1 lpo2 ca ys nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa ka xe xf xh f lpo1 lpo2 ca ys nat x)(*strict*)
    apply(subgoal_tac "ka = Suc nat+(length xh + length x)")
     apply(rename_tac xa ka xe xf xh f lpo1 lpo2 ca ys nat x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa ka xe xf xh f lpo1 lpo2 ca ys nat x)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xe xf xh f lpo1 lpo2 ca ys x)(*strict*)
    apply(rule_tac x="[]" in exI)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match ((xh @ x) @ [parser_bottom G]) (parser_bottom G) = xh@x")
     apply(rename_tac xa xe xf xh f lpo1 lpo2 ca ys x)(*strict*)
     prefer 2
     apply (metis butlast_if_match_direct)
    apply(rename_tac xa xe xf xh f lpo1 lpo2 ca ys x)(*strict*)
    apply(clarsimp)
    apply(thin_tac "butlast_if_match (xh @ x @ [parser_bottom G]) (parser_bottom G) =
       xh @ x")
    apply(thin_tac "xf @ lpo2 = xe @ lpo1")
    apply(subgoal_tac "ys=drop (length f) xa @ drop (length f - length xa) ca")
     apply(rename_tac xa xe xf xh f lpo1 lpo2 ca ys x)(*strict*)
     prefer 2
     apply (metis List.drop_append drop_append)
    apply(rename_tac xa xe xf xh f lpo1 lpo2 ca ys x)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xe xh f ca x)(*strict*)
    apply(erule_tac P="(\<exists>c. xa @ ca @ parser_bottom G # c = f)" in disjE)
     apply(rename_tac xa xe xh f ca x)(*strict*)
     apply(clarsimp)
    apply(rename_tac xa xe xh f ca x)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xe xh f ca x c)(*strict*)
    apply(subgoal_tac "c=drop (length f) xa @ drop (length f - length xa) ca@[parser_bottom G]")
     apply(rename_tac xa xe xh f ca x c)(*strict*)
     prefer 2
     apply(rule_tac w="f" in append_linj)
     apply(rule_tac t="f @ c" and s="xa @ ca @ [parser_bottom G]" in ssubst)
      apply(rename_tac xa xe xh f ca x c)(*strict*)
      apply(blast)
     apply(rename_tac xa xe xh f ca x c)(*strict*)
     apply(force)
    apply(rename_tac xa xe xh f ca x c)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xe xh f ca x)(*strict*)
    apply(erule disjE)
     apply(rename_tac xa xe xh f ca x)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa xe xh ca x c)(*strict*)
     apply (metis append_assoc in_set_conv_decomp not_set_append)
    apply(rename_tac xa xe xh f ca x)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa xe xh f ca x c)(*strict*)
    apply (metis set_butlast_if_match_subset ConsApp List.drop_append append_Cons append_Nil2 append_assoc append_eq_conv_conj butlast_if_match_direct butlast_if_match_pull_out drop_butlast_if_match_distrib empty_subsetI in_set_conv_decomp  not_set_append  prefix_def set_empty set_eq_subset)
   apply(rename_tac x xa xb ka wa xe xf c xh f lpo1 rpu1 lpo2 nat xc ca ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa ka wa xe xf c xh f lpo1 rpu1 lpo2 nat xc ca ys)(*strict*)
   apply(rule_tac w="xc" and v="ys" and r="wiX" and s="ca" and A="parser_bottom G" in elem_in_append_set)
     apply(rename_tac x xa ka wa xe xf c xh f lpo1 rpu1 lpo2 nat xc ca ys)(*strict*)
     apply(force)
    apply(rename_tac x xa ka wa xe xf c xh f lpo1 rpu1 lpo2 nat xc ca ys)(*strict*)
    apply (metis in_set_takeD nset_diff)
   apply(rename_tac x xa ka wa xe xf c xh f lpo1 rpu1 lpo2 nat xc ca ys)(*strict*)
   apply(force)
  apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 rpu1 lpo2 rpu2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "(\<exists>x. x @ [parser_bottom G] = take k w) \<longrightarrow>
       (\<exists>x. x @ [parser_bottom G] = rpu2)")
  apply(subgoal_tac "min (length w) k = k")
   apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 rpu1 lpo2 rpu2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 rpu1 lpo2 rpu2)(*strict*)
  apply(clarsimp)
  apply(rule_tac xs="drop k f" in rev_cases)
   apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 rpu1 lpo2 rpu2)(*strict*)
   apply(clarsimp)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac x xa xb k w ka wa xe xf c xg xh f lpo1 rpu1 lpo2 ca)(*strict*)
   apply (metis set_take_subset insert_subset nset_diff set_append2 set_simps(2) subset_trans)
  apply(rename_tac x xa xb k w ka wa xe xf c y xg xh wb f h lpo1 rpu1 lpo2 rpu2 ys ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xa xb k w ka wa xe xf c xg xh f h lpo1 rpu1 lpo2 rpu2 ys)(*strict*)
  apply(thin_tac "(rpu2 @ ys @ [parser_bottom G]) \<sqsupseteq> [parser_bottom G]")
  apply(subgoal_tac "xa=xg")
   apply(rename_tac x xa xb k w ka wa xe xf c xg xh f h lpo1 rpu1 lpo2 rpu2 ys)(*strict*)
   prefer 2
   apply (metis append_same_eq)
  apply(rename_tac x xa xb k w ka wa xe xf c xg xh f h lpo1 rpu1 lpo2 rpu2 ys)(*strict*)
  apply(thin_tac "xf @ lpo2 = xe @ lpo1")
  apply(clarsimp)
  apply(rename_tac x xb k w ka wa xe c xg xh f h rpu1 rpu2 ys)(*strict*)
  apply(rule_tac xs="xb" in rev_cases)
   apply(rename_tac x xb k w ka wa xe c xg xh f h rpu1 rpu2 ys)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xb k w ka wa xe c xg xh f h rpu1 rpu2 ys ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x k w ka wa xe c xg xh f h rpu1 rpu2 ys ysa)(*strict*)
  apply(rule_tac xs="f" in rev_cases)
   apply(rename_tac x k w ka wa xe c xg xh f h rpu1 rpu2 ys ysa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x k w ka wa xe c xg xh f h rpu1 rpu2 ys ysa ysb y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ys ysa ysb y)(*strict*)
  apply(case_tac "k - length ysb")
   apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ys ysa ysb y)(*strict*)
   prefer 2
   apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ys ysa ysb y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ys ysa ysb y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ysa ysb)(*strict*)
  apply(rule_tac xs="c" in rev_cases)
   apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ysa ysb)(*strict*)
   prefer 2
   apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ysa ysb ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x k w ka wa xe xg xh h rpu1 rpu2 ysa ysb ys)(*strict*)
   apply(rule_tac w="ysb" and v="ys" and r="wi @ rpu2" and s="drop k ysb" and A="parser_bottom G" in elem_in_append_set)
     apply(rename_tac x k w ka wa xe xg xh h rpu1 rpu2 ysa ysb ys)(*strict*)
     apply(force)
    apply(rename_tac x k w ka wa xe xg xh h rpu1 rpu2 ysa ysb ys)(*strict*)
    apply(clarsimp)
   apply(rename_tac x k w ka wa xe xg xh h rpu1 rpu2 ysa ysb ys)(*strict*)
   apply (metis in_set_takeD nset_diff)
  apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ysa ysb)(*strict*)
  apply(subgoal_tac "ysb @ parser_bottom G #[] =
       wi @ rpu2 @ drop k ysb @ [parser_bottom G]")
   apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ysa ysb)(*strict*)
   prefer 2
   apply(blast)
  apply(rename_tac x k w ka wa xe c xg xh h rpu1 rpu2 ysa ysb)(*strict*)
  apply(thin_tac "ysb @ parser_bottom G # c =
       wi @ rpu2 @ drop k ysb @ [parser_bottom G]")
  apply(clarsimp)
  apply(rename_tac x k w ka wa xe xh h rpu1 rpu2 ysa ca)(*strict*)
  apply(thin_tac " h \<sqsupseteq>
       butlast_if_match (wi @ rpu2 @ ysa @ [parser_bottom G])
        (parser_bottom G)")
  apply(thin_tac "drop (Suc (k + length ysa))
        (butlast_if_match
          (take ka wa @ take (ka - length wa) [parser_bottom G])
          (parser_bottom G)) =
       drop (Suc (k + length ysa))
        (butlast_if_match (wi @ rpu2) (parser_bottom G))")
  apply(rule_tac xs="ca" in rev_cases)
   apply(rename_tac x k w ka wa xe xh h rpu1 rpu2 ysa ca)(*strict*)
   prefer 2
   apply(rename_tac x k w ka wa xe xh h rpu1 rpu2 ysa ca ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa ys y)(*strict*)
   apply(case_tac "ka - length wa")
    apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa ys y)(*strict*)
    apply(clarsimp)
    apply(rule_tac w="wi @ rpu2 @ ysa" and v="ys@[y]" and r="take ka wa" and s="[]" and A="parser_bottom G" in elem_in_append_set)
      apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa ys y)(*strict*)
      apply(force)
     apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa ys y)(*strict*)
     apply (metis in_set_takeD nset_diff)
    apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa ys y)(*strict*)
    apply(force)
   apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa ys y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac x k w ka wa xe xh h rpu1 rpu2 ysa ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa)(*strict*)
  apply(case_tac "ka - length wa")
   apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa)(*strict*)
   apply(clarsimp)
   apply(rule_tac w="wi @ rpu2 @ ysa" and v="[]" and r="take ka wa" and s="[]" and A="parser_bottom G" in elem_in_append_set)
     apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa)(*strict*)
     apply(force)
    apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa)(*strict*)
    apply (metis in_set_takeD nset_diff)
   apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa)(*strict*)
   apply(force)
  apply(rename_tac x k w ka wa xe xh rpu1 rpu2 ysa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x k w ka xe xh rpu2 ysa nat xa)(*strict*)
  apply(subgoal_tac "ka  = Suc nat+(length wi + (length rpu2 + length ysa))")
   apply(rename_tac x k w ka xe xh rpu2 ysa nat xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x k w ka xe xh rpu2 ysa nat xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x k w xe xh rpu2 ysa xa)(*strict*)
  apply(subgoal_tac "x=xh")
   apply(rename_tac x k w xe xh rpu2 ysa xa)(*strict*)
   prefer 2
   apply (metis append_same_eq)
  apply(rename_tac x k w xe xh rpu2 ysa xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w xe xh rpu2 ysa xa)(*strict*)
  apply(rule_tac x="[]" in exI)
  apply(clarsimp)
  apply (metis List.length_take add_diff_cancel_left' append_Nil append_take_drop_id diff_is_0_eq' drop_eq_Nil drop_length_append length_append order_refl take_0)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step2_hlp: "
              valid_parser G \<Longrightarrow>
       ATS.derivation_initial parserHF_initial_configurations
        parserHF_step_relation G d \<Longrightarrow>
       parserHF_step_relation G c e1 c1 \<Longrightarrow>
       parserHF_step_relation G c e2a c2 \<Longrightarrow>
       d i = Some (pair e1a c) \<Longrightarrow>
       parserHF_conf_history c1 = parserHF_conf_history c @ hf2 \<Longrightarrow>
       parserHF_conf_history c2 = parserHF_conf_history c @ hf2 \<Longrightarrow>
       hf2 \<in> parser_markers G \<Longrightarrow>
       \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
       \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<Longrightarrow>
       \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
          parserHFS_conf_history = parserHF_conf_history c,
          parserHFS_conf_stack = parserHF_conf_stack c,
          parserHFS_conf_scheduler =
            wi @
            (if parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
             then parserHF_conf_fixed c2
             else parserHF_conf_fixed c2 @ [parser_bottom G])\<rparr>
       \<in> parserHFS_configurations G \<Longrightarrow>
       parserHFS_step_relation G
        \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
           parserHFS_conf_history = parserHF_conf_history c,
           parserHFS_conf_stack = parserHF_conf_stack c,
           parserHFS_conf_scheduler =
             wi @
             (if parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
              then parserHF_conf_fixed c2
              else parserHF_conf_fixed c2 @ [parser_bottom G])\<rparr>
        e2a
        \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c2,
           parserHFS_conf_history = parserHF_conf_history c @ hf2,
           parserHFS_conf_stack = parserHF_conf_stack c2,
           parserHFS_conf_scheduler =
             wix @
             (if parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G]
              then parserHF_conf_fixed c2
              else parserHF_conf_fixed c2 @ [parser_bottom G])\<rparr> \<Longrightarrow>
       (parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
        Ex (parserHFS_step_relation G
             \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
                parserHFS_conf_history = parserHF_conf_history c,
                parserHFS_conf_stack = parserHF_conf_stack c,
                parserHFS_conf_scheduler =
                  wi @
                  parserHF_conf_fixed c2\<rparr>
             e1)) \<and>
       (\<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
        Ex (parserHFS_step_relation G
             \<lparr>parserHFS_conf_fixed = parserHF_conf_fixed c,
                parserHFS_conf_history = parserHF_conf_history c,
                parserHFS_conf_stack = parserHF_conf_stack c,
                parserHFS_conf_scheduler =
                  wi @
                  parserHF_conf_fixed c2 @ [parser_bottom G]\<rparr>
             e1))"
  apply(rule conjI)
   apply(clarsimp)
   prefer 2
   apply(clarsimp)
   apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step2_hlp1)
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
  apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step2_hlp2)
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
  done

lemma parserHF_history_prefix_makes_equal: "
  valid_parser G
  \<Longrightarrow> hf1 \<in> parser_markers G
  \<Longrightarrow> hf2 \<in> parser_markers G
  \<Longrightarrow> ATS_History.history_fragment_prefixes parser_markers (@) G hf1 = ATS_History.history_fragment_prefixes parser_markers (@) G hf2
  \<Longrightarrow> hf1 = hf2"
  apply(subgoal_tac "prefix hf1 hf2")
   prefer 2
   apply(rule parserHF_history_prefix_makes_prefix)
    apply(force)
   apply(force)
  apply(subgoal_tac "prefix hf2 hf1")
   prefer 2
   apply(rule parserHF_history_prefix_makes_prefix)
    apply(force)
   apply(force)
  apply (metis mutual_prefix_implies_equality)
  done

lemma parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step2: "
    (\<forall>G. valid_parser G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial parserHF_initial_configurations
               parserHF_step_relation G d \<longrightarrow>
              (\<forall>c e1 c1.
                  parserHF_step_relation G c e1 c1 \<longrightarrow>
                  (\<forall>e2 c2.
                      parserHF_step_relation G c e2 c2 \<longrightarrow>
                      (\<forall>i. (\<exists>ei. d i = Some (pair ei c)) \<longrightarrow>
                           (\<forall>hf1. parserHF_conf_history c1 =
                                  parserHF_conf_history c @ hf1 \<longrightarrow>
                                  (\<forall>hf2.
parserHF_conf_history c2 = parserHF_conf_history c @ hf2 \<longrightarrow>
ATS_History.history_fragment_prefixes parser_markers (@) G hf1 =
ATS_History.history_fragment_prefixes parser_markers (@) G hf2 \<longrightarrow>
ATS.derivation_initial parserHFS_initial_configurations
 parserHFS_step_relation G
 (ATS_Branching_Versus_Linear1.Bra2LinDer parser_empty_scheduler_fragment
   (@) (@) parserHF_conf_fixed parserHFvHFS_Bra2LinConf
   parserHFvHFS_Bra2LinStep
   (\<lambda>G w. if w \<sqsupseteq> [parser_bottom G] then w else w @ [parser_bottom G]) G
   (derivation_append d (der2 c e2 c2) i) (Suc i)) \<longrightarrow>
hf1 \<in> parser_markers G \<longrightarrow>
hf2 \<in> parser_markers G \<longrightarrow>
(\<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow>
 \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G]) \<longrightarrow>
Ex (parserHFS_step_relation G
     (the (get_configuration
            (ATS_Branching_Versus_Linear1.Bra2LinDer
              parser_empty_scheduler_fragment (@) (@) parserHF_conf_fixed
              parserHFvHFS_Bra2LinConf parserHFvHFS_Bra2LinStep
              (\<lambda>G w. if w \<sqsupseteq> [parser_bottom G] then w
                     else w @ [parser_bottom G])
              G (derivation_append d (der2 c e2 c2) i) (Suc i) i)))
     e1))))))))"
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. SSd SSn = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2)(*strict*)
   prefer 2
   apply(rule_tac
      d="parserHF_vs_parserHFS.Bra2LinDer
          G (derivation_append d (der2 c e2 c2) i) (Suc i)"
      and n="i" and
      m="Suc i"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2)(*strict*)
    apply(simp add: parserHF_vs_parserHFS.Bra2LinDer_def derivation_append_def der2_def get_configuration_def parserHFvHFS_Bra2LinConf_def parserHF_vs_parserHFS.Bra2LinDer'_def parserHFvHFS_Bra2LinStep_def parser_empty_scheduler_fragment_def)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2)(*strict*)
   apply(force)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2)(*strict*)
  apply(erule exE)+
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2 e1a e2a c1a c2a)(*strict*)
  apply(subgoal_tac "c1a \<in> parserHFS_configurations G")
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2 e1a e2a c1a c2a)(*strict*)
   prefer 2
   apply(rule_tac e="e1a" and i="i" in parserHFS.belongs_configurations)
    apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2 e1a e2a c1a c2a)(*strict*)
    apply(rule parserHFS.derivation_initial_belongs)
     apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2 e1a e2a c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2 e1a e2a c1a c2a)(*strict*)
    apply(force)
   apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2 e1a e2a c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac G d c e1 c1 e2 c2 i ei hf1 hf2 e1a e2a c1a c2a)(*strict*)
  apply(thin_tac "parserHFS.derivation_initial G
        (parserHF_vs_parserHFS.Bra2LinDer
          G (derivation_append d (der2 c e2 c2) i) (Suc i))")
  apply(simp only: parserHF_vs_parserHFS.Bra2LinDer_def get_configuration_def derivation_append_def der2_def)
  apply(simp add: parserHFvHFS_Bra2LinConf_def)
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 c2 i hf1 hf2 e1a e2a)(*strict*)
  apply(subgoal_tac "hf1=hf2")
   apply(rename_tac G d c e1 c1 c2 i hf1 hf2 e1a e2a)(*strict*)
   prefer 2
   apply(rule parserHF_history_prefix_makes_equal)
      apply(rename_tac G d c e1 c1 c2 i hf1 hf2 e1a e2a)(*strict*)
      apply(force)
     apply(rename_tac G d c e1 c1 c2 i hf1 hf2 e1a e2a)(*strict*)
     apply(force)
    apply(rename_tac G d c e1 c1 c2 i hf1 hf2 e1a e2a)(*strict*)
    apply(force)
   apply(rename_tac G d c e1 c1 c2 i hf1 hf2 e1a e2a)(*strict*)
   apply(force)
  apply(rename_tac G d c e1 c1 c2 i hf1 hf2 e1a e2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d c e1 c1 c2 i hf2 e1a e2a)(*strict*)
  apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step2_hlp)
            apply(rename_tac G d c e1 c1 c2 i hf2 e1a e2a)(*strict*)
            apply(force)+
  done

lemma parserHF_vs_parserHFS_inst_ATS_Branching_Versus_Linear2_axioms: "
  ATS_Branching_Versus_Linear2_axioms valid_parser
     parserHFS_configurations parserHFS_initial_configurations
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect
     parser_fixed_scheduler_extendable parser_scheduler_fragments
     parser_empty_scheduler_fragment (@) right_quotient_word (@)
     parser_unfixed_scheduler_extendable parser_schedulers
     parser_empty_scheduler parserHFS_get_scheduler (@)
     parserHFS_get_unfixed_scheduler parserHFS_set_unfixed_scheduler
     parserHFS_conf_fixed parser_markers parser_empty_history_fragment (@)
     (@) parserHF_configurations parserHF_initial_configurations
     parserHF_step_relation parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect
     parser_empty_fixed_scheduler parser_fixed_scheduler_extendable
     parserHF_conf_fixed parserHF_conf_history parserHFvHFS_Lin2BraConf
     parserHFvHFS_Bra2LinConf parserHFvHFS_Bra2LinStep
     (\<lambda>G w. if w \<sqsupseteq> [parser_bottom G] then w else w @ [parser_bottom G]) "
  apply(simp only: ATS_Branching_Versus_Linear2_axioms_def)
  apply(rule conjI)+
      apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinConf_triv_with_get_scheduler)
     apply(simp)
     apply(rule parserHF_vs_parserHFS_inst_AX_Lin2BraDer_preserves_marking_condition)
    apply(rule conjI)+
     apply(simp)
     apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_preserves_marking_condition)
    apply(rule conjI)+
     apply(simp)
     apply(rule parserHFvHFS_inst_AX_Bra2LinConf_on_empty_bra_sched_closed)
    apply(simp add: suffix_def)
   apply(rule conjI)+
     apply(simp)
     apply(rule parserHF_vs_parserHFS_inst_AX_Lin2BraConf_Bra2LinConf_idemp)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule parserHF_vs_parserHFS_inst_AX_set_constructed_sched_vs_set_constructed_schedUF_prime_prime)
    apply(rule allI)+
    apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
    apply(rule impI)+
    apply(erule_tac x="G" in allE)
    apply(erule_tac x="c1L" in allE)
    apply(erule_tac x="c3L" in allE)
    apply(erule_tac x="cB" in allE)
    apply(erule_tac x="e" in allE)
    apply(erule_tac x="c2L" in allE)
    apply(erule_tac x="sE3" in allE)
    apply(erule_tac x="sE2" in allE)
    apply(erule_tac x="sE1" in allE)
    apply(erule impE)
     apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
    apply(erule impE)
     apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
    apply(erule impE)
     apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
    apply(erule impE)
     apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
    apply(erule impE)
     apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
    apply(erule impE)
     apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
     apply(force)
    apply(rename_tac G c1L c3L cB e c2L sL sLUF sE2 sE3 sE1)(*strict*)
    apply(force)
   apply(rule conjI)+
    apply(rule parserHF_vs_parserHFS_inst_AX_lin_unfixed_scheduler_right_quotient_drop_proper2)
   apply(rule conjI)+
    apply(rule parserHF_vs_parserHFS_inst_AX_Lin2BraConf_ignores_set_unfixed_scheduler)
   apply(rule parserHF_vs_parserHFS_inst_AX_Lin2BraConf_preserves_fixed_scheduler_extendable)
  apply(rule conjI)+
     apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinStep_Bra2LinFin_compatible)
    apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinFin_takes_entire_fixed_scheduler)
   apply(rule conjI)+
    apply(rule parserHF_vs_parserHFS_inst_AX_combine_consumed_and_remaining_scheduler)
   apply(rule conjI)+
    apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinConf_Lin2BraConf_idemp_on_get_scheduler)
   apply(rule parserHF_vs_parserHFS_inst_AX_bra2lin_preserves_unmarked_effect)
  apply(rule conjI)+
    apply(rule parserHF_vs_parserHFS_inst_AX_lin2bra_preserves_unmarked_effect)
   apply(rule conjI)+
    apply(rule parserHF_vs_parserHFS_inst_AX_bra2lin_preserves_marked_effect)
   apply(rule parserHF_vs_parserHFS_inst_AX_lin2bra_preserves_marked_effect)
  apply(rule conjI)+
   apply(simp)
   apply(rule parserHF_vs_parserHFS_inst_AX_Lin2BraConf_enforces_compatible_history_fragment_SB)
  apply(rule conjI)+
   apply(simp)
   apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step1)
  apply(simp)
  apply(rule parserHF_vs_parserHFS_inst_AX_Bra2LinDer_allows_slim_step2)
  done

interpretation "parserHF_vs_parserHFS" : ATS_Branching_Versus_Linear2
  (* TSstructure *)
  "valid_parser"
  (* lin_configurations *)
  "parserHFS_configurations"
  (* lin_initial_configurations *)
  "parserHFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* lin_step_relation *)
  "parserHFS_step_relation"
  (* effects *)
  "parser_markers"
  (* lin_marking_condition *)
  "parserHFS_marking_condition"
  (* lin_marked_effect *)
  "parserHFS_marked_effect"
  (* lin_unmarked_effect *)
  "parserHFS_unmarked_effect"
  (* lin_fixed_schedulers *)
  "parser_fixed_schedulers"
  (* lin_empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* lin_fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* lin_scheduler_fragments *)
  "parser_scheduler_fragments"
  (* lin_empty_scheduler_fragment *)
  "parser_empty_scheduler_fragment"
  (* lin_join_scheduler_fragments *)
  "append"
  (* lin_unfixed_schedulers *)
  "parser_unfixed_schedulers"
  (* lin_empty_unfixed_scheduler *)
  "parser_empty_unfixed_scheduler"
  (* lin_unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* lin_extend_unfixed_scheduler *)
  "append"
  (* lin_unfixed_scheduler_extendable *)
  "parser_unfixed_scheduler_extendable"
  (* lin_schedulers *)
  "parser_schedulers"
  (* lin_initial_schedulers *)
  "parser_schedulers"
  (* lin_empty_scheduler *)
  "parser_empty_scheduler"
  (* lin_get_scheduler *)
  "parserHFS_get_scheduler"
  (* lin_join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* lin_extend_scheduler *)
  "append"
  (* lin_get_unfixed_scheduler *)
  "parserHFS_get_unfixed_scheduler"
  (* lin_set_unfixed_scheduler *)
  "parserHFS_set_unfixed_scheduler"
  (* lin_get_fixed_scheduler *)
  "parserHFS_conf_fixed"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* lin_set_history *)
  "parserHFS_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* lin_get_history *)
  "parserHFS_conf_history"
  (* bra_configurations *)
  "parserHF_configurations"
  (* bra_initial_configurations *)
  "parserHF_initial_configurations"
  (* bra_step_relation *)
  "parserHF_step_relation"
  (* bra_marking_condition *)
  "parserHF_marking_condition"
  (* bra_marked_effect *)
  "parserHF_marked_effect"
  (* bra_unmarked_effect *)
  "parserHF_unmarked_effect"
  (* bra_fixed_schedulers *)
  "parser_fixed_schedulers"
  (* bra_empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* bra_fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* bra_get_fixed_scheduler *)
  "parserHF_conf_fixed"
  (* bra_set_history *)
  "parserHF_set_history"
  (* bra_get_history *)
  "parserHF_conf_history"
  (* Lin2BraConf *)
  "parserHFvHFS_Lin2BraConf"
  (* Bra2LinConf *)
  "parserHFvHFS_Bra2LinConf"
  (* Bra2LinStep *)
  "parserHFvHFS_Bra2LinStep"
  (* Bra2LinFin *)
  "\<lambda>G w. if (suffix w [parser_bottom G]) then w else w@[parser_bottom G]"
  apply(simp add: LOCALE_DEFS parserHF_interpretations parserHFS_interpretations0)
  apply(simp add: parserHF_vs_parserHFS_inst_ATS_Branching_Versus_Linear1_axioms parserHF_vs_parserHFS_inst_ATS_Branching_Versus_Linear2_axioms)
  done

theorem parserHFS2HF_DEdetermR_FEdetermHist_DB: "
  valid_parser G
  \<Longrightarrow> parserHFS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> parserHF.is_forward_edge_deterministicHist_DB_long G"
  apply(simp add: parserHF.is_forward_edge_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
  apply(case_tac "w1=w2")
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
   apply(simp add: parserHFS.is_forward_edge_deterministic_accessible_def)
   apply(case_tac "parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]")
    apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
    apply(subgoal_tac "w2=[]")
     apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
     prefer 2
     apply(rule_tac
      c="c"
      in no_history_extension_if_already_unextendable)
         apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
         apply(force)
        apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
        apply(simp add: get_configuration_def)
        apply(case_tac "d n")
         apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
         apply(force)
        apply(rename_tac c d n c1 c2 e1 e2 w2 a)(*strict*)
        apply(clarsimp)
        apply(case_tac a)
        apply(rename_tac c d n c1 c2 e1 e2 w2 a option b)(*strict*)
        apply(clarsimp)
        apply(rename_tac c d n c1 c2 e1 e2 w2 option)(*strict*)
        apply(subgoal_tac "c \<in> parserHF_configurations G")
         apply(rename_tac c d n c1 c2 e1 e2 w2 option)(*strict*)
         prefer 2
         apply(rule_tac
      d="d"
      in parserHF.belongs_configurations)
          apply(rename_tac c d n c1 c2 e1 e2 w2 option)(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac c d n c1 c2 e1 e2 w2 option)(*strict*)
         apply (metis parserHF.derivation_initial_belongs)
        apply(rename_tac c d n c1 c2 e1 e2 w2 option)(*strict*)
        apply(clarsimp)
       apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
     apply(force)
    apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
    apply(rule parserHFS2HF_FEdetermHist_hlp2)
            apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
            apply(force)
           apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
           apply(force)
          apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
          apply(force)
         apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
         apply(force)
        apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
     apply(force)
    apply(rename_tac c d n c1 c2 e1 e2)(*strict*)
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
   apply(subgoal_tac "(suffix (parserHF_conf_fixed c1) [parser_bottom G] \<longrightarrow> (suffix (parserHF_conf_fixed c2) [parser_bottom G])) \<or> ((suffix (parserHF_conf_fixed c2) [parser_bottom G]) \<longrightarrow> (suffix (parserHF_conf_fixed c1) [parser_bottom G]))")
    apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
   apply(erule disjE)
    apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
    prefer 2
    apply(rule parserHFS2HF_FEdetermHist_hlp1)
             apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
             apply(force)
            apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
            apply(force)
           apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
           apply(force)
          apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
          apply(force)
         apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
         apply(force)
        apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
     apply(force)
    apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
   apply(rule sym)
   apply(rule parserHFS2HF_FEdetermHist_hlp1)
            apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
            apply(force)
           apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
           apply(force)
          apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
          apply(force)
         apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
         apply(force)
        apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
     apply(force)
    apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w2)(*strict*)
   apply(force)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac "d n")
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2)(*strict*)
   apply(force)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
  apply(subgoal_tac "c \<in> parserHF_configurations G")
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in parserHF.belongs_configurations)
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   apply (metis parserHF.derivation_initial_belongs)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
  apply(case_tac "ATS_History.history_fragment_prefixes parser_markers (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<and> \<not> parserHF_get_fixed_scheduler_DB G (derivation_append d (der2 c e1 c1) n) (Suc n) \<sqsupseteq> [parser_bottom G]")
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule parserHFS2HF_FEdetermHist_hlp3)
              apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
              apply(force)
             apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
             apply(force)
            apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
            apply(force)
           apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
           apply(force)
          apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
          apply(force)
         apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
         apply(force)
        apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
     apply(force)
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   apply(force)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
  apply(erule disjE)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   apply(force)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
  apply(erule disjE)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   prefer 2
   apply(simp add: parserHF.history_fragment_prefixes_def)
   apply(subgoal_tac "w1=w2")
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   apply(subgoal_tac "w1 \<in> parser_markers G")
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
    apply(subgoal_tac "w2 \<in> parser_markers G")
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
     apply(subgoal_tac "[] \<in> parser_markers G")
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
      apply(rule mutual_prefix_implies_equality)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
       apply(subgoal_tac "w1 \<in> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}")
        apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
        apply(thin_tac "{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2} = {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}")
        apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
        apply(simp add: prefix_def)
        apply(clarsimp)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
       apply(rule_tac
      t="{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}"
      and s="{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}"
      in ssubst)
        apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
      apply(subgoal_tac "w2 \<in> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}")
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
       apply(thin_tac "{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2} = {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}")
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
       apply(simp add: prefix_def)
       apply(clarsimp)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
      apply(rule_tac
      s="{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}"
      and t="{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}"
      in ssubst)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
     apply(simp add: parser_markers_def)
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
    apply(simp add: parser_markers_def)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   apply(simp add: parser_markers_def)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
  apply(rule parserHFS2HF_FEdetermHist_hlp3)
             apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
             apply(force)
            apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
            apply(force)
           apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
           apply(force)
          apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
          apply(force)
         apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
         apply(force)
        apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
        apply(force)
       apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
       apply(force)
      apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
      apply(force)
     apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
     apply(force)
    apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
    apply(force)
   apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
   apply(force)
  apply(rename_tac c d n c1 c2 e1 e2 w1 w2 option)(*strict*)
  apply(force)
  done

corollary parserHFS2HF_FEdetermHist: "
  valid_parser G
  \<Longrightarrow> parserHFS.is_forward_edge_deterministicHist_DB_long G
  \<Longrightarrow> parserHF.is_forward_edge_deterministicHist_DB_long G"
  apply (metis parserHFS.AX_is_forward_edge_deterministic_correspond_DB_SB parserHFS.AX_is_forward_edge_deterministic_correspond_SB parserHFS2HF_DEdetermR_FEdetermHist_DB)
  done

theorem parserHF_vs_parserHFS_Nonblockingness_and_lang_transfer: "
  valid_parser G
  \<Longrightarrow> (parserHFS.Nonblockingness_linear_DB G \<longleftrightarrow> parserHF.Nonblockingness_branching G) \<and> parserHFS.unmarked_language G = parserHF.unmarked_language G \<and> parserHFS.marked_language G = parserHF.marked_language G"
  apply(rule conjI)
   apply(rule order_antisym)
    apply(clarsimp)
    apply(rule parserHF_vs_parserHFS.bflin_to_bfbra)
     apply(force)+
    apply(metis parserHFS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
   apply(clarsimp)
   apply(metis parserHF_vs_parserHFS.bfbra_to_bflin parserHFS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  apply(rule conjI)
   apply(rule order_antisym)
    apply(rule_tac
      t="parserHFS.unmarked_language G"
      and s="parserHFS.finite_unmarked_language G"
      in ssubst)
     apply (metis parserHFS.AX_unmarked_language_finite)
    apply (metis parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_unmarked_language_translation2)
   apply(rule_tac
      t="parserHF.unmarked_language G"
      and s="parserHF.finite_unmarked_language G"
      in ssubst)
    apply (metis parserHF.AX_unmarked_language_finite)
   apply (metis parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_unmarked_language_translation1)
  apply(rule order_antisym)
   apply(rule_tac
      t="parserHFS.marked_language G"
      and s="parserHFS.finite_marked_language G"
      in ssubst)
    apply (metis parserHFS.AX_marked_language_finite)
   apply (metis parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_marked_language_translation2)
  apply(rule_tac
      t="parserHF.marked_language G"
      and s="parserHF.finite_marked_language G"
      in ssubst)
   apply (metis parserHF.AX_marked_language_finite)
  apply (metis parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_marked_language_translation1)
  done

lemma parserHFS_inst_hlp_BF_LinSBRest_DetR_LaOp: "
  valid_parser G
  \<Longrightarrow> parserHFS.is_forward_deterministic_accessible G
  \<Longrightarrow> nonblockingness_language (parserHFS.unmarked_language G) (parserHFS.marked_language G)
  \<Longrightarrow> parserHFS.Nonblockingness_linear_restricted G"
  apply(rule parserHF_vs_parserHFS.bfbra_to_bflin_rest)
   apply(force)
  apply(rule parserHF.AX_BF_BraSBRest_DetHDB_LaOp)
    apply(force)
   apply(rule_tac
      t="parserHF.is_forward_deterministicHist_SB G"
      and s="parserHF.is_forward_deterministicHist_DB G"
      in ssubst)
    apply(rule parserHF.is_forward_deterministic_correspond_DB_SB)
    apply(force)
   apply(simp only: parserHF.is_forward_deterministicHist_DB_def)
   apply(rule conjI)
    apply(rule parserHF_is_forward_target_deterministicHist_DB_long)
    apply(force)
   apply(rule parserHFS2HF_FEdetermHist)
    apply(force)
   apply(rule parserHFS.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
    apply(force)
   apply(simp add: parserHFS.is_forward_deterministic_accessible_def)
  apply(rule_tac
      t="parserHF.unmarked_language G"
      and s="parserHFS.unmarked_language G"
      in ssubst)
   apply(metis parserHF_vs_parserHFS_Nonblockingness_and_lang_transfer)
  apply(rule_tac
      t="parserHF.marked_language G"
      and s="parserHFS.marked_language G"
      in ssubst)
   apply(metis parserHF_vs_parserHFS_Nonblockingness_and_lang_transfer)
  apply(force)
  done

lemma parserHFS_inst_hlp_BF_LinDBRest_DetR_LaOp: "
  valid_parser G
  \<Longrightarrow> parserHFS.is_forward_deterministic_accessible G
  \<Longrightarrow> nonblockingness_language (parserHFS.unmarked_language G) (parserHFS.marked_language G)
  \<Longrightarrow> parserHFS.Nonblockingness_linear_restricted_DB G"
  apply(rule_tac
      t="parserHFS.Nonblockingness_linear_restricted_DB G"
      and s="parserHFS.Nonblockingness_linear_restricted G"
      in ssubst)
   apply (metis parserHFS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB)
  apply (metis parserHFS_inst_hlp_BF_LinSBRest_DetR_LaOp)
  done

lemma parserHFS_inst_BF_LinDBRest_DetR_LaOp_axioms: "
  BF_LinDBRest_DetR_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect
     parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_get_scheduler (@)
     parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB
     parserHFS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDBRest_DetR_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(metis parserHFS_inst_hlp_BF_LinDBRest_DetR_LaOp)
  done

lemma parserHFS_inst_BF_LinDBRest_DetHDB_LaOp_axioms: "
  BF_LinDBRest_DetHDB_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect parser_markers (@)
     (@) parserHFS_conf_history parser_fixed_scheduler_extendable
     parserHFS_get_fixed_scheduler_DB parser_unfixed_schedulers
     right_quotient_word (@) parser_unfixed_scheduler_extendable
     parserHFS_get_scheduler (@) parserHFS_set_unfixed_scheduler_DB
     parserHFS_get_unfixed_scheduler_DB"
  apply(simp add: BF_LinDBRest_DetHDB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinDBRest_DetR_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect
     parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_get_scheduler (@)
     parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB
     parserHFS_get_fixed_scheduler_DB")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_BF_LinDBRest_DetR_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinDBRest_DetR_LaOp_axioms_def)
  apply(erule_tac
      x="M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (parserHFS.unmarked_language M) (parserHFS.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply(simp add: parserHFS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rename_tac M)(*strict*)
   apply (metis parserHFS_is_forward_target_deterministic_accessible)
  apply(rename_tac M)(*strict*)
  apply(simp add: parserHFS.is_forward_deterministicHist_DB_def)
  apply(clarsimp)
  apply(thin_tac "ATS_determHIST_DB.is_forward_target_deterministicHist_DB_long parserHFS_initial_configurations parserHFS_step_relation parser_markers (@) (@) parserHFS_conf_history parser_fixed_scheduler_extendable parserHFS_get_fixed_scheduler_DB M")
  apply(rename_tac M)(*strict*)
  apply (metis parserHFS.AX_is_forward_edge_deterministic_correspond_DB_SB parserHFS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  done

lemma parserHFS_inst_BF_LinDBRest_DetHSB_LaOp_axioms: "
  BF_LinDBRest_DetHSB_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect parser_markers (@)
     (@) parserHFS_conf_history parser_fixed_scheduler_extendable
     parserHFS_conf_fixed parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_get_scheduler (@)
     parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB
     parserHFS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDBRest_DetHSB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinDBRest_DetR_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect
     parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_get_scheduler (@)
     parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB
     parserHFS_get_fixed_scheduler_DB ")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_BF_LinDBRest_DetR_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinDBRest_DetR_LaOp_axioms_def)
  apply(erule_tac
      x="M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (parserHFS.unmarked_language M) (parserHFS.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply(simp add: parserHFS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rename_tac M)(*strict*)
   apply (metis parserHFS_is_forward_target_deterministic_accessible)
  apply(rename_tac M)(*strict*)
  apply(simp add: parserHFS.is_forward_deterministicHist_SB_def)
  apply(clarsimp)
  apply (metis parserHFS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  done

lemma parserHFS_inst_BF_LinSBRest_DetR_LaOp_axioms: "
  BF_LinSBRest_DetR_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect right_quotient_word
     (@) parser_unfixed_scheduler_extendable
     parserHFS_set_unfixed_scheduler parserHFS_get_unfixed_scheduler"
  apply(simp add: BF_LinSBRest_DetR_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply (metis parserHFS_inst_hlp_BF_LinSBRest_DetR_LaOp)
  done

lemma parserHFS_inst_BF_LinSBRest_DetHDB_LaOp_axioms: "
  BF_LinSBRest_DetHDB_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect parser_markers (@)
     (@) parserHFS_conf_history parser_fixed_scheduler_extendable
     parserHFS_get_fixed_scheduler_DB right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_set_unfixed_scheduler
     parserHFS_get_unfixed_scheduler"
  apply(simp add: BF_LinSBRest_DetHDB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinSBRest_DetR_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect right_quotient_word
     (@) parser_unfixed_scheduler_extendable
     parserHFS_set_unfixed_scheduler parserHFS_get_unfixed_scheduler")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_BF_LinSBRest_DetR_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinSBRest_DetR_LaOp_axioms_def)
  apply(erule_tac
      x="M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (parserHFS.unmarked_language M) (parserHFS.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply(simp add: parserHFS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rename_tac M)(*strict*)
   apply (metis parserHFS_is_forward_target_deterministic_accessible)
  apply(rename_tac M)(*strict*)
  apply(simp add: parserHFS.is_forward_deterministicHist_DB_def)
  apply(clarsimp)
  apply (metis parserHFS.AX_is_forward_edge_deterministic_correspond_DB_SB parserHFS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  done

lemma parserHFS_inst_BF_LinSBRest_DetHSB_LaOp_axioms: "
  BF_LinSBRest_DetHSB_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect parser_markers (@)
     (@) parserHFS_conf_history parser_fixed_scheduler_extendable
     parserHFS_conf_fixed right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_set_unfixed_scheduler
     parserHFS_get_unfixed_scheduler"
  apply(simp add: BF_LinSBRest_DetHSB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinSBRest_DetHDB_LaOp_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect parser_markers (@)
     (@) parserHFS_conf_history parser_fixed_scheduler_extendable
     parserHFS_get_fixed_scheduler_DB right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_set_unfixed_scheduler
     parserHFS_get_unfixed_scheduler")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_BF_LinSBRest_DetHDB_LaOp_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinSBRest_DetHDB_LaOp_axioms_def)
  apply(erule_tac
      x="M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (parserHFS.unmarked_language M) (parserHFS.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply (metis parserHFS.is_forward_deterministic_correspond_DB_SB)
  done

lemma parserHFS_inst_BF_LinSB_OpLa_axioms: "
  BF_LinSB_OpLa_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect right_quotient_word
     (@) parser_unfixed_scheduler_extendable
     parserHFS_set_unfixed_scheduler parserHFS_get_unfixed_scheduler"
  apply(simp add: BF_LinSB_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      s="parserHF.unmarked_language M"
      and t="parserHFS.unmarked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply(metis parserHF_vs_parserHFS_Nonblockingness_and_lang_transfer)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      s="parserHF.marked_language M"
      and t="parserHFS.marked_language M"
      in ssubst)
   apply(rename_tac M)(*strict*)
   apply(metis parserHF_vs_parserHFS_Nonblockingness_and_lang_transfer)
  apply(rename_tac M)(*strict*)
  apply(rule parserHF.AX_BF_Bra_OpLa)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply (metis parserHF_vs_parserHFS.bflin_to_bfbra)
  done

lemma parserHFS_inst_BF_LinDB_OpLa_axioms: "
  BF_LinDB_OpLa_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect
     parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_get_scheduler (@)
     parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB
     parserHFS_get_fixed_scheduler_DB"
  apply(simp add: BF_LinDB_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_LinSB_OpLa_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect right_quotient_word
     (@) parser_unfixed_scheduler_extendable
     parserHFS_set_unfixed_scheduler parserHFS_get_unfixed_scheduler")
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_BF_LinSB_OpLa_axioms)
  apply(rename_tac M)(*strict*)
  apply(simp add: BF_LinSB_OpLa_axioms_def)
  apply(erule_tac
      x="M"
      in allE)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(erule impE)
   apply(rename_tac M)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac M)(*strict*)
  apply (metis parserHFS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  done

interpretation "parserHFS" : loc_autHFS_10
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHFS_configurations"
  (* initial_configurations *)
  "parserHFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHFS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHFS_marking_condition"
  (* marked_effect *)
  "parserHFS_marked_effect"
  (* unmarked_effect *)
  "parserHFS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHFS_get_destinations"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* set_history *)
  "parserHFS_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "parserHFS_conf_history"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserHFS_string_state"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* scheduler_fragments *)
  "parser_scheduler_fragments"
  (* empty_scheduler_fragment *)
  "parser_empty_scheduler_fragment"
  (* join_scheduler_fragments *)
  "append"
  (* unfixed_schedulers *)
  "parser_unfixed_schedulers"
  (* empty_unfixed_scheduler *)
  "parser_empty_unfixed_scheduler"
  (* unfixed_scheduler_right_quotient_word *)
  "right_quotient_word"
  (* extend_unfixed_scheduler *)
  "append"
  (* unfixed_scheduler_extendable *)
  "parser_unfixed_scheduler_extendable"
  (* schedulers *)
  "parser_schedulers"
  (* initial_schedulers *)
  "parser_schedulers"
  (* empty_scheduler *)
  "parser_empty_scheduler"
  (* get_scheduler *)
  "parserHFS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler *)
  "parserHFS_set_unfixed_scheduler"
  (* get_unfixed_scheduler *)
  "parserHFS_get_unfixed_scheduler"
  (* get_fixed_scheduler *)
  "parserHFS_conf_fixed"
  (* set_unfixed_scheduler_DB *)
  "parserHFS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserHFS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserHFS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parserHF_interpretations parserHFS_interpretations0)
  apply(simp add: parserHFS_inst_BF_LinDBRest_DetR_LaOp_axioms parserHFS_inst_BF_LinDBRest_DetHDB_LaOp_axioms parserHFS_inst_BF_LinDBRest_DetHSB_LaOp_axioms parserHFS_inst_BF_LinSBRest_DetR_LaOp_axioms parserHFS_inst_BF_LinSBRest_DetHDB_LaOp_axioms parserHFS_inst_BF_LinSBRest_DetHSB_LaOp_axioms parserHFS_inst_BF_LinSB_OpLa_axioms parserHFS_inst_BF_LinDB_OpLa_axioms parserHFS_inst_ATS_HistoryCE_DB_axioms )
  done

lemma set_drop_subset2: "
  set w \<subseteq> A
  \<Longrightarrow> set(drop n w) \<subseteq> A"
  apply(induct w arbitrary: n)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w n)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w n x)(*strict*)
  apply(case_tac n)
   apply(rename_tac a w n x)(*strict*)
   apply(clarsimp)
   apply(rename_tac a w x)(*strict*)
   apply(force)
  apply(rename_tac a w n x nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w x nat)(*strict*)
  apply(force)
  done

lemma prefix_common: "
  prefix a c
  \<Longrightarrow> prefix b c
  \<Longrightarrow> prefix a b \<or> prefix b a"
  apply (metis mutual_prefix_prefix prefix_def)
  done

lemma prefix_closure_subset_to_prefix: "
  (prefix_closure {w} \<subseteq> prefix_closure {v})
  = (prefix w v)"
  apply (metis insert_subset prefixExists prefix_closure_idempotent prefix_closure_single_prefix prefix_closure_subset prefix_closure_subset2 prefix_def)
  done

lemma parserHF_parserHFS_preserve_determ_hlp1: "
       parserHFS_step_relation G ci e1 c1 \<Longrightarrow>
       parserHFS_conf_history c1 = parserHFS_conf_history ci @ w1 \<Longrightarrow>
       ci \<in> parserHFS_configurations G \<Longrightarrow>
       c1 \<in> parserHFS_configurations G \<Longrightarrow>
       valid_parser_step_label G e1 \<Longrightarrow>
       w1 \<sqsubseteq> drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci)"
  apply(simp add: parserHFS_step_relation_def Let_def parserHFS_configurations_def prefix_def)
  apply(clarsimp)
  apply(rename_tac f h x xa c ca y w)(*strict*)
  apply(rule_tac
      xs="xa"
      in rev_cases)
   apply(rename_tac f h x xa c ca y w)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h x c y w)(*strict*)
   apply(rule_tac
      xs="c"
      in rev_cases)
    apply(rename_tac f h x c y w)(*strict*)
    apply(clarsimp)
    apply(rename_tac h x y w)(*strict*)
    apply(rule butlast_if_match_length_le)
   apply(rename_tac f h x c y w ys ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h x y w ys ya)(*strict*)
   apply(subgoal_tac "f @ ys = w")
    apply(rename_tac f h x y w ys ya)(*strict*)
    prefer 2
    apply (metis append1_eq_conv append_assoc)
   apply(rename_tac f h x y w ys ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h x y ys ya)(*strict*)
   apply(subgoal_tac "ya=parser_bottom G")
    apply(rename_tac f h x y ys ya)(*strict*)
    prefer 2
    apply (metis empty_iff insert_iff list.set(1) same_append_eq set_simps(2))
   apply(rename_tac f h x y ys ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h x y ys)(*strict*)
   apply(subgoal_tac "butlast_if_match (rule_rpop e1) (parser_bottom G) = f@ys")
    apply(rename_tac f h x y ys)(*strict*)
    prefer 2
    apply (metis (erased, hide_lams) append_assoc butlast_if_match_direct)
   apply(rename_tac f h x y ys)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast_if_match (y @ [parser_bottom G]) (parser_bottom G) = y")
    apply(rename_tac f h x y ys)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct)
   apply(rename_tac f h x y ys)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast_if_match f (parser_bottom G) = f")
    apply(rename_tac f h x y ys)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct2_prime)
   apply(rename_tac f h x y ys)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="drop (length f) (rule_rpop e1)"
      and s="ys @ [parser_bottom G]"
      in ssubst)
    apply(rename_tac f h x y ys)(*strict*)
    apply(rule_tac
      t="rule_rpop e1"
      and s="f@ys @ [parser_bottom G]"
      in ssubst)
     apply(rename_tac f h x y ys)(*strict*)
     apply(force)
    apply(rename_tac f h x y ys)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac f h x y ys)(*strict*)
   apply(force)
  apply(rename_tac f h x xa c ca y w ys ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h x c ca ys)(*strict*)
  apply(rule_tac
      xs="c"
      in rev_cases)
   apply(rename_tac f h x c ca ys)(*strict*)
   apply(clarsimp)
   apply(rename_tac h x ys)(*strict*)
   apply(rule_tac
      j="length (rule_rpop e1)"
      in le_trans)
    apply(rename_tac h x ys)(*strict*)
    apply(rule butlast_if_match_length_le)
   apply(rename_tac h x ys)(*strict*)
   apply(force)
  apply(rename_tac f h x c ca ys ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h x ca ys ysa)(*strict*)
  apply(case_tac e1)
  apply(rename_tac f h x ca ys ysa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h x ca ys ysa rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
  apply(rename_tac lpop rpop lpush rpush)
  apply(rename_tac f h x ca ys ysa lpop rpop lpush rpush)(*strict*)
  apply(subgoal_tac "prefix f rpop \<or> prefix rpop f")
   apply(rename_tac f h x ca ys ysa lpop rpop lpush rpush)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac f h x ca ys ysa lpop rpop lpush rpush)(*strict*)
  apply(erule disjE)
   apply(rename_tac f h x ca ys ysa lpop rpop lpush rpush)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac h x ysa lpop rpop lpush rpush c)(*strict*)
   apply(rule_tac
      t="drop (length rpop + length c) (butlast_if_match rpop (parser_bottom G))"
      and s="[]"
      in ssubst)
    apply(rename_tac h x ysa lpop rpop lpush rpush c)(*strict*)
    apply (metis butlast_if_match_direct2_prime length_append prefix_def prefix_drop_none)
   apply(rename_tac h x ysa lpop rpop lpush rpush c)(*strict*)
   apply(clarsimp)
  apply(rename_tac f h x ca ys ysa lpop rpop lpush rpush)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac f h x ys lpop lpush rpush c)(*strict*)
  apply(rule_tac
      xs="c"
      in rev_cases)
   apply(rename_tac f h x ys lpop lpush rpush c)(*strict*)
   apply(clarsimp)
   apply(rename_tac f h x ys lpop lpush rpush)(*strict*)
   apply(rule_tac
      t="drop (length f) (butlast_if_match f (parser_bottom G))"
      and s="[]"
      in ssubst)
    apply(rename_tac f h x ys lpop lpush rpush)(*strict*)
    apply (metis butlast_if_match_direct2_prime drop_eq_Nil order_refl)
   apply(rename_tac f h x ys lpop lpush rpush)(*strict*)
   apply(force)
  apply(rename_tac f h x ys lpop lpush rpush c ysa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h x ys lpop lpush rpush ysa y)(*strict*)
  apply(case_tac "y=parser_bottom G")
   apply(rename_tac f h x ys lpop lpush rpush ysa y)(*strict*)
   apply(clarsimp)
  apply(rename_tac f h x ys lpop lpush rpush ysa y)(*strict*)
  apply(rule_tac
      t="butlast_if_match (f @ ysa @ [y]) (parser_bottom G)"
      and s="f@ysa@[y]"
      in ssubst)
   apply(rename_tac f h x ys lpop lpush rpush ysa y)(*strict*)
   apply (metis append_assoc butlast_if_match_direct2)
  apply(rename_tac f h x ys lpop lpush rpush ysa y)(*strict*)
  apply(force)
  done

lemma parserHF_parserHFS_preserve_determ_hlp2: "
  valid_parser G \<Longrightarrow>
       parserHFS_step_relation G ci e1 c1 \<Longrightarrow>
       parserHFS_step_relation G ci e2 c2 \<Longrightarrow>
       ATS.derivation_initial parserHFS_initial_configurations
        parserHFS_step_relation G d \<Longrightarrow>
       d i = Some (pair e ci) \<Longrightarrow>
       set w1 \<subseteq> parser_events G - {parser_bottom G} \<Longrightarrow>
       set w2 \<subseteq> parser_events G - {parser_bottom G} \<Longrightarrow>
       parserHFS_conf_history c1 = parserHFS_conf_history ci @ w1 \<Longrightarrow>
       parserHFS_conf_history c2 = parserHFS_conf_history ci @ w2 \<Longrightarrow>
       ci \<in> parserHFS_configurations G \<Longrightarrow>
       c1 \<in> parserHFS_configurations G \<Longrightarrow>
       c2 \<in> parserHFS_configurations G \<Longrightarrow>
       valid_parser_step_label G e1 \<Longrightarrow>
       valid_parser_step_label G e2 \<Longrightarrow>
       w1 \<sqsubseteq>
       drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci) \<Longrightarrow>
       w2 \<sqsubseteq>
       drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci) \<Longrightarrow>
       w1 \<noteq> w2 \<Longrightarrow>
       w1 \<sqsubseteq> w2 \<Longrightarrow> parserHFS_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<Longrightarrow> False"
  apply(subgoal_tac "w2\<noteq>[]")
   prefer 2
   apply(simp add: prefix_def)
   apply(force)
  apply(case_tac "parserHFS_conf_fixed ci \<sqsupseteq> [parser_bottom G]")
   apply(thin_tac "parserHFS_step_relation G ci e1 c1")
   apply(thin_tac "c1 \<in> parserHFS_configurations G")
   apply(thin_tac "c2 \<in> parserHFS_configurations G")
   apply(thin_tac "parserHFS_conf_history c1 = parserHFS_conf_history ci @ w1")
   apply(thin_tac "w1 \<sqsubseteq> drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci)")
   apply(thin_tac "w1 \<noteq> w2")
   apply(thin_tac "w1 \<sqsubseteq> w2")
   apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac c ca cb x xa cc "cd" y w)(*strict*)
   apply(rule_tac
      xs="cc"
      in rev_cases)
    apply(rename_tac c ca cb x xa cc "cd" y w)(*strict*)
    apply(clarsimp)
   apply(rename_tac c ca cb x xa cc "cd" y w ys ya)(*strict*)
   apply(clarsimp)
  apply(subgoal_tac "rule_rpop e1 = parserHFS_conf_scheduler ci")
   prefer 2
   apply(thin_tac "parserHFS_step_relation G ci e2 c2")
   apply(simp add: parserHFS_step_relation_def prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac c ca cb cc x xa y)(*strict*)
   apply(rule_tac
      xs="xa"
      in rev_cases)
    apply(rename_tac c ca cb cc x xa y)(*strict*)
    apply(clarsimp)
   apply(rename_tac c ca cb cc x xa y ys ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ca cb cc x ys)(*strict*)
   apply(thin_tac "c2 \<in> parserHFS_configurations G")
   apply(simp add: parserHFS_configurations_def prefix_def)
   apply(clarsimp)
   apply(rename_tac c ca cb cc x ys f h "cd" ce)(*strict*)
   apply(rule_tac
      xs="f"
      in rev_cases)
    apply(rename_tac c ca cb cc x ys f h "cd" ce)(*strict*)
    apply(clarsimp)
   apply(rename_tac c ca cb cc x ys f h "cd" ce ysa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ca cb cc x ys h "cd" ce ysa y)(*strict*)
   apply(rule_tac
      xs="cd"
      in rev_cases)
    apply(rename_tac c ca cb cc x ys h "cd" ce ysa y)(*strict*)
    apply(clarsimp)
   apply(rename_tac c ca cb cc x ys h "cd" ce ysa y ysb ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ca cb cc x ys h ce ysa y ysb)(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac c ca cb cc x ys ce ysa y ysb "cd" cf)(*strict*)
   apply(rule_tac
      xs="ce"
      in rev_cases)
    apply(rename_tac c ca cb cc x ys ce ysa y ysb "cd" cf)(*strict*)
    apply(clarsimp)
    apply(rename_tac c ca cb x ys ysa y ysb "cd" cf)(*strict*)
    apply (metis List.drop_append append_assoc append_take_drop_id butlast_if_match_direct2 in_set_conv_decomp)
   apply(rename_tac c ca cb cc x ys ce ysa y ysb "cd" cf ysc ya)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc)(*strict*)
   apply(subgoal_tac "butlast_if_match (cc @ [parser_bottom G]) (parser_bottom G) = cc")
    apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct)
   apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc)(*strict*)
   apply(subgoal_tac "butlast_if_match (ysa @ [y]) (parser_bottom G) = ysa@[y]")
    apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct2)
   apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc)(*strict*)
   apply(clarsimp)
   apply(case_tac e1)
   apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
   apply(rename_tac lp rp lpu rpu)
   apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc lp rp lpu rpu)(*strict*)
   apply(case_tac "length rp - length ysa")
    apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc lp rp lpu rpu)(*strict*)
    apply(clarsimp)
   apply(rename_tac c ca cb cc x ys ysa y ysb "cd" cf ysc lp rp lpu rpu nat)(*strict*)
   apply(clarsimp)
  apply(subgoal_tac "prefix (parserHFS_conf_fixed ci) (parserHFS_conf_scheduler ci)")
   prefer 2
   apply(simp add: parserHFS_configurations_def)
   apply(force)
  apply(subgoal_tac "prefix (parserHFS_conf_fixed c1) (parserHFS_conf_scheduler c1)")
   prefer 2
   apply(simp add: parserHFS_configurations_def)
   apply(force)
  apply(subgoal_tac "prefix (parserHFS_conf_fixed c2) (parserHFS_conf_scheduler c2)")
   prefer 2
   apply(simp add: parserHFS_configurations_def)
   apply(force)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac c ca cb cc "cd" ce cf)(*strict*)
  apply(rule_tac
      xs="ce"
      in rev_cases)
   apply(rename_tac c ca cb cc "cd" ce cf)(*strict*)
   prefer 2
   apply(rename_tac c ca cb cc "cd" ce cf ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac c ca cb cc "cd" cf ys y)(*strict*)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
  apply(rename_tac c ca cb cc "cd" ce cf)(*strict*)
  apply(clarsimp)
  apply(rename_tac c ca cb cc "cd" cf)(*strict*)
  apply(subgoal_tac "rule_rpop e1 = parserHFS_conf_fixed ci@w1@[parser_bottom G]")
   apply(rename_tac c ca cb cc "cd" cf)(*strict*)
   prefer 2
   apply(thin_tac "parserHFS_step_relation G ci e2 c2")
   apply(simp add: parserHFS_step_relation_def prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac c ca cb cc "cd" cf x y)(*strict*)
   apply(thin_tac "c2 \<in> parserHFS_configurations G")
   apply(simp add: parserHFS_configurations_def prefix_def)
   apply(clarsimp)
   apply(rename_tac c ca cb "cd" cf x f h ce w wa)(*strict*)
   apply(subgoal_tac "butlast_if_match (w @ [parser_bottom G]) (parser_bottom G) = w")
    apply(rename_tac c ca cb "cd" cf x f h ce w wa)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct)
   apply(rename_tac c ca cb "cd" cf x f h ce w wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac ca cb "cd" cf x f h ce w wa)(*strict*)
   apply(rule_tac
      xs="ce"
      in rev_cases)
    apply(rename_tac ca cb "cd" cf x f h ce w wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac ca cb "cd" cf x f h ce w wa ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac c ca cb cc "cd" cf)(*strict*)
  apply(subgoal_tac "prefix (rule_rpop e2) (parserHFS_conf_scheduler ci)")
   apply(rename_tac c ca cb cc "cd" cf)(*strict*)
   prefer 2
   apply(simp add: parserHFS_step_relation_def prefix_def)
   apply(clarsimp)
  apply(rename_tac c ca cb cc "cd" cf)(*strict*)
  apply (metis ConsApp append_Cons drop_prefix_closureise length_1_context_both_empty_right list.distinct(1) list.exhaust nset_diff set_subset_in subset_refl)
  done

theorem parserHF_parserHFS_preserve_determ: "
  valid_parser G
  \<Longrightarrow> parserHF.is_forward_edge_deterministicHist_SB G
  \<Longrightarrow> parserHFS.is_forward_edge_deterministic_accessible G"
  apply(simp add: parserHF.is_forward_edge_deterministicHist_SB_def parserHFS.is_forward_edge_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(simp add: parserHFS.get_accessible_configurations_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
  apply(case_tac "d i")
   apply(rename_tac c c1 c2 e1 e2 d i)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac c c1 c2 e1 e2 d i a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac c c1 c2 e1 e2 d i a option conf)(*strict*)
  apply(rename_tac e ci)
  apply(rename_tac c c1 c2 e1 e2 d i a e ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
  apply(erule_tac
      x="parserHFvHFS_Lin2BraConf c"
      in ballE)
   apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
   prefer 2
   apply(simp add: parserHF.get_accessible_configurations_def)
   apply(erule_tac
      x="parserHF_vs_parserHFS.Lin2BraDer d"
      in allE)
   apply(erule impE)
    apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
    apply (metis parserHF_vs_parserHFS.Lin2BraConf_preserves_initiality_lift)
   apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
   apply(simp add: get_configuration_def parserHF_vs_parserHFS.Lin2BraDer_def derivation_map_def)
   apply(erule_tac
      x="i"
      in allE)
   apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "c=ci")
   apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
   prefer 2
   apply(simp add: get_configuration_def)
  apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
  apply(erule_tac
      x="parserHFvHFS_Lin2BraConf c1"
      in allE)
  apply(erule_tac
      x="parserHFvHFS_Lin2BraConf c2"
      in allE)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule impE)
   apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
   apply (metis parserHFS.derivation_initial_configurations parserHFvHFS_inst_AX_Lin2BraConf_preserves_steps)
  apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule impE)
   apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
   apply (metis parserHFS.derivation_initial_configurations parserHFvHFS_inst_AX_Lin2BraConf_preserves_steps)
  apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
  apply(erule impE)
   apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac c c1 c2 e1 e2 d i e ci)(*strict*)
  apply(clarify)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 d i e)(*strict*)
  apply(rename_tac ci c1 c2 e1 e2 d i e)
  apply(rename_tac ci c1 c2 e1 e2 d i e)(*strict*)
  apply(subgoal_tac " \<exists>w1. set w1 \<subseteq> parser_events G - {parser_bottom G} \<and> (\<exists>w2. set w2 \<subseteq> parser_events G - {parser_bottom G} \<and> parserHF_conf_history (parserHFvHFS_Lin2BraConf c1) = parserHF_conf_history (parserHFvHFS_Lin2BraConf ci) @ w1 \<and> parserHF_conf_history (parserHFvHFS_Lin2BraConf c2) = parserHF_conf_history (parserHFvHFS_Lin2BraConf ci) @ w2)")
   apply(rename_tac ci c1 c2 e1 e2 d i e)(*strict*)
   prefer 2
   apply(simp add: parserHFvHFS_Lin2BraConf_def parserHFS_step_relation_def Let_def parser_markers_def)
   apply(clarsimp)
   apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya)(*strict*)
   apply(rule conjI)
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya)(*strict*)
    apply(rule set_drop_subset2)
    apply(subgoal_tac "valid_parser_step_label G e1")
     apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya)(*strict*)
     prefer 2
     apply(simp add: valid_parser_def)
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya)(*strict*)
    apply(simp add: valid_parser_step_label_def kPrefix_def)
    apply(clarsimp)
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
    apply(simp add: valid_parser_step_label_def kPrefix_def)
    apply(case_tac "k - length w")
     apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
      apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
      prefer 2
      apply (metis append_take_drop_id butlast_if_match_reduces in_set_conv_decomp nset_diff set_app_subset subsetD)
     apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
      apply (metis Diff_iff in_set_takeD subsetD)
     apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
     apply (metis in_set_takeD nset_diff)
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf nat xe)(*strict*)
    apply(subgoal_tac "butlast_if_match (w @ [parser_bottom G]) (parser_bottom G) = w")
     apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf nat xe)(*strict*)
     prefer 2
     apply (metis butlast_if_match_direct)
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf nat xe)(*strict*)
    apply(clarsimp)
    apply (metis DiffE subsetD triv_compl)
   apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya)(*strict*)
   apply(rule set_drop_subset2)
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya)(*strict*)
    prefer 2
    apply(simp add: valid_parser_def)
   apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya)(*strict*)
   apply(simp add: valid_parser_step_label_def kPrefix_def)
   apply(clarsimp)
   apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
   apply(simp add: valid_parser_step_label_def kPrefix_def)
   apply(case_tac "k - length w")
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
     apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
     prefer 2
     apply (metis append_take_drop_id butlast_if_match_reduces in_set_conv_decomp nset_diff set_app_subset subsetD)
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
     apply (metis Diff_iff in_set_takeD subsetD)
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf)(*strict*)
    apply (metis in_set_takeD nset_diff)
   apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf nat xe)(*strict*)
   apply(subgoal_tac "butlast_if_match (w @ [parser_bottom G]) (parser_bottom G) = w")
    apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf nat xe)(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct)
   apply(rename_tac ci c1 c2 e1 e2 d i e x xa xb xc y ya xd k w xf nat xe)(*strict*)
   apply(clarsimp)
   apply (metis DiffE subsetD triv_compl)
  apply(rename_tac ci c1 c2 e1 e2 d i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(simp add: parserHFvHFS_Lin2BraConf_def)
  apply(subgoal_tac "ci \<in> parserHFS_configurations G")
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   prefer 2
   apply(rule parserHFS.belongs_configurations)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(rule parserHFS.derivation_initial_belongs)
     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(subgoal_tac "c1 \<in> parserHFS_configurations G")
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   prefer 2
   apply(rule parserHFS.AX_step_relation_preserves_belongsC)
     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(subgoal_tac "c2 \<in> parserHFS_configurations G")
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   prefer 2
   apply(rule parserHFS.AX_step_relation_preserves_belongsC)
     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
   apply(simp add: parserHFS_step_relation_def)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
   apply(simp add: parserHFS_step_relation_def)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(subgoal_tac "(prefix w1 w2 \<or> prefix w2 w1) \<and> (prefix w1 (drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci))) \<and> (prefix w2 (drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci)))")
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   prefer 2
   apply(subgoal_tac "(prefix w1 (drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci)))")
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    prefer 2
    apply(rule parserHF_parserHFS_preserve_determ_hlp1)
        apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
      apply(force)
     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(subgoal_tac "(prefix w2 (drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci)))")
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    prefer 2
    apply(rule_tac
      ?c1.0="c2"
      in parserHF_parserHFS_preserve_determ_hlp1)
        apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
      apply(force)
     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(rule conjI)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(rule_tac
      c="drop (length (parserHFS_conf_fixed ci)) (parserHFS_conf_scheduler ci)"
      in prefix_common)
     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(unfold parserHF.compatible_history_fragment_SB_def)
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule_tac
      x="w2"
      in exI)
  apply(rule conjI)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(simp add: parser_markers_def)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(simp add: parser_markers_def)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(clarsimp)
  apply(simp add: Let_def)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes parser_markers (@) G w1"
      and s="prefix_closure {w1}"
      in ssubst)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(rule antisym)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(simp add: parser_markers_def prefix_closure_def prefix_def)
    apply(clarsimp)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2 x)(*strict*)
   apply(simp add: parser_markers_def prefix_closure_def prefix_def)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes parser_markers (@) G w2"
      and s="prefix_closure {w2}"
      in ssubst)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(rule antisym)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(simp add: parser_markers_def prefix_closure_def prefix_def)
    apply(clarsimp)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2 x)(*strict*)
   apply(simp add: parser_markers_def prefix_closure_def prefix_def)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes parser_markers (@) G X"
      and s="prefix_closure {X}" for X
      in ssubst)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(rule antisym)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(simp add: parser_markers_def prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2 x c ca hf'')(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(simp add: parser_markers_def prefix_closure_def prefix_def)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(rule_tac
      t="prefix_closure {SSX} \<subseteq> prefix_closure {SSY}"
      and s="prefix SSX SSY" for SSX SSY
      in ssubst)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(rule prefix_closure_subset_to_prefix)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(rule_tac
      t="prefix_closure {SSX} \<subseteq> prefix_closure {SSY}"
      and s="prefix SSX SSY" for SSX SSY
      in ssubst)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(rule prefix_closure_subset_to_prefix)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(rule_tac
      t="prefix_closure {SSX} = prefix_closure {SSY}"
      and s="SSX=SSY" for SSX SSY
      in ssubst)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply (metis prefix_closure_single_eq)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(case_tac "w1=w2")
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(erule disjE)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(rule disjI1)
   apply(clarsimp)
   apply(rule_tac
      ?c1.0="c1"
      and ?c2.0="c2"
      and ?w1.0="w1"
      and ?w2.0="w2"
      in parserHF_parserHFS_preserve_determ_hlp2)
                     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                     apply(force)
                    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                    apply(force)
                   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                   apply(force)
                  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                  apply(force)
                 apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                 apply(force)
                apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                apply(force)
               apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
               apply(force)
              apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
              apply(force)
             apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
             apply(force)
            apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
            apply(force)
           apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
           apply(force)
          apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
          apply(force)
         apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
         apply(force)
        apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
      apply(force)
     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(rule disjI2)
  apply(clarsimp)
  apply(rule_tac
      ?c1.0="c2"
      and ?c2.0="c1"
      and ?w1.0="w2"
      and ?w2.0="w1"
      in parserHF_parserHFS_preserve_determ_hlp2)
                    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                    apply(force)
                   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                   apply(force)
                  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                  apply(force)
                 apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                 apply(force)
                apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
                apply(force)
               apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
               apply(force)
              apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
              apply(force)
             apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
             apply(force)
            apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
            apply(force)
           apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
           apply(force)
          apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
          apply(force)
         apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
         apply(force)
        apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
        apply(force)
       apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
       apply(force)
      apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
      apply(force)
     apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac ci c1 c2 e1 e2 d i e w1 w2)(*strict*)
  apply(force)
  done

lemma parserHFS_step_relation_slim_step_intro: "
  valid_parser G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> e \<in> parser_step_labels G
  \<Longrightarrow> suffix (parserHFS_conf_stack c1) (rule_lpop e)
  \<Longrightarrow> \<exists>w. ((rule_rpop e @ w @[parser_bottom G] = parserHFS_conf_scheduler c1) \<or> (rule_rpop e =  parserHFS_conf_scheduler c1))
  \<Longrightarrow> \<exists>c2. parserHFS_step_relation G c1 e c2"
  apply(erule exE)+
  apply(rename_tac w)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac w c)(*strict*)
  apply(simp add: parser_step_labels_def)
  apply(erule disjE)
   apply(rename_tac w c)(*strict*)
   apply(rule_tac x="\<lparr>parserHFS_conf_fixed = rule_rpush e @
           drop (length (rule_rpop e)) (parserHFS_conf_fixed c1),
    parserHFS_conf_history = parserHFS_conf_history c1 @
           drop (length (parserHFS_conf_fixed c1))
            (butlast_if_match (rule_rpop e) (parser_bottom G)),
    parserHFS_conf_stack = c @ rule_lpush e,
    parserHFS_conf_scheduler = SSr\<rparr> " for SSr in exI)
   apply(clarsimp)
   apply(rule_tac x="w @ [parser_bottom G]" in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac w c)(*strict*)
    apply(force)
   apply(rename_tac w c)(*strict*)
   apply(simp add: parserHFS_configurations_def)
  apply(rename_tac w c)(*strict*)
  apply(rule_tac x="\<lparr>parserHFS_conf_fixed = rule_rpush e @
           drop (length (rule_rpop e)) (parserHFS_conf_fixed c1),
    parserHFS_conf_history = parserHFS_conf_history c1 @
           drop (length (parserHFS_conf_fixed c1))
            (butlast_if_match (rule_rpop e) (parser_bottom G)),
    parserHFS_conf_stack = c @ rule_lpush e,
    parserHFS_conf_scheduler = SSr\<rparr> " for SSr in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac w c)(*strict*)
   apply(force)
  apply(rename_tac w c)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(rename_tac c)(*strict*)
  apply(clarsimp)
  apply(rename_tac c f h w)(*strict*)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac x="e" in ballE)
   apply(rename_tac c f h w)(*strict*)
   prefer 2
   apply(simp add: parser_step_labels_def)
  apply(rename_tac c f h w)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac c f w ca cb k wa xa xb)(*strict*)
  apply(rule_tac xs="w" in rev_cases)
   apply(rename_tac c f w ca cb k wa xa xb)(*strict*)
   apply(clarsimp)
   apply(rename_tac c f ca cb k wa xa xb)(*strict*)
   apply(rule_tac xs="rule_rpush e" in rev_cases)
    apply(rename_tac c f ca cb k wa xa xb)(*strict*)
    apply(clarsimp)
   apply(rename_tac c f ca cb k wa xa xb ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac c f w ca cb k wa xa xb ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac c f ca cb k wa xa xb ys y)(*strict*)
  apply(rule_tac x="xb" in exI)
  apply(force)
  done

lemmas parserHFS_interpretations1 =
  parserHFS_inst_BF_LinDBRest_DetR_LaOp_axioms
  parserHFS_inst_BF_LinDBRest_DetHDB_LaOp_axioms
  parserHFS_inst_BF_LinDBRest_DetHSB_LaOp_axioms
  parserHFS_inst_BF_LinSBRest_DetR_LaOp_axioms
  parserHFS_inst_BF_LinSBRest_DetHDB_LaOp_axioms
  parserHFS_inst_BF_LinSBRest_DetHSB_LaOp_axioms
  parserHFS_inst_BF_LinSB_OpLa_axioms
  parserHFS_inst_BF_LinDB_OpLa_axioms

end

