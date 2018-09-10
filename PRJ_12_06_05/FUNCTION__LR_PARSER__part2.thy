section {*FUNCTION\_\_LR\_PARSER\_\_part2*}
theory
  FUNCTION__LR_PARSER__part2

imports
  FUNCTION__LR_PARSER__part1

begin

theorem Lemma6__29: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> viable_prefix G' (teB Do # YSEQ)
  \<Longrightarrow> parserS.derivation P dP
  \<Longrightarrow> maximum_of_domain dP dPn
  \<Longrightarrow> \<pi>' = get_labels dP dPn
  \<Longrightarrow> parserS.belongs P dP
  \<Longrightarrow> dP 0 = Some (pair None
                \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ),
                parserS_conf_scheduler = w\<rparr>)
  \<Longrightarrow> dP dPn = Some (pair e \<Phi>)
  \<Longrightarrow> \<exists>XSEQ y x.
        \<Phi> = \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ), parserS_conf_scheduler = y\<rparr>
        \<and> w = x @ y
        \<and> viable_prefix G' (teB Do # XSEQ)
        \<and> length \<pi>' = length (tau (parser_marker P) \<pi>') + length x
        \<and> (\<exists>dG e dGn.
            cfgRM.derivation G dG
            \<and> maximum_of_domain dG dGn
            \<and> dG 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>)
            \<and> dG dGn = Some (pair e \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>)
            \<and> get_labels dG dGn = rev (tau (parser_marker P) \<pi>'))"
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
    apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def AF_LR_PARSER_input_def)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "(F_DFA_GOTO M (epda_initial M) (teB Do)) \<in> epda_states M")
   prefer 2
   apply(rule_tac
      ?q0.0="epda_initial M"
      and X="teB Do"
      in DFA_F_DFA_GOTO_in_states)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def AF_LR_PARSER_input_def)
   apply(force)
  apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<in> epda_states M")
   prefer 2
   apply(rule_tac
      ?q0.0="epda_initial M"
      and w="[teB Do, teA (cfg_initial G), teB Do]"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(subgoal_tac "teA (cfg_initial G) \<in> teA ` cfg_nonterminals G")
      apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def AF_LR_PARSER_input_def)
      apply(force)
     apply(simp add: valid_cfg_def AF_LR_PARSER_input_def)
    apply(force)
   apply(force)
  apply(subgoal_tac "valid_parser P")
   prefer 2
   apply(rule_tac
      G="G"
      in AF_LR_PARSER_valid_parser)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "\<forall>dPn dP YSEQ \<pi>' \<Phi> e w. viable_prefix G' (teB Do#YSEQ) \<and> parserS.derivation P dP \<and> parserS.belongs P dP \<and> maximum_of_domain dP dPn \<and> \<pi>' = get_labels dP dPn \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#YSEQ),parserS_conf_scheduler=w\<rparr>) \<and> dP dPn = Some (pair e \<Phi>) \<longrightarrow> (\<exists>XSEQ y x dGn. \<Phi> = \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#XSEQ),parserS_conf_scheduler=y\<rparr> \<and> w=x@y \<and> viable_prefix G' (teB Do#XSEQ) \<and> (length \<pi>') = length (tau (parser_marker P) \<pi>') + length x \<and> (\<exists>dG e. cfgRM.derivation G dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf=XSEQ\<rparr>) \<and> dG dGn = Some (pair e \<lparr>cfg_conf=YSEQ@(liftB x)\<rparr>) \<and> get_labels dG dGn = (List.rev (tau (parser_marker P) \<pi>'))))")
   apply(erule_tac
      x="dPn"
      in allE)
   apply(erule_tac
      x="dP"
      in allE)
   apply(erule_tac
      x="YSEQ"
      in allE)
   apply(erule_tac
      x="\<pi>'"
      in allE)
   apply(erule_tac
      x="\<Phi>"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule_tac
      x="w"
      in allE)
   apply(force)
  apply(thin_tac "viable_prefix G' (teB Do#YSEQ)")
  apply(thin_tac "parserS.derivation P dP")
  apply(thin_tac "parserS.belongs P dP")
  apply(thin_tac "maximum_of_domain dP dPn")
  apply(thin_tac "\<pi>' = get_labels dP dPn")
  apply(thin_tac "dP 0 = Some (pair None \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#YSEQ),parserS_conf_scheduler=w\<rparr>)")
  apply(thin_tac "dP dPn = Some (pair e \<Phi>)")
  apply(rule allI)
  apply(rename_tac dPn)(*strict*)
  apply(induct_tac dPn)
   apply(rename_tac dPn)(*strict*)
   apply(rule allI)+
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule impI)
   apply(erule conjE)+
   apply(rule_tac
      x="YSEQ"
      in exI)
   apply(rule_tac
      x="w"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="0"
      in exI)
   apply(subgoal_tac "get_labels dP 0=[]")
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    prefer 2
    apply(rule get_labelsEmpty)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(subgoal_tac "get_labels (der1 \<lparr>cfg_conf = YSEQ\<rparr>) 0=[]")
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    prefer 2
    apply(rule get_labelsEmpty)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(rule_tac
      i="0"
      and d="dP"
      in parserS.sameget_configurationigSame)
     apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
     apply(blast)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(blast)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(force)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(blast)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(force)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule_tac
      x = "der1 \<lparr>cfg_conf = YSEQ\<rparr>"
      in exI)
   apply(rule_tac
      x="None"
      in exI)
   apply(rule conjI)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(rule cfgRM.der1_is_derivation)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(simp add: der1_def)
   apply(rename_tac dPn dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(force)
  apply(rename_tac dPn n)(*strict*)
  apply(rule allI)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w)(*strict*)
  apply(rule impI)
  apply(erule conjE)+
  apply(subgoal_tac "\<exists>r' \<pi>''. \<pi>'=r'#\<pi>''")
   apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   prefer 2
   apply(subgoal_tac "length \<pi>' = Suc n")
    apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    prefer 2
    apply(rule get_labelsLength)
     apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w)(*strict*)
     apply(arith)
    apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(blast)
   apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w)(*strict*)
   apply(case_tac "\<pi>'")
    apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w)(*strict*)
    apply(force)
   apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w a list)(*strict*)
   apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w)(*strict*)
  apply(erule exE)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
  apply(subgoal_tac "\<exists>r'_v. r'=Some r'_v")
   apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
   prefer 2
   apply(case_tac "r'")
    apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
    apply(rule_tac
      i="0"
      in parserS.get_labels_nth_notNone)
        apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
        apply(blast)
       apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
       apply(blast)
      apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
      apply(arith)
     apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
     apply(blast)
    apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
    apply(force)
   apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' a)(*strict*)
   apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'')(*strict*)
  apply(erule exE)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
  apply(subgoal_tac "set (teB Do # YSEQ) \<subseteq> epda_events M")
   apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
   prefer 2
   apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
    apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
    apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
   apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
   apply(rule viable_prefix_in_CFG)
    apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
    apply(force)
   apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
   apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
  apply(case_tac "(parser_marker P) r'_v")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
  prefer 2
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(case_tac a)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  prefer 2
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(subgoal_tac "\<exists>A XSEQ. (parser_marker P) r'_v = Some(Some \<lparr>prod_lhs=A,prod_rhs=XSEQ\<rparr>) \<and> (\<exists>q\<delta> y. r'_v=\<lparr>rule_lpop = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ, rule_rpop = y, rule_lpush = q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> [teA A], rule_rpush = y\<rparr>)")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and k="k"
      in AF_LR_PARSER_reduce_rules2_direction2)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(rule AF_LR_PARSER_NonNone_effect_only_for_rules)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa)(*strict*)
  apply(erule exE)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(subgoal_tac "\<exists>q q_seq I y qA. (r'_v,parser_marker P r'_v)=(\<lparr>rule_lpop=q#q_seq, rule_rpop=y,rule_lpush=[q,qA], rule_rpush=y\<rparr>,Some(Some \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=(cfg_item_rhs1 I)@(cfg_item_rhs2 I)\<rparr>)) \<and> q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> (cfg_item_rhs1 I=[]) \<and> qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I))) \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) \<and> \<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs2 I,cfg_item_rhs2=[],cfg_item_look_ahead=y\<rparr> \<in> last (q#q_seq)")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  prefer 2
  apply(subgoal_tac "r'_v \<in> parser_rules P")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  prefer 2
  apply(rule AF_LR_PARSER_NonNone_effect_only_for_rules)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(rule AF_LR_PARSER__rules_reduce_elem)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y)(*strict*)
  apply(erule exE)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "set XSEQ \<subseteq> epda_events M")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      in cfg_prod_in_two_elements_construct_domain_subset_trans)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(subgoal_tac "teA (cfg_item_lhs I) \<in> epda_events M")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      in cfg_prod_in_two_elements_construct_domain_subset_trans2)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(simp add: F_LR_MACHINE_def AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(subgoal_tac "qA=F_DFA_GOTO M q\<delta> (teA A)")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  prefer 2
  apply(subgoal_tac "[qA]=[F_DFA_GOTO M q\<delta> (teA A)]")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(rule_tac
      t="[F_DFA_GOTO M q\<delta> (teA A)]"
      and s="F_DFA_GOTO_SEQUENCE M q\<delta> [teA A]"
      in subst)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(subgoal_tac "\<exists>YSEQ'. YSEQ'@XSEQ=YSEQ \<and> dP (Suc 0) = Some (pair r' \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ'@[teA A]), parserS_conf_scheduler = w\<rparr>)")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  prefer 2
  apply(thin_tac "\<forall>dP YSEQ \<pi>' \<Phi> e w. viable_prefix G' (teB Do # YSEQ) \<and> parserS.derivation P dP \<and> parserS.belongs P dP \<and> maximum_of_domain dP n \<and> \<pi>' = get_labels dP n \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ), parserS_conf_scheduler = w\<rparr>) \<and> dP n = Some (pair e \<Phi>) \<longrightarrow> (\<exists>XSEQ y x dGn. \<Phi> = \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ), parserS_conf_scheduler = y\<rparr> \<and> w = x @ y \<and> viable_prefix G' (teB Do # XSEQ) \<and> length \<pi>' = length (tau (parser_marker P) \<pi>') + length x \<and> (\<exists>dG e. cfgRM.derivation G dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>) \<and> dG dGn = Some (pair e \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>) \<and> get_labels dG dGn = (List.rev (tau (parser_marker P) \<pi>'))))")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(subgoal_tac "\<exists>e c. dP (Suc 0) = Some (pair (Some e) c)")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  prefer 2
  apply(rule parserS.some_position_has_details_before_max_dom_after_0)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(blast)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(blast)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(arith)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(erule exE)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(subgoal_tac "ea=r'_v")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  prefer 2
  apply(subgoal_tac "Some ea = \<pi>'!0")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  prefer 2
  apply(rule_tac
      n="n"
      in parserS.identify_getLabel_with_derivation_get_label)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(subgoal_tac "parserS_step_relation P \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ), parserS_conf_scheduler = w\<rparr> r'_v c")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  prefer 2
  apply(rule_tac
      n="0"
      in parserS.position_change_due_to_step_relation)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(blast)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(blast)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(blast)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c)(*strict*)
  apply(simp (no_asm_use) only: parserS_step_relation_def)
  apply(erule_tac conjE)+
  apply(erule exE)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(erule_tac conjE)+
  apply(subgoal_tac "parserS_conf_scheduler c = w")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ) = x @ q\<delta> # F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(subgoal_tac "\<exists>w y. w@y#XSEQ=(teB Do # YSEQ) \<and> x=F_DFA_GOTO_SEQUENCE M (epda_initial M) w \<and> q\<delta>=F_DFA_GOTO M (last ((epda_initial M)#x)) y")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      in partial_F_DFA_GOTO_SEQUENCE_eq_implies_existence_of_sub_F_DFA_GOTO_SEQUENCEs)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa)(*strict*)
  apply(erule exE)+
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa wa yb)(*strict*)
  apply(erule conjE)+
  apply(case_tac I)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA ea c x xa wa yb cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_ahead)(*strict*)
  apply(rename_tac A w1 w2 y)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa Aa XSEQ q\<delta> ya q q_seq I yaa qA ea c x xa wa yb A w1 w2 y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa c xa wa yb A w2 y)(*strict*)
  apply(case_tac c)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa c xa wa yb A w2 y parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(rename_tac c1 c2)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa c xa wa yb A w2 y c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(case_tac wa)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) [] = []")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(rule sym)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA A]"
      and s="F_DFA_GOTO M (epda_initial M) (teB Do) # (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (epda_initial M) (teB Do)) [teA A])"
      in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_take_head)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa A y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(subgoal_tac "length []=length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  prefer 2
  apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(case_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) wa = []")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(subgoal_tac "length wa=length (F_DFA_GOTO_SEQUENCE M (epda_initial M) wa)")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  prefer 2
  apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(thin_tac "dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) wa @ F_DFA_GOTO M (if F_DFA_GOTO_SEQUENCE M (epda_initial M) wa = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) wa)) yb # F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (if F_DFA_GOTO_SEQUENCE M (epda_initial M) wa = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) wa)) yb) w2, parserS_conf_scheduler = yaa @ xa\<rparr>)")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(thin_tac "\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = w2, cfg_item_rhs2 = [], cfg_item_look_ahead = yaa\<rparr> \<in> (if F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (if F_DFA_GOTO_SEQUENCE M (epda_initial M) wa = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) wa)) yb) w2 = [] then F_DFA_GOTO M (if F_DFA_GOTO_SEQUENCE M (epda_initial M) wa = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) wa)) yb else last (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (if F_DFA_GOTO_SEQUENCE M (epda_initial M) wa = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) wa)) yb) w2))")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(thin_tac "ATS.derivation (\<lambda>a b c d. c \<in> parser_rules a \<and> (\<exists>x. parserS_conf_stack b = x @ rule_lpop c \<and> parserS_conf_stack d = x @ rule_lpush c) \<and> (\<exists>x. parserS_conf_scheduler b = rule_rpop c @ x \<and> parserS_conf_scheduler d = rule_rpush c @ x)) P dP")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' yaa xa wa yb A w2 y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule_tac
      t="[F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) yb, F_DFA_GOTO M (F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) yb) (teA A)]"
      and s="(F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb]) @ (F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) yb) [teA A])"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  prefer 4
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list) @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb] @ F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) yb) [teA A]"
      and s="(F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list) @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb]) @ F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) yb) [teA A]"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list) @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb]"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((teB Do # list) @ [yb])"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule sym)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))"
      and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  prefer 2
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) yb"
      and s="last(F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb])"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb]"
      and s="[F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) yb]"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  prefer 4
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="teB Do # list @ [yb, teA A]"
      and s="(teB Do # list @ [yb]) @ [teA A]"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((teB Do # list @ [yb]) @ [teA A])"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list @ [yb]) @ (F_DFA_GOTO_SEQUENCE M (last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list @ [yb])))) [teA A])"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list @ [yb]))"
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb])"
      and s="last (F_DFA_GOTO_SEQUENCE SSM SSp (SSw1@SSw2))" for SSM SSp SSw1 SSw2
      in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_concat)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (teB Do # list @ [yb])=length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list @ [yb]))")
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  prefer 2
  apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' yaa xa yb A w2 y list)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a aa A XSEQ q\<delta> y q q_seq I ya qA)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q I ya YSEQ')(*strict*)
  apply(case_tac I)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q I ya YSEQ' cfg_item_lhsa cfg_item_rhs1a cfg_item_rhs2a cfg_item_look_ahead)(*strict*)
  apply(rename_tac A w1 w2 y)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q I ya YSEQ' A w1 w2 y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q ya YSEQ' A w2 y)(*strict*)
  apply(erule_tac
      x="derivation_drop dP (Suc 0)"
      in allE)
  apply(erule_tac
      x="YSEQ' @ [teA A]"
      in allE)
  apply(erule_tac
      x="\<Phi>"
      in allE)
  apply(erule_tac
      x="if n=0 then None else e"
      in allE)
  apply(erule_tac
      x="w"
      in allE)
  apply(subgoal_tac "q=last(F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ'))")
  apply(rename_tac n dP \<Phi> e w \<pi>'' q ya YSEQ' A w2 y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(erule impE)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(subgoal_tac "\<forall>I \<in> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ')). (cfg_item_lhs I\<noteq>S' \<longrightarrow> (cfg_item_rhs1 I = [] \<longrightarrow> (\<exists>J. setA (cfg_item_rhs2 J) \<subseteq> cfg_nonterminals G' \<and> (\<exists>w. cfg_item_rhs2 J = teA (cfg_item_lhs I) # w) \<and> J \<in> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ')))))")
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      in rhs1_empty_items_due_to_specific_item)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(erule_tac
      x="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = [], cfg_item_rhs2 = w2, cfg_item_look_ahead = y\<rparr>"
      in ballE)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(clarsimp)
  apply(erule impE)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(case_tac "A=S'")
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(subgoal_tac "A \<in> cfg_nonterminals G")
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(subgoal_tac "S'\<notin>cfg_nonterminals G")
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule F_FRESH_is_fresh)
  apply(simp add: valid_cfg_def AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule prod_lhs_in_nonterms)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: valid_cfg_def AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa)(*strict*)
  apply(subgoal_tac "\<exists>J'. F_VALID_ITEM_SET_GOTO__passes (teA A) J J'")
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa)(*strict*)
  prefer 2
  apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(rule_tac
      x="\<lparr>cfg_item_lhs=cfg_item_lhs J,cfg_item_rhs1=cfg_item_rhs1 J @ [teA A],cfg_item_rhs2=wa,cfg_item_look_ahead=cfg_item_look_ahead J\<rparr>"
      in exI)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa)(*strict*)
  apply(erule exE)+
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(rule_tac
      I="J'"
      and k="k"
      in Fact6_12__1)
  apply(rule_tac
      t="(teB Do # YSEQ' @ [teA A])"
      and s="((teB Do # YSEQ') @ [teA A])"
      in ssubst)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(rule valid_item_set_F_VALID_ITEM_SET_GOTO__passes)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(rule_tac
      t="valid_item_set G' k (teB Do # YSEQ')"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ'))"
      in ssubst)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(rule_tac
      t="valid_item_set G' k (teB Do # YSEQ')"
      and s="(if (teB Do # YSEQ')=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ')))"
      in ssubst)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(rule F_LR_MACHINE_all_SOUND)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(force)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(rule_tac
      B="cfg_events G'"
      in two_elements_construct_domain_setA)
  apply(rule set_take_head2)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(rule_tac
      B="cfg_events G'"
      in two_elements_construct_domain_setB)
  apply(rule set_take_head2)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y J wa J')(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule_tac
      m = "n"
      in parserS.derivation_drop_preserves_derivation)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule conjI)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule parserS.derivation_drop_preserves_belongs)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule derivation_drop_preserves_generates_maximum_of_domain)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: derivation_drop_def)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(simp add: derivation_drop_def)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y)(*strict*)
  apply(erule exE)+
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y XSEQ yb)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y XSEQ yb x)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n dP \<Phi> e w \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    x="XSEQ"
    in exI)
  apply(rule_tac
    x="yb"
    in exI)
  apply(clarsimp)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(subgoal_tac "get_labels dP (Suc n)=Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ')) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ'))) w2, rule_rpop = ya, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ')), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ'))) (teA A)], rule_rpush = ya\<rparr> # get_labels (derivation_drop dP (Suc 0)) n")
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    t="get_labels dP (Suc n)"
    and s="Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ')) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ'))) w2, rule_rpop = ya, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ')), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ'))) (teA A)], rule_rpush = ya\<rparr> # get_labels (derivation_drop dP (Suc 0)) n"
    in ssubst)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    x="Suc dGn"
    in exI)
  apply(rule_tac
    x = "derivation_append dG (der2 \<lparr>cfg_conf = YSEQ' @ teA A # liftB x\<rparr> \<lparr>prod_lhs = A, prod_rhs = w2\<rparr> \<lparr>cfg_conf = YSEQ' @ w2 @ liftB x\<rparr>) dGn"
    in exI)
  apply(rule context_conjI)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule cfgRM.derivation_concat2)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule cfgRM.der2_is_derivation)
  apply(simp add: cfgRM_step_relation_def)
  apply(rule_tac
    x="YSEQ'"
    in exI)
  apply(rule_tac
    x="liftB x"
    in exI)
  apply(clarsimp)
  apply(rule setA_liftB_empty)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    s = "dGn+(Suc 0)"
    in ssubst)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(arith)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac concat_has_max_dom)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule der2_maximum_of_domain)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    t="(List.rev (tau (parser_marker P) (get_labels (derivation_drop dP (Suc 0)) n)))"
    and s="get_labels dG dGn"
    in ssubst)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    t="get_labels (derivation_append dG (der2 \<lparr>cfg_conf = YSEQ' @ teA A # liftB x\<rparr> \<lparr>prod_lhs = A, prod_rhs = w2\<rparr> \<lparr>cfg_conf = YSEQ' @ w2 @ liftB x\<rparr>) dGn) (Suc dGn)"
    and s="(get_labels dG dGn)@(get_labels (der2 \<lparr>cfg_conf = YSEQ' @ teA A # liftB x\<rparr> \<lparr>prod_lhs = A, prod_rhs = w2\<rparr> \<lparr>cfg_conf = YSEQ' @ w2 @ liftB x\<rparr>) (Suc 0))"
    in ssubst)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    t="Suc dGn"
    and s="dGn+(Suc 0)"
    in ssubst)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule derivation_concat_get_labels)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    t="get_labels (der2 \<lparr>cfg_conf = YSEQ' @ teA A # liftB x\<rparr> \<lparr>prod_lhs = A, prod_rhs = w2\<rparr> \<lparr>cfg_conf = YSEQ' @ w2 @ liftB x\<rparr>) (Suc 0)"
    and s="[Some \<lparr>prod_lhs = A, prod_rhs = w2\<rparr>]"
    in ssubst)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(rule_tac
    t="nat_seq (Suc 0) (Suc 0)"
    and s="[Suc 0]"
    in ssubst)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule natUptTo_n_n)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP e ya YSEQ' A w2 y XSEQ yb x dGn dG ea eb)(*strict*)
  apply(simp add: der2_def)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule_tac
    t="get_labels dP (Suc n)"
    and s="(get_labels dP (Suc 0))@(get_labels (derivation_drop dP (Suc 0)) (Suc n-(Suc 0)))"
    in ssubst)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule derivation_skip_get_labels)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(clarsimp)
  apply(simp add: get_labels_def)
  apply(simp add: get_label_def)
  apply(rule_tac
    t="nat_seq (Suc 0) (Suc 0)"
    and s="[Suc 0]"
    in ssubst)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(rule natUptTo_n_n)
  apply(rename_tac n dP e \<pi>'' ya YSEQ' A w2 y XSEQ yb x dGn dG ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q ya YSEQ' A w2 y)(*strict*)
  apply(subgoal_tac "parserS_step_relation P \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ' @ w2), parserS_conf_scheduler = w\<rparr> \<lparr>rule_lpop = q # F_DFA_GOTO_SEQUENCE M q w2, rule_rpop = ya, rule_lpush = [q, F_DFA_GOTO M q (teA A)], rule_rpush = ya\<rparr> \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ' @ [teA A]), parserS_conf_scheduler = w\<rparr>")
  apply(rename_tac n dP \<Phi> e w \<pi>'' q ya YSEQ' A w2 y)(*strict*)
  prefer 2
  apply(rule_tac parserS.position_change_due_to_step_relation)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q ya YSEQ' A w2 y)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e w \<pi>'' q ya YSEQ' A w2 y)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(subgoal_tac "\<exists>w y. w@y#w2=(teB Do # YSEQ' @ w2) \<and> x=F_DFA_GOTO_SEQUENCE M (epda_initial M) w \<and> q=F_DFA_GOTO M (last ((epda_initial M)#x)) y")
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  prefer 2
  apply(rule_tac
    G="G"
    in partial_F_DFA_GOTO_SEQUENCE_eq_implies_existence_of_sub_F_DFA_GOTO_SEQUENCEs)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(case_tac w2)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa a list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' q ya YSEQ' A w2 y x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(case_tac w)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) w = []")
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
    and s="[F_DFA_GOTO M (epda_initial M) (teB Do)]"
    in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  prefer 2
  apply(rule_tac
    M="M"
    and q="epda_initial M"
    in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) w \<noteq> []")
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(rule_tac
    t="(teB Do # list @ [yb])"
    and s="((teB Do # list) @ [yb])"
    in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((teB Do # list) @ [yb])"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list) @ (F_DFA_GOTO_SEQUENCE M (last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list)))) [yb])"
    in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) [yb]"
    and s="[F_DFA_GOTO M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))) yb]"
    in ssubst)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(subgoal_tac "(set (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list)) \<subseteq> epda_states M)")
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(rule_tac
    A="set (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # list))"
    in set_mp)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(blast)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(rule_tac
    w="(teB Do # list)"
    and q="(epda_initial M)"
    in F_DFA_GOTO_SEQUENCESound_main3)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(blast)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya A w2 y xa yb list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  prefer 2
  apply(rule_tac
    M="M"
    and q="epda_initial M"
    in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(force)
  apply(rename_tac n dP \<Phi> e \<pi>'' ya YSEQ' A w2 y xa w yb a list)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(subgoal_tac "r'_v \<in> parser_rules P")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(subgoal_tac "r'_v \<in> {r. \<exists>lpop rpop lpush rpush. r=\<lparr>rule_lpop=lpop,rule_rpop=rpop,rule_lpush=lpush,rule_rpush=rpush\<rparr> \<and> (\<exists>q\<delta> y \<beta> z A \<alpha> a \<delta>. y \<in> (cfgSTD_first G' (k- 1) (\<beta>@(liftB z))) \<and> \<lparr>prod_lhs=A,prod_rhs=\<alpha>@(teB a)#\<beta>\<rparr> \<in> cfg_productions G \<and> q\<delta>=last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#\<delta>)) \<and> \<lparr>cfg_item_lhs = A,cfg_item_rhs1 = \<alpha>,cfg_item_rhs2 = (teB a)#\<beta>,cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (teB Do#\<delta>) \<and> lpop=[q\<delta>] \<and> rpop=a#y \<and> lpush=[q\<delta>,F_DFA_GOTO M q\<delta> (teB a)] \<and> rpush=y)}")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  prefer 2
  apply(rule_tac
    P="\<lambda>x. r'_v \<in> x"
    and s="{r. r \<in> (parser_rules P) \<and> (parser_marker P) r = Some None}"
    in subst)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(rule AF_LR_PARSER_shift_rules)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> aa \<delta>)(*strict*)
  apply(rename_tac a \<delta>)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(thin_tac "\<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr> \<in> parser_rules P")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(subgoal_tac "\<exists>y'. w=a#y@y' \<and> dP (Suc 0) = Some (pair (Some \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr>) \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ@[teB a]), parserS_conf_scheduler = y@y'\<rparr>)")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  prefer 2
  apply(thin_tac "\<forall>dP YSEQ \<Phi> e w. viable_prefix G' (teB Do # YSEQ) \<and> parserS.derivation P dP \<and> parserS.belongs P dP \<and> maximum_of_domain dP n \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ), parserS_conf_scheduler = w\<rparr>) \<and> dP n = Some (pair e \<Phi>) \<longrightarrow> (\<exists>XSEQ y. \<Phi> = \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ), parserS_conf_scheduler = y\<rparr> \<and> (\<exists>x. w = x @ y \<and> viable_prefix G' (teB Do # XSEQ) \<and> length (get_labels dP n) = length (tau (parser_marker P) (get_labels dP n)) + length x \<and> (\<exists>dGn dG. cfgRM.derivation G dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>) \<and> (\<exists>e. dG dGn = Some (pair e \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>)) \<and> get_labels dG dGn = (List.rev (tau (parser_marker P) (get_labels dP n))))))")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(subgoal_tac "\<exists>e c. dP (Suc 0) = Some (pair (Some e) c)")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  prefer 2
  apply(rule parserS.some_position_has_details_before_max_dom_after_0)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(arith)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(erule exE)+
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(subgoal_tac "ea=\<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr>")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  prefer 2
  apply(subgoal_tac "Some ea=(Some \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr> # \<pi>'')!0")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  prefer 2
  apply(rule_tac
    t="Some \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr> # \<pi>''"
    and s="get_labels dP (Suc n)"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(rule_tac
    n="n"
    in parserS.identify_getLabel_with_derivation_get_label)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(subgoal_tac "Some ea = Some \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr>")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(rule_tac
    t="Some \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr>"
    and s="(Some \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr> # \<pi>'') ! 0"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(rule nth_first)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> ea c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> c)(*strict*)
  apply(subgoal_tac "parserS_step_relation P \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ), parserS_conf_scheduler = w\<rparr> \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr> c")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> c)(*strict*)
  prefer 2
  apply(rule_tac
    n="0"
    in parserS.position_change_due_to_step_relation)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> c)(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> c)(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> c)(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> c)(*strict*)
  apply(simp (no_asm_use) only: parserS_step_relation_def)
  apply(erule_tac conjE)+
  apply(erule exE)+
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta> c x xa)(*strict*)
  apply(erule_tac conjE)+
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> c x xa)(*strict*)
  apply(case_tac c)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> c x xa parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(rename_tac c1 c2)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> c x xa c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="x @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)]"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ) @ [F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)]"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(subgoal_tac "set(teB Do # \<delta>) \<subseteq> epda_events M")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  prefer 2
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule viable_prefix_in_CFG)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule Fact6_12__1)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(subgoal_tac "teB a \<in> epda_events M")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  prefer 2
  apply(subgoal_tac "valid_item G' k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teB a # \<beta>, cfg_item_look_ahead = z\<rparr>")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  prefer 2
  apply(rule Fact6_12__2)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(subgoal_tac "set (teB a # \<beta>) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  prefer 2
  apply(rule Item_rhs2_in_CFG)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="[F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)]"
    and s="F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) [teB a]"
    in subst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    A="set (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
    in set_mp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    w="(teB Do#\<delta>)"
    and q="epda_initial M"
    in F_DFA_GOTO_SEQUENCESound_main3)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule List.last_in_set)
  apply(rule F_DFA_GOTO_SEQUENCE_not_empty)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="(teB Do # YSEQ @ [teB a])"
    and s="(teB Do # YSEQ) @ [teB a]"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((teB Do # YSEQ) @ [teB a])"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ) @ (F_DFA_GOTO_SEQUENCE M (last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ)))) [teB a])"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' y \<beta> z A \<alpha> a \<delta>)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(erule_tac
    x="derivation_drop dP (Suc 0)"
    in allE)
  apply(erule_tac
    x="YSEQ@[teB a]"
    in allE)
  apply(erule_tac
    x="\<Phi>"
    in allE)
  apply(erule_tac
    x="if n=0 then None else e"
    in allE)
  apply(erule_tac
    x="y@y'"
    in allE)
  apply(erule impE)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule_tac
    x="XSEQ"
    in exI)
  apply(clarsimp)
  apply(rule_tac
    t="get_labels dP (Suc n)"
    and s="(get_labels dP (Suc 0))@(get_labels (derivation_drop dP (Suc 0)) ((Suc n)-(Suc 0)))"
    in ssubst)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule derivation_skip_get_labels)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="tau (parser_marker P) (get_labels dP (Suc 0) @ get_labels (derivation_drop dP (Suc 0)) n)"
    and s="tau (parser_marker P) (get_labels dP (Suc 0)) @ (tau (parser_marker P) (get_labels (derivation_drop dP (Suc 0)) n))"
    in ssubst)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule tau_append_commutes)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule_tac
    t="tau (parser_marker P) (get_labels dP (Suc 0))"
    and s="[]"
    in ssubst)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule_tac
    t="get_labels dP (Suc 0)"
    and s="[Some \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr>]"
    in ssubst)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule get_labelsLength)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule_tac
    x="dGn"
    in exI)
  apply(rule_tac
    x="dG"
    in exI)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(subgoal_tac "Some \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr> = get_labels dP (Suc 0) ! 0")
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(clarsimp)
  apply(rule length_1_cons_nth)
  apply(rule get_labelsLength)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule_tac
    t="get_labels dP (Suc 0) ! 0"
    and s="get_labels dP (Suc n) ! 0"
    in ssubst)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  prefer 2
  apply(rule parserS.identify_getLabel_with_derivation_get_label)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule_tac
    n="Suc 0"
    in take_nth_crop)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule_tac
    t="Suc n"
    and s="Suc 0 + n"
    in ssubst)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(rule parserS.get_labels_prefixes)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' XSEQ ya x dGn dG ea)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(subgoal_tac "set (teB Do # \<delta>) \<subseteq> epda_events M")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  prefer 2
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(rule viable_prefix_in_CFG)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(rule_tac
    k="k"
    and I="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teB a # \<beta>, cfg_item_look_ahead = z\<rparr>"
    in Fact6_12__1)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  prefer 2
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(rule AF_LR_PARSER_NonNone_effect_only_for_rules)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v a)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(rule conjI)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  prefer 2
  apply(rule context_conjI)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(rule_tac
    m = "n"
    in parserS.derivation_drop_preserves_derivation)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(rule conjI)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(rule parserS.derivation_drop_preserves_belongs)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(rule context_conjI)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(rule derivation_drop_preserves_generates_maximum_of_domain)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(simp add: derivation_drop_def)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(subgoal_tac "parserS_step_relation P \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ), parserS_conf_scheduler = a # y @ y'\<rparr> \<lparr>rule_lpop = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))], rule_rpop = a # y, rule_lpush = [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>)), F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))) (teB a)], rule_rpush = y\<rparr> \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ [teB a]), parserS_conf_scheduler = y @ y'\<rparr>")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  prefer 2
  apply(rule_tac
    n="0"
    in parserS.position_change_due_to_step_relation)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y')(*strict*)
  apply(simp (no_asm_use) only: parserS_step_relation_def)
  apply(erule_tac conjE)+
  apply(erule exE)+
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> y' x xa)(*strict*)
  apply(erule_tac conjE)+
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(subgoal_tac "valid_item_set G' k (teB Do # YSEQ) = valid_item_set G' k (teB Do # \<delta>)")
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  prefer 2
  apply(rule_tac
    t="valid_item_set G' k (teB Do # YSEQ)"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) SSw)" for SSw
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule F_LR_MACHINE_all_SOUND_NotNil)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    B="cfg_events G'"
    in two_elements_construct_domain_setA)
  apply(rule_tac
    t="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    and s="epda_events M"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    A="cfg_nonterminals G'"
    in two_elements_construct_domain_setB)
  apply(rule_tac
    t="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    and s="epda_events M"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="valid_item_set G' k (teB Do # \<delta>)"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) SSw)" for SSw
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule F_LR_MACHINE_all_SOUND_NotNil)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    B="cfg_events G'"
    in two_elements_construct_domain_setA)
  apply(rule_tac
    t="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    and s="epda_events M"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    A="cfg_nonterminals G'"
    in two_elements_construct_domain_setB)
  apply(rule_tac
    t="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    and s="epda_events M"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))"
    and s="last (x @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # \<delta>))])"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    k="k"
    and I="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>@[teB a], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr>"
    in Fact6_12__1)
  apply(rule_tac
    t="valid_item_set G' k (teB Do # YSEQ @ [teB a])"
    and s="valid_item_set G' k (teB Do # \<delta> @ [teB a])"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  prefer 2
  apply(rule_tac
    t="(teB Do # \<delta> @ [teB a])"
    and s="((teB Do # \<delta>) @ [teB a])"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    I="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = teB a#\<beta>, cfg_item_look_ahead = z\<rparr>"
    in valid_item_set_F_VALID_ITEM_SET_GOTO__passes)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="(teB Do # YSEQ @ [teB a])"
    and s="((teB Do # YSEQ) @ [teB a])"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="(teB Do # \<delta> @ [teB a])"
    and s="((teB Do # \<delta>) @ [teB a])"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule valid_item_set_eq_preserved_under_post_extension)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    t="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    and s="epda_events M"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule set_concat_subset)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule set_concat_subset)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    B="set (teB a # \<beta>)"
    in subset_trans)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule_tac
    s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    and t="epda_events M"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule Item_rhs2_in_CFG)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(rule Fact6_12__2)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e \<pi>'' y \<beta> z A \<alpha> a \<delta> x xa)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
  apply(force)
  apply(rename_tac dPn n dP YSEQ \<pi>' \<Phi> e w r' \<pi>'' r'_v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
    x="Suc 0"
    in allE)
  apply(subgoal_tac "\<exists>e c. dP (Suc 0) = Some (pair (Some e) c)")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v)(*strict*)
  prefer 2
  apply(rule parserS.some_position_has_details_before_max_dom_after_0)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v)(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v)(*strict*)
  apply(blast)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v)(*strict*)
  apply(arith)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(subgoal_tac "ea=r'_v")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(simp add: parser_step_labels_def)
  apply(subgoal_tac "parser_marker P r'_v \<noteq> None")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(rule_tac
    t="parser_marker P"
    and s="(\<lambda>x. if (\<exists>!y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) then Some(THE y. (x,y) \<in> (AF_LR_PARSER__rules G G' M k)) else None)"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(clarsimp)
  apply(rule X6_3_InformationOnRules_UniqueEffect)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v c)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(subgoal_tac "Some ea = Some r'_v")
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(rule_tac
    t="Some r'_v"
    and s="get_labels dP (Suc n) ! 0"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  prefer 2
  apply(rule parserS.identify_getLabel_with_derivation_get_label)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(rule_tac
    t="get_labels dP (Suc n)"
    and s="Some r'_v # \<pi>''"
    in ssubst)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(force)
  apply(rename_tac n dP YSEQ \<Phi> e w \<pi>'' r'_v ea c)(*strict*)
  apply(thin_tac "Some r'_v # \<pi>'' = get_labels dP (Suc n)")
  apply(force)
  done

lemma F_LR_MACHINE_F_DFA_GOTO_SEQUENCE_everywhere: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> d 0 = Some (pair None \<lparr>parserS_conf_stack = [parser_initial P], parserS_conf_scheduler = w @ v @ [parser_bottom P]\<rparr>)
  \<Longrightarrow> d i = Some (pair e \<lparr>parserS_conf_stack = seq, parserS_conf_scheduler = v @ [parser_bottom P]\<rparr>)
  \<Longrightarrow> \<exists>s. set s \<subseteq> epda_events M \<and> seq = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s)"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
  prefer 2
  apply(rule F_LR_MACHINE_all_Connected)
  prefer 3
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(induct i arbitrary: v w e seq)
  apply(rename_tac v w e seq)(*strict*)
  apply(clarsimp)
  apply(rename_tac v)(*strict*)
  apply(rule_tac
      t="parser_initial P"
      and s="F_DFA_GOTO M (epda_initial M) (teB Do)"
      in ssubst)
  apply(rename_tac v)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac v)(*strict*)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rule sym)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac v)(*strict*)
  apply(force)
  apply(rename_tac v)(*strict*)
  apply(force)
  apply(rename_tac v)(*strict*)
  apply(force)
  apply(rename_tac v)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac v)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac i v w e seq)(*strict*)
  apply(subgoal_tac "\<exists>e seq v. d i = Some (pair e \<lparr>parserS_conf_stack = seq, parserS_conf_scheduler = v @ [parser_bottom P]\<rparr>) ")
  apply(rename_tac i v w e seq)(*strict*)
  prefer 2
  apply(case_tac "d i")
  apply(rename_tac i v w e seq)(*strict*)
  apply(rule parserS.derivationNoFromNone)
  apply(rename_tac i v w e seq)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i v w e seq a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v w e seq option b)(*strict*)
  apply(case_tac e)
  apply(rename_tac i v w e seq option b)(*strict*)
  apply(rule parserS.derivation_Always_PreEdge_prime)
  apply(rename_tac i v w e seq option b)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq option b)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v w seq option b a)(*strict*)
  apply(case_tac b)
  apply(rename_tac i v w seq option b a parserS_conf_stack parserS_conf_scheduler)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v w seq option a parserS_conf_stack parserS_conf_scheduler)(*strict*)
  apply(subgoal_tac "\<exists>v'. parserS_conf_scheduler=v'@[parser_bottom P] \<and> (parser_bottom P \<notin> set v')")
  apply(rename_tac i v w seq option a parserS_conf_stack parserS_conf_scheduler)(*strict*)
  prefer 2
  apply(rule PARSER_always_bottom)
  apply(rename_tac i v w seq option a parserS_conf_stack parserS_conf_scheduler)(*strict*)
  apply(force)
  apply(rename_tac i v w seq option a parserS_conf_stack parserS_conf_scheduler)(*strict*)
  apply(force)
  apply(rename_tac i v w seq option a parserS_conf_stack parserS_conf_scheduler)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v w e seq)(*strict*)
  apply(erule exE)+
  apply(rename_tac i v w e seq ea seqa va)(*strict*)
  apply(case_tac e)
  apply(rename_tac i v w e seq ea seqa va)(*strict*)
  apply(rule parserS.derivation_Always_PreEdge_prime)
  apply(rename_tac i v w e seq ea seqa va)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq ea seqa va)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(clarify)
  apply(subgoal_tac "valid_parser P")
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      in AF_LR_PARSER_valid_parser)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(subgoal_tac "\<exists>v'. v'@(v@[parser_bottom P])=(va@[parser_bottom P])")
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  prefer 2
  apply(rule_tac
      P="P"
      and d="d"
      and e="ea"
      and w="seqa"
      and i="i"
      and j="Suc 0"
      in PARSER_always_suffixing)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(force)
  apply(rename_tac i v w e seq ea seqa va a)(*strict*)
  apply(clarify)
  apply(rename_tac i v w e seq ea seqa va a v')(*strict*)
  apply(clarsimp)
  apply(rename_tac i v w seq ea seqa a v')(*strict*)
  apply(subgoal_tac "\<exists>v''. v''@(v' @ v @ [parser_bottom P]) = w @ v @ [parser_bottom P]")
  apply(rename_tac i v w seq ea seqa a v')(*strict*)
  prefer 2
  apply(rule_tac
      P="P"
      and d="d"
      and i="0"
      and j="i"
      in PARSER_always_suffixing)
  apply(rename_tac i v w seq ea seqa a v')(*strict*)
  apply(force)
  apply(rename_tac i v w seq ea seqa a v')(*strict*)
  apply(force)
  apply(rename_tac i v w seq ea seqa a v')(*strict*)
  apply(force)
  apply(rename_tac i v w seq ea seqa a v')(*strict*)
  apply(force)
  apply(rename_tac i v w seq ea seqa a v')(*strict*)
  apply(force)
  apply(rename_tac i v w seq ea seqa a v')(*strict*)
  apply(clarify)
  apply(rename_tac i v w seq ea seqa a v' v'')(*strict*)
  apply(clarsimp)
  apply(rename_tac i v seq ea seqa a v' v'')(*strict*)
  apply(erule_tac
      x="v'@v"
      in meta_allE)
  apply(erule_tac
      x="v''"
      in meta_allE)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(erule_tac
      x="seqa"
      in meta_allE)
  apply(erule meta_impE)
  apply(rename_tac i v seq ea seqa a v' v'')(*strict*)
  apply(force)
  apply(rename_tac i v seq ea seqa a v' v'')(*strict*)
  apply(erule meta_impE)
  apply(rename_tac i v seq ea seqa a v' v'')(*strict*)
  apply(force)
  apply(rename_tac i v seq ea seqa a v' v'')(*strict*)
  apply(clarsimp)
  apply(rename_tac i v seq ea a v' v'' s)(*strict*)
  apply(subgoal_tac "parserS_step_relation P \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s), parserS_conf_scheduler = v' @ v @ [parser_bottom P]\<rparr> a \<lparr>parserS_conf_stack = seq, parserS_conf_scheduler = v @ [parser_bottom P]\<rparr>")
  apply(rename_tac i v seq ea a v' v'' s)(*strict*)
  prefer 2
  apply(rule_tac
      n="i"
      in parserS.position_change_due_to_step_relation)
  apply(rename_tac i v seq ea a v' v'' s)(*strict*)
  apply(blast)
  apply(rename_tac i v seq ea a v' v'' s)(*strict*)
  apply(blast)
  apply(rename_tac i v seq ea a v' v'' s)(*strict*)
  apply(blast)
  apply(rename_tac i v seq ea a v' v'' s)(*strict*)
  apply(simp (no_asm_use) only: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i v ea a v' v'' s x xa)(*strict*)
  apply(subgoal_tac "a \<in> parser_rules P")
  apply(rename_tac i v ea a v' v'' s x xa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac i v ea a v' v'' s x xa)(*strict*)
  apply(subgoal_tac "a \<in> (\<lambda>(x,y). x) ` (AF_LR_PARSER__rules G G' M k)")
  apply(rename_tac i v ea a v' v'' s x xa)(*strict*)
  prefer 2
  apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac i v ea a v' v'' s x xa)(*strict*)
  apply(thin_tac "a \<in> parser_rules P")
  apply(case_tac a)
  apply(rename_tac i v ea a v' v'' s x xa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v' v'' s x xa rule_lpop rule_lpush rule_rpush b)(*strict*)
  apply(rename_tac l1 l2 r b)
  apply(rename_tac i v ea v' v'' s x xa l1 l2 r b)(*strict*)
  apply(simp add: AF_LR_PARSER__rules_def)
  apply(erule disjE)
  apply(rename_tac i v ea v' v'' s x xa l1 l2 r b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(subgoal_tac "set [teA (cfg_item_lhs I)] \<subseteq> epda_events M")
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  prefer 2
  apply(subgoal_tac "cfg_item_lhs I \<in> cfg_nonterminals G")
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp (no_asm_use))
  apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp (no_asm_use) add: two_elements_construct_domain_def)
  apply(rule disjI1)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>x. prod_lhs x \<in> cfg_nonterminals G \<and> setA (prod_rhs x) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs x) \<subseteq> cfg_events G"
      in ballE)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(subgoal_tac "set (cfg_item_rhs2 I) \<subseteq> epda_events M")
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  prefer 2
  apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def valid_cfg_def)
  apply(erule conjE)+
  apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs2 I\<rparr>"
      and P="\<lambda>x. prod_lhs x \<in> cfg_nonterminals G \<and> setA (prod_rhs x) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs x) \<subseteq> cfg_events G"
      in ballE)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(simp add: F_CFG_AUGMENT_def)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(subgoal_tac "q_seq=F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  prefer 2
  apply(rule F_DFA_GOTO_SEQUENCE_F_EPDA_GOTO_SEQUENCE_elem)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q q_seq I qA)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  apply(thin_tac "F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) \<in> F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)")
  apply(subgoal_tac "qA=F_DFA_GOTO M q (teA (cfg_item_lhs I))")
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  prefer 2
  apply(rule F_DFA_GOTO_F_EPDA_GOTO_elem)
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I qA)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(thin_tac "F_DFA_GOTO M q (teA (cfg_item_lhs I)) \<in> F_EPDA_GOTO M q (teA (cfg_item_lhs I))")
  apply(subgoal_tac "\<exists>w y. w@y#(cfg_item_rhs2 I)=(teB Do # s) \<and> x=F_DFA_GOTO_SEQUENCE M (epda_initial M) w \<and> q=F_DFA_GOTO M (last ((epda_initial M)#x)) y")
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      and G'="G'"
      and Do="Do"
      and S'="S'"
      and M="M"
      in partial_F_DFA_GOTO_SEQUENCE_eq_implies_existence_of_sub_F_DFA_GOTO_SEQUENCEs)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(force)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I)(*strict*)
  apply(erule exE)+
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "set w \<subseteq> epda_events M")
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  prefer 2
  apply(rule_tac
      B="set (w @ y # cfg_item_rhs2 I)"
      in subset_trans)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(rule set_append1)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(rule_tac
      t="w @ y # cfg_item_rhs2 I"
      and s="teB Do # s"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(rule set_take_head2)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(rule_tac
      G="G"
      in F_LR_MACHINE_Do_in_cfg_events)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp only: AF_LR_PARSER_input_def)
  apply(force)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(subgoal_tac "y \<in> epda_events M")
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  prefer 2
  apply(rule_tac
      A="set (w @ y # cfg_item_rhs2 I)"
      in set_mp)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(rule_tac
      t="w @ y # cfg_item_rhs2 I"
      and s="teB Do # s"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(rule set_take_head2)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(rule_tac
      G="G"
      in F_LR_MACHINE_Do_in_cfg_events)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp only: AF_LR_PARSER_input_def)
  apply(force)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(simp (no_asm_use))
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(subgoal_tac "\<exists>w'. w@[y]=(teB Do) # w'")
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  prefer 2
  apply(case_tac w)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(case_tac y)
  apply(rename_tac i v ea v'' s x xa r q I w y a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' s x xa r q I w y b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' s x xa r q I w y a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' s x xa r q I w y)(*strict*)
  apply(erule exE)+
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      x="w'@[teA (cfg_item_lhs I)]"
      in exI)
  apply(rule_tac
      t="x"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) w"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="q"
      and s="F_DFA_GOTO M (last (epda_initial M # x)) y"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) w @ [F_DFA_GOTO M (last (epda_initial M # x)) y, F_DFA_GOTO M (F_DFA_GOTO M (last (epda_initial M # x)) y) (teA (cfg_item_lhs I))]"
      and s="(F_DFA_GOTO_SEQUENCE M (epda_initial M) w @ [F_DFA_GOTO M (last (epda_initial M # x)) y])@[ F_DFA_GOTO M (F_DFA_GOTO M (last (epda_initial M # x)) y) (teA (cfg_item_lhs I))]"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="x"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) w"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="(F_DFA_GOTO_SEQUENCE M (epda_initial M) w @ [F_DFA_GOTO M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) y])"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@[y])"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="[F_DFA_GOTO M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) y]"
      and s="F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [y]"
      in subst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      a="epda_initial M"
      and w="F_DFA_GOTO_SEQUENCE M (epda_initial M) w"
      in prop_last)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      ?q0.0="epda_initial M"
      and w="w"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule sym)
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(subgoal_tac "length (w@[y]) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@[y]))")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule set_concat_subset)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w) \<in> epda_states M")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(rule_tac
      a="epda_initial M"
      and w="F_DFA_GOTO_SEQUENCE M (epda_initial M) w"
      in prop_last)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      ?q0.0="epda_initial M"
      and w="w"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(subgoal_tac "length [y] = length (F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [y])")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(rule_tac
      M="M"
      and q="(last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule conjI)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(thin_tac "d (Suc i) = Some (pair (Some \<lparr>rule_lpop = q # F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I), rule_rpop = r, rule_lpush = [q, F_DFA_GOTO M q (teA (cfg_item_lhs I))], rule_rpush = r\<rparr>) \<lparr>parserS_conf_stack = x @ [q, F_DFA_GOTO M q (teA (cfg_item_lhs I))], parserS_conf_scheduler = r @ xa\<rparr>)")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(thin_tac "\<lparr>rule_lpop = q # F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I), rule_rpop = r, rule_lpush = [q, F_DFA_GOTO M q (teA (cfg_item_lhs I))], rule_rpush = r\<rparr> \<in> parser_rules P")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' s xa r I w y w' xb)(*strict*)
  apply(rule_tac
      A="set w'"
      in set_mp)
  apply(rename_tac i v ea v'' s xa r I w y w' xb)(*strict*)
  apply(rule_tac
      B="set (w@[y])"
      in subset_trans)
  apply(rename_tac i v ea v'' s xa r I w y w' xb)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s xa r I w y w' xb)(*strict*)
  apply(rule set_concat_subset)
  apply(rename_tac i v ea v'' s xa r I w y w' xb)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s xa r I w y w' xb)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s xa r I w y w' xb)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="teB Do # w' @ [teA (cfg_item_lhs I)]"
      and s="(w@[y])@[teA (cfg_item_lhs I)]"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((w @ [y]) @ [teA (cfg_item_lhs I)])"
      and s="F_DFA_GOTO_SEQUENCE SSM SSp SSw1 @ F_DFA_GOTO_SEQUENCE SSM (last (SSp # F_DFA_GOTO_SEQUENCE SSM SSp SSw1)) SSw2" for SSM SSp SSw1 SSw2
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule set_concat_subset)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="[F_DFA_GOTO M (F_DFA_GOTO M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) y) (teA (cfg_item_lhs I))]"
      and s="F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) y) [(teA (cfg_item_lhs I))]"
      in subst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule DFA_F_DFA_GOTO_in_states)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 3
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(case_tac x)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule_tac
      t="(if x = [] then epda_initial M else last x)"
      and s="last(F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule_tac
      w="w"
      and ?q0.0="epda_initial M"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  prefer 4
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  prefer 2
  apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [y]))"
      and s="F_DFA_GOTO M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) y"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(subgoal_tac "length [teB Do] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule_tac
      B="set (w@[y])"
      in subset_trans)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule set_concat_subset)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(subgoal_tac "length (w@[y]) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@[y]))")
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  prefer 2
  apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(rule set_concat_subset)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(case_tac w)
  apply(rename_tac i v ea v'' s x xa r q I w y w')(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(rule conjI)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
      and s="[F_DFA_GOTO M (epda_initial M) (teB Do)]"
      in ssubst)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' xa r I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [y]))"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [y]))"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule last_ConsR)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule last_ConsR)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [y]))"
      and s="last (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M SSp SSw1)) SSw2)" for SSp SSw1 SSw2
      in subst)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_concat)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) [y]"
      and s="[F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) y]"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(rule_tac
      ?q0.0="epda_initial M"
      and w="w"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa r q I w y w' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v' v'' s x xa l1 l2 r b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(subgoal_tac "set [teA (cfg_item_lhs I)] \<subseteq> epda_events M")
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  prefer 2
  apply(subgoal_tac "cfg_item_lhs I \<in> cfg_nonterminals G")
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp (no_asm_use))
  apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp (no_asm_use) add: two_elements_construct_domain_def)
  apply(rule disjI1)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
    x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>"
    and P="\<lambda>x. prod_lhs x \<in> cfg_nonterminals G \<and> setA (prod_rhs x) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs x) \<subseteq> cfg_events G"
    in ballE)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(subgoal_tac "set (cfg_item_rhs1 I @ cfg_item_rhs2 I) \<subseteq> epda_events M")
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  prefer 2
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
    in subset_trans)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule prod_rhs_in_cfg_events)
    apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
   apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule prod_rhs_in_nonterms)
   apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
    apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    x="s@[teB a]"
    in exI)
  apply(subgoal_tac "teB a \<in> epda_events M")
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  prefer 2
  apply(rule_tac
    A="set ((cfg_item_rhs2 I))"
    in set_mp)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    A="set (take (Suc 0) (cfg_item_rhs2 I))"
    in set_mp)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule List.set_take_subset)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    t="take (Suc 0) (cfg_item_rhs2 I)"
    and s="[teB a]"
    in ssubst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp (no_asm_use))
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule set_concat_subset)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp (no_asm_use))
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="x@[q,qA]"
    and s="(x@[q])@[qA]"
    in ssubst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    t="x@[q]"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s)"
    in ssubst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(subgoal_tac "qA=F_DFA_GOTO M q (teB a)")
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  prefer 2
  apply(rule F_DFA_GOTO_F_EPDA_GOTO_elem)
      apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
      apply(force)
     apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
     apply(force)
    apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
    apply(force)
   apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
   apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    t="qA"
    and s="F_DFA_GOTO M q (teB a)"
    in ssubst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    t="[F_DFA_GOTO M q (teB a)]"
    and s="F_DFA_GOTO_SEQUENCE M q [teB a]"
    in subst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
     apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
     apply(force)
    apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
    apply(force)
   apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
   apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule sym)
  apply(rule_tac
    t="q"
    and s="last(F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s))"
    in ssubst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    t="teB Do # s @ take (Suc 0) (cfg_item_rhs2 I)"
    and s="(teB Do # s) @ [teB a]"
    in ssubst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule_tac
    t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s))"
    and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # s))"
    in subst)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule last_ConsR)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
     apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
     apply(force)
    apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
    apply(force)
   apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
   apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(rule set_take_head2)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  apply(rename_tac i v ea v'' s x xa q a y qA I)(*strict*)
  apply(force)
  done

theorem Lemma6__30: "
  AF_LR_PARSER_input G F Do S' G' M (P :: (('nonterminal DT_symbol, 'event DT_symbol) DT_cfg_item set, 'event DT_symbol, ('nonterminal DT_symbol, 'event DT_symbol) cfg_step_label option option) parser) k
  \<Longrightarrow> parserS.marked_language P \<subseteq> cfgRM.marked_language G"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_AUGMENT__makes_CFG)
   apply(simp add: F_CFG_AUGMENT__input_def)
   apply(simp add: AF_LR_PARSER_input_def)
   apply(force)
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
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(simp add: parserS.marked_language_def cfgRM.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(subgoal_tac "parserS.belongs P d")
   apply(rename_tac x d)(*strict*)
   prefer 2
   apply(simp only: parserS.belongs_def)
   apply(clarsimp)
   apply(rename_tac x d i)(*strict*)
   apply(case_tac i)
    apply(rename_tac x d i)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d)(*strict*)
    apply(simp add: parserS.derivation_initial_def)
    apply(case_tac "d 0")
     apply(rename_tac x d)(*strict*)
     apply(clarsimp)
    apply(rename_tac x d a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac x d a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d b)(*strict*)
    apply(simp add: parserS_initial_configurations_def)
   apply(rename_tac x d i nat)(*strict*)
   apply(case_tac "d i")
    apply(rename_tac x d i nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d i nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d nat a)(*strict*)
   apply(case_tac a)
   apply(rename_tac x d nat a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d nat option b)(*strict*)
   apply(case_tac option)
    apply(rename_tac x d nat option b)(*strict*)
    apply(rule parserS.derivation_Always_PreEdge_prime)
     apply(rename_tac x d nat option b)(*strict*)
     apply(force)
    apply(rename_tac x d nat option b)(*strict*)
    apply(force)
   apply(rename_tac x d nat option b a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d nat b a)(*strict*)
   apply(simp add: parserS.derivation_initial_def)
   apply(case_tac "d 0")
    apply(rename_tac x d nat b a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d nat b a aa)(*strict*)
   apply(clarsimp)
   apply(case_tac aa)
   apply(rename_tac x d nat b a aa option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d nat b a ba)(*strict*)
   apply(rule_tac
      m="0"
      and n="Suc nat"
      in parserS.later_in_configuration_label)
        apply(rename_tac x d nat b a ba)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(rule_tac
      G="G"
      in AF_LR_PARSER_valid_parser)
              apply(rename_tac x d nat b a ba)(*strict*)
              apply(force)+
     apply(rename_tac x d nat b a ba)(*strict*)
     apply(simp add: parserS_initial_configurations_def)
    apply(rename_tac x d nat b a ba)(*strict*)
    apply(force)
   apply(rename_tac x d nat b a ba)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(simp add: parserS_marked_effect_def parserS_marking_condition_def parserS_marking_configurations_def parserS_configurations_def parserS_initial_configurations_def)
  apply(erule exE)+
  apply(rename_tac x d c)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x d c ca i e cb)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x d c ca i e cb l la r ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e l f w wa)(*strict*)
  apply(subgoal_tac "\<exists>v'. wa @ [parser_bottom P] = v'@[parser_bottom P] \<and> (parser_bottom P \<notin> set v')")
   apply(rename_tac d i e l f w wa)(*strict*)
   prefer 2
   apply(rule PARSER_always_bottom)
    apply(rename_tac d i e l f w wa)(*strict*)
    apply(force)
   apply(rename_tac d i e l f w wa)(*strict*)
   apply(force)
  apply(rename_tac d i e l f w wa)(*strict*)
  apply(erule exE)+
  apply(rename_tac d i e l f w wa v')(*strict*)
  apply(erule conjE)+
  apply(clarsimp)
  apply(rename_tac d i e l f w v')(*strict*)
  apply(rename_tac w)
  apply(rename_tac d i e l f wa w)(*strict*)
  apply(subgoal_tac "\<exists>XSEQ y x. \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#[teA (cfg_initial G)]),parserS_conf_scheduler=[parser_bottom P]\<rparr> = \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#XSEQ),parserS_conf_scheduler=y\<rparr> \<and> w@[parser_bottom P]=x@y \<and> viable_prefix G' (teB Do#XSEQ) \<and> (length (get_labels (derivation_take d i) i)) = length (tau (parser_marker P) (get_labels (derivation_take d i) i)) + length x \<and> (\<exists>dG e dGn. cfgRM.derivation G dG \<and> maximum_of_domain dG dGn \<and> dG 0 = Some (pair None \<lparr>cfg_conf=XSEQ\<rparr>) \<and> dG dGn = Some (pair e \<lparr>cfg_conf=[]@(liftB x)\<rparr>) \<and> (get_labels dG dGn) = (List.rev (tau (parser_marker P) (get_labels (derivation_take d i) i))))")
   apply(rename_tac d i e l f wa w)(*strict*)
   apply(simp add: cfg_marked_effect_def cfg_marking_condition_def cfg_initial_configurations_def cfg_configurations_def cfg_marking_configuration_def)
   apply(clarsimp)
   apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
   apply(rule_tac
      x="dG"
      in exI)
   apply(clarsimp)
   apply(subgoal_tac "cfg_initial G \<in> cfg_nonterminals G")
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    prefer 2
    apply(rule cfg_initial_in_nonterms)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
   apply(simp add: cfgRM.derivation_initial_def)
   apply(simp add: cfg_initial_configurations_def)
   apply(subgoal_tac "set ([teB Do]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
   apply(subgoal_tac "set XSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    prefer 2
    apply(subgoal_tac "set (teB Do#XSEQ) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     prefer 2
     apply(rule viable_prefix_in_CFG)
      apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
      apply(force)
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     apply(force)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(force)
   apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
   apply(subgoal_tac "(teB Do # XSEQ) = [teB Do, teA (cfg_initial G)]")
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    prefer 2
    apply(rule_tac
      k="k"
      and G="G"
      and G'="G'"
      and S'="S'"
      and Do="Do"
      in DollarInitialReadItem_OnlyIn_Specific_Valid)
          apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     apply(force)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(rule_tac
      t="valid_item_set G' k (teB Do # XSEQ)"
      and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#XSEQ))"
      in ssubst)
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
            apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
            apply(force)
           apply(simp add: AF_LR_PARSER_input_def)
           apply(force)
          apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
         apply(force)
        apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
        apply(force)
       apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
       apply(rule two_elements_construct_domain_setA)
       apply(force)
      apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
      apply(rule two_elements_construct_domain_setB)
      apply(force)
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     apply(force)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ)"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]"
      in ssubst)
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     apply(force)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(rule_tac
      A="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])))-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      in set_mp)
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     apply(force)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) - {I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}"
      and s="{\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>}"
      in ssubst)
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     apply(rule_tac
      k="k"
      and G="G"
      and G'="G'"
      and S'="S'"
      and Do="Do"
      in F_LR_MACHINE_prefix_closureise_additionalItems_2)
               apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
               apply(simp add: AF_LR_PARSER_input_def)
              apply(simp add: AF_LR_PARSER_input_def)
              apply(force)
             apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
          apply(force)
         apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
         apply(force)
        apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
        apply(force)
       apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
      apply(force)
     apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
     apply(force)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(force)
   apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(force)
   apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
    apply(rule_tac
      x="ea"
      in exI)
    apply(rule_tac
      x="\<lparr>cfg_conf = liftB w\<rparr>"
      in exI)
    apply(clarsimp)
    apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
    apply(rule conjI)
     apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
     apply(rule_tac
      x="dGn"
      in exI)
     apply(clarsimp)
    apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac d i e l f wa w XSEQ dG ea dGn)(*strict*)
   apply(rule_tac
      x="dGn"
      in exI)
   apply(rule_tac
      x="ea"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf = liftB w\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
    apply(rule setA_liftB)
   apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
   apply(rule conjI)
    apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
    apply(rule_tac
      t="setA (liftB w)"
      and s="{}"
      in ssubst)
     apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
     apply(rule setA_liftB)
    apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
    apply(force)
   apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
   apply(rule_tac
      t="setB (liftB w)"
      and s="set w"
      in subst)
    apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
    apply(rule set_setBliftB)
   apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
   apply(subgoal_tac "parser_events P = cfg_events G'")
    apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def F_CFG_AUGMENT_def)
   apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
   apply(subgoal_tac "cfg_events G' = cfg_events G \<union> {parser_bottom P}")
    apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def F_CFG_AUGMENT_def)
   apply(rename_tac d i e l f wa w dG ea dGn)(*strict*)
   apply(force)
  apply(rename_tac d i e l f wa w)(*strict*)
  apply(rule_tac
      S'="S'"
      and k="k"
      and dP="(derivation_take d i)"
      and dPn="i"
      in Lemma6__29)
         apply(rename_tac d i e l f wa w)(*strict*)
         apply(force)
        apply(rename_tac d i e l f wa w)(*strict*)
        apply(rule_tac
      k="k"
      and I="\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do],cfg_item_rhs2=[teA (cfg_initial G),teB Do],cfg_item_look_ahead=[]\<rparr>"
      and \<gamma>="[teB Do]"
      in Fact6_12__1)
        apply(rule_tac
      t="valid_item_set G' k [teB Do]"
      and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
         apply(rename_tac d i e l f wa w)(*strict*)
         apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
                apply(rename_tac d i e l f wa w)(*strict*)
                apply(force)
               apply(simp add: AF_LR_PARSER_input_def)
               apply(force)
              apply(rename_tac d i e l f wa w)(*strict*)
              apply(simp add: AF_LR_PARSER_input_def)
             apply(rename_tac d i e l f wa w)(*strict*)
             apply(force)
            apply(rename_tac d i e l f wa w)(*strict*)
            apply(force)
           apply(rename_tac d i e l f wa w)(*strict*)
           apply(force)
          apply(rename_tac d i e l f wa w)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
         apply(rename_tac d i e l f wa w)(*strict*)
         apply(force)
        apply(rename_tac d i e l f wa w)(*strict*)
        apply(rule_tac
      A="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])))-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      in set_mp)
         apply(rename_tac d i e l f wa w)(*strict*)
         apply(force)
        apply(rename_tac d i e l f wa w)(*strict*)
        apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) - {I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}"
      and s="{\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}"
      in ssubst)
         apply(rename_tac d i e l f wa w)(*strict*)
         apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_1)
                   apply(rename_tac d i e l f wa w)(*strict*)
                   apply(simp add: AF_LR_PARSER_input_def)
                  apply(simp add: AF_LR_PARSER_input_def)
                  apply(force)
                 apply(rename_tac d i e l f wa w)(*strict*)
                 apply(force)
                apply(rename_tac d i e l f wa w)(*strict*)
                apply(simp add: AF_LR_PARSER_input_def)
               apply(rename_tac d i e l f wa w)(*strict*)
               apply(simp add: AF_LR_PARSER_input_def)
              apply(rename_tac d i e l f wa w)(*strict*)
              apply(force)
             apply(rename_tac d i e l f wa w)(*strict*)
             apply(force)
            apply(rename_tac d i e l f wa w)(*strict*)
            apply(force)
           apply(rename_tac d i e l f wa w)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac d i e l f wa w)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac d i e l f wa w)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac d i e l f wa w)(*strict*)
        apply(force)
       apply(rename_tac d i e l f wa w)(*strict*)
       apply(rule_tac parserS.derivation_take_preserves_derivation)
       apply(force)
      apply(rename_tac d i e l f wa w)(*strict*)
      apply(rule maximum_of_domain_derivation_take)
      apply(force)
     apply(rename_tac d i e l f wa w)(*strict*)
     apply(force)
    apply(rename_tac d i e l f wa w)(*strict*)
    apply(rule parserS.derivation_take_preserves_belongs)
    apply(force)
   apply(rename_tac d i e l f wa w)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: parserS.derivation_initial_def)
   apply(simp add: parserS_initial_configurations_def)
   apply(rule_tac
      t="parser_initial P"
      and s="F_DFA_GOTO M (epda_initial M) (teB Do)"
      in ssubst)
    apply(rename_tac d i e l f wa w)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(rename_tac d i e l f wa w)(*strict*)
   apply(rule sym)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(rename_tac d i e l f wa w)(*strict*)
       apply(force)
      apply(rename_tac d i e l f wa w)(*strict*)
      apply(force)
     apply(rename_tac d i e l f wa w)(*strict*)
     apply(force)
    apply(rename_tac d i e l f wa w)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac d i e l f wa w)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(rename_tac d i e l f wa w)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rule conjI)
   apply(rename_tac d i e l f wa w)(*strict*)
   apply(force)
  apply(rename_tac d i e l f wa w)(*strict*)
  apply(subgoal_tac "f \<in> {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do,teA (cfg_initial G)])}")
   apply(rename_tac d i e l f wa w)(*strict*)
   prefer 2
   apply(rule_tac
      t="{last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])}"
      and s="parser_marking P"
      in ssubst)
    apply(rename_tac d i e l f wa w)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(rename_tac d i e l f wa w)(*strict*)
   apply(force)
  apply(rename_tac d i e l f wa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e l wa w)(*strict*)
  apply(subgoal_tac "epda_initial M \<in> epda_states M")
   apply(rename_tac d i e l wa w)(*strict*)
   prefer 2
   apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac d i e l wa w)(*strict*)
  apply(subgoal_tac "set [teB Do, teA (cfg_initial G)] \<subseteq> epda_events M")
   apply(rename_tac d i e l wa w)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_DoS_in_cfg_events)
        apply(rename_tac d i e l wa w)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(simp add: AF_LR_PARSER_input_def)
       apply(force)
      apply(rename_tac d i e l wa w)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac d i e l wa w)(*strict*)
     apply(force)
    apply(rename_tac d i e l wa w)(*strict*)
    apply(force)
   apply(rename_tac d i e l wa w)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac d i e l wa w)(*strict*)
  apply(subgoal_tac "teB Do \<in> epda_events M")
   apply(rename_tac d i e l wa w)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_LR_MACHINE_Do_in_cfg_events)
        apply(rename_tac d i e l wa w)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(simp add: AF_LR_PARSER_input_def)
       apply(force)
      apply(rename_tac d i e l wa w)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac d i e l wa w)(*strict*)
     apply(force)
    apply(rename_tac d i e l wa w)(*strict*)
    apply(force)
   apply(rename_tac d i e l wa w)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac d i e l wa w)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> (epda_events M) \<and> wa @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])] = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#w)")
   apply(rename_tac d i e l wa w)(*strict*)
   prefer 2
   apply(simp add: parserS.derivation_initial_def)
   apply(simp add: parserS_initial_configurations_def)
   apply(rule_tac
      v="[]"
      in F_LR_MACHINE_F_DFA_GOTO_SEQUENCE_everywhere)
          apply(rename_tac d i e l wa w)(*strict*)
          apply(force)
         apply(rename_tac d i e l wa w)(*strict*)
         apply(force)
        apply(rename_tac d i e l wa w)(*strict*)
        apply(force)
       apply(rename_tac d i e l wa w)(*strict*)
       apply(force)
      apply(rename_tac d i e l wa w)(*strict*)
      apply(force)
     apply(rename_tac d i e l wa w)(*strict*)
     apply(force)
    apply(rename_tac d i e l wa w)(*strict*)
    apply(force)
   apply(rename_tac d i e l wa w)(*strict*)
   apply(force)
  apply(rename_tac d i e l wa w)(*strict*)
  apply(erule exE)+
  apply(rename_tac d i e l wa w wb)(*strict*)
  apply(rename_tac wxy)
  apply(rename_tac d i e l wa w wxy)(*strict*)
  apply(subgoal_tac "\<exists>w. set w \<subseteq> (epda_events M) \<and> wa @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])] = F_DFA_GOTO_SEQUENCE M (epda_initial M) w")
   apply(rename_tac d i e l wa w wxy)(*strict*)
   prefer 2
   apply(rule_tac
      x="teB Do#wxy"
      in exI)
   apply(force)
  apply(rename_tac d i e l wa w wxy)(*strict*)
  apply(thin_tac "set wxy \<subseteq> (epda_events M) \<and> wa @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])] = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#wxy)")
  apply(rename_tac d i e l wa w wxy)(*strict*)
  apply(thin_tac "d 0 = Some (pair None \<lparr>parserS_conf_stack = l, parserS_conf_scheduler = w @ [parser_bottom P]\<rparr>)")
  apply(rename_tac d i e l wa w wxy)(*strict*)
  apply(thin_tac "d i = Some (pair e \<lparr>parserS_conf_stack = wa @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])], parserS_conf_scheduler = [parser_bottom P]\<rparr>)")
  apply(rename_tac d i e l wa w wxy)(*strict*)
  apply(thin_tac "parserS.derivation P d")
  apply(thin_tac "parserS.belongs P d")
  apply(thin_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<in> parser_marking P")
  apply(thin_tac "parser_bottom P \<in> parser_events P")
  apply(subgoal_tac "set w \<subseteq> cfg_events G'")
   apply(rename_tac d i e l wa w wxy)(*strict*)
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(rename_tac d i e l wa w wxy)(*strict*)
  apply(thin_tac "set w \<subseteq> parser_events P")
  apply(thin_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<in> parser_nonterms P")
  apply(rename_tac d i e l wa w wxy)(*strict*)
  apply(clarsimp)
  apply(rename_tac d l wa w wb)(*strict*)
  apply(subgoal_tac "set w \<subseteq> cfg_events G")
   apply(rename_tac d l wa w wb)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac d l wa w wb x)(*strict*)
   apply(subgoal_tac "parser_bottom P = Do")
    apply(rename_tac d l wa w wb x)(*strict*)
    prefer 2
    apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(rename_tac d l wa w wb x)(*strict*)
   apply(clarsimp)
   apply(case_tac "x=parser_bottom P")
    apply(rename_tac d l wa w wb x)(*strict*)
    apply(clarsimp)
   apply(rename_tac d l wa w wb x)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac d l wa w wb)(*strict*)
  apply(thin_tac "set w \<subseteq> cfg_events G'")
  apply(thin_tac "parser_bottom P \<notin> set w")
  apply(subgoal_tac "wb=[teB Do, teA (cfg_initial G)]")
   apply(rename_tac d l wa w wb)(*strict*)
   apply(force)
  apply(rename_tac d l wa w wb)(*strict*)
  apply(subgoal_tac "length wb = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) wb)")
   apply(rename_tac d l wa w wb)(*strict*)
   prefer 2
   apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac d l wa w wb)(*strict*)
        apply(force)
       apply(rename_tac d l wa w wb)(*strict*)
       apply(force)
      apply(rename_tac d l wa w wb)(*strict*)
      apply(force)
     apply(rename_tac d l wa w wb)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac d l wa w wb)(*strict*)
    apply(force)
   apply(rename_tac d l wa w wb)(*strict*)
   apply(force)
  apply(rename_tac d l wa w wb)(*strict*)
  apply(subgoal_tac "Suc (length wa) = length wb")
   apply(rename_tac d l wa w wb)(*strict*)
   prefer 2
   apply(rule_tac
      t="length wb"
      and s="length (F_DFA_GOTO_SEQUENCE M (epda_initial M) wb)"
      in ssubst)
    apply(rename_tac d l wa w wb)(*strict*)
    apply(force)
   apply(rename_tac d l wa w wb)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) wb"
      and s="wa @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])]"
      in ssubst)
    apply(rename_tac d l wa w wb)(*strict*)
    apply(force)
   apply(rename_tac d l wa w wb)(*strict*)
   apply(rule length_Suc)
  apply(rename_tac d l wa w wb)(*strict*)
  apply(case_tac wb)
   apply(rename_tac d l wa w wb)(*strict*)
   apply(clarsimp)
  apply(rename_tac d l wa w wb a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. wb = w' @ [x']")
   apply(rename_tac d l wa w wb a list)(*strict*)
   prefer 2
   apply(rule_tac
      n="length list"
      in NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac d l wa w wb a list)(*strict*)
  apply(thin_tac "wb=a#list")
  apply(clarsimp)
  apply(rename_tac d l wa w w' x')(*strict*)
  apply(subgoal_tac "wa @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])] = butlast (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w' @ [x'])) @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w' @ [x']))] ")
   apply(rename_tac d l wa w w' x')(*strict*)
   prefer 2
   apply(rule_tac
      t="butlast (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w' @ [x'])) @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w' @ [x']))]"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (w' @ [x'])"
      in ssubst)
    apply(rename_tac d l wa w w' x')(*strict*)
    apply(rule List.append_butlast_last_id)
    apply(force)
   apply(rename_tac d l wa w w' x')(*strict*)
   apply(force)
  apply(rename_tac d l wa w w' x')(*strict*)
  apply(thin_tac "wa @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])] = F_DFA_GOTO_SEQUENCE M (epda_initial M) (w' @ [x'])")
  apply(rename_tac d l wa w w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac d l w w' x')(*strict*)
  apply(subgoal_tac "\<lparr>cfg_item_lhs=S',cfg_item_rhs1=[teB Do, teA (cfg_initial G)],cfg_item_rhs2=[teB Do],cfg_item_look_ahead=[]\<rparr> \<in> valid_item_set G' k (w'@[x'])")
   apply(rename_tac d l w w' x')(*strict*)
   apply(simp add: valid_item_set_def valid_item_set_n_def)
   apply(clarsimp)
   apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
   apply(subgoal_tac "da (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G',prod_rhs=[teB Do,teA (cfg_initial G),teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do,teA (cfg_initial G),teB Do]\<rparr>)")
    apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(force)
     apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
   apply(subgoal_tac "\<exists>e w. da (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w\<rparr>)")
    apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      and m="Suc 0"
      and n="n"
      in terminal_at_beginning_are_never_modified)
        apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
        apply(rule cfgRM_derivations_are_cfg_derivations)
        apply(force)
       apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac d l w n da \<delta> e1 e2 z)(*strict*)
   apply(erule exE)+
   apply(rename_tac d l w n da \<delta> e1 e2 z e wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
   apply(subgoal_tac "\<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> da (Suc n) = Some (pair e \<lparr>cfg_conf=teB Do#w@[teB Do]\<rparr>)")
    apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
    prefer 2
    apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__on_old_grammar_basically)
            apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
         apply(force)
        apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
     apply(force)
    apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
    apply(force)
   apply(rename_tac d l w n da \<delta> e1 e2 z wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac d l w n da \<delta> e1 e2 z wb)(*strict*)
   apply(case_tac \<delta>)
    apply(rename_tac d l w n da \<delta> e1 e2 z wb)(*strict*)
    apply(clarsimp)
   apply(rename_tac d l w n da \<delta> e1 e2 z wb a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d l w n da e1 e2 z wb list)(*strict*)
   apply(case_tac z)
    apply(rename_tac d l w n da e1 e2 z wb list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d l w n da e1 e2 z wb list a lista)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. z = w' @ [x']")
    apply(rename_tac d l w n da e1 e2 z wb list a lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac d l w n da e1 e2 z wb list a lista)(*strict*)
   apply(thin_tac "z=a#lista")
   apply(clarsimp)
  apply(rename_tac d l w w' x')(*strict*)
  apply(rule_tac
      t="valid_item_set G' k (w' @ [x'])"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w' @ [x']))"
      in ssubst)
   apply(rename_tac d l w w' x')(*strict*)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(rename_tac d l w w' x')(*strict*)
          apply(force)
         apply(simp add: AF_LR_PARSER_input_def)
         apply(force)
        apply(rename_tac d l w w' x')(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac d l w w' x')(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac d l w w' x')(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac d l w w' x')(*strict*)
     apply(rule setA_app)
      apply(rename_tac d l w w' x')(*strict*)
      apply(rule two_elements_construct_domain_setA)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def)
     apply(rename_tac d l w w' x')(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def)
    apply(rename_tac d l w w' x')(*strict*)
    apply(rule setB_app)
     apply(rename_tac d l w w' x')(*strict*)
     apply(rule two_elements_construct_domain_setB)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def)
    apply(rename_tac d l w w' x')(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def F_CFG_AUGMENT_def)
   apply(rename_tac d l w w' x')(*strict*)
   apply(force)
  apply(rename_tac d l w w' x')(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w' @ [x']))"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
   apply(rename_tac d l w w' x')(*strict*)
   apply(force)
  apply(rename_tac d l w w' x')(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
   apply(rename_tac d l w w' x')(*strict*)
   apply(rule last_F_DFA_GOTO_SEQUENCE_Cons)
        apply(rename_tac d l w w' x')(*strict*)
        apply(force)
       apply(rename_tac d l w w' x')(*strict*)
       apply(force)
      apply(rename_tac d l w w' x')(*strict*)
      apply(force)
     apply(rename_tac d l w w' x')(*strict*)
     apply(force)
    apply(rename_tac d l w w' x')(*strict*)
    apply(force)
   apply(rename_tac d l w w' x')(*strict*)
   apply(force)
  apply(rename_tac d l w w' x')(*strict*)
  apply(rule_tac
      A="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      in set_mp)
   apply(rename_tac d l w w' x')(*strict*)
   apply(force)
  apply(rename_tac d l w w' x')(*strict*)
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) - {I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}"
      and s="{\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>}"
      in ssubst)
   apply(rename_tac d l w w' x')(*strict*)
   apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_2)
             apply(rename_tac d l w w' x')(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(simp add: AF_LR_PARSER_input_def)
            apply(force)
           apply(rename_tac d l w w' x')(*strict*)
           apply(force)
          apply(rename_tac d l w w' x')(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac d l w w' x')(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac d l w w' x')(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac d l w w' x')(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac d l w w' x')(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac d l w w' x')(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac d l w w' x')(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac d l w w' x')(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rename_tac d l w w' x')(*strict*)
  apply(force)
  done

definition Lemma6__31_input :: "
  'a list
  \<Rightarrow> 'a list
  \<Rightarrow> bool"
  where
    "Lemma6__31_input w v \<equiv>
  \<exists>a. w @ [a] = v"

lemma Lemma6__31_hlp: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> viable_prefix G' \<gamma>
  \<Longrightarrow> set y \<subseteq> cfg_events G
  \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))
  \<Longrightarrow> take (k - Suc 0) (y @ [Do]) \<in> cfgSTD_first G' (k - Suc 0) (\<beta> @ liftB z)
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> x \<in> cfg_events G
  \<Longrightarrow> set xs \<subseteq> cfg_events G
  \<Longrightarrow> \<alpha> \<noteq> []
  \<Longrightarrow> \<alpha> = \<alpha>' @ [teB x]
  \<Longrightarrow> length \<pi>' = length xs
  \<Longrightarrow> tau (parser_marker P) \<pi>' = []
  \<Longrightarrow> parserS.derivation P dP
  \<Longrightarrow> maximum_of_domain dP (length xs)
  \<Longrightarrow> dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ [valid_item_set G' k \<gamma>], parserS_conf_scheduler = xs @ (x # y) @ [Do]\<rparr>)
  \<Longrightarrow> get_labels dP (length xs) = \<pi>'
  \<Longrightarrow> dP (length xs) = Some (pair e \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs), parserS_conf_scheduler = (x # y) @ [Do]\<rparr>)
  \<Longrightarrow> Lemma6__31_input \<Phi> \<gamma>
  \<Longrightarrow> \<exists>\<pi>'. length \<pi>' = Suc (length xs) \<and> tau (parser_marker P) \<pi>' = [] \<and> (\<exists>dP. parserS.derivation P dP \<and> maximum_of_domain dP (Suc (length xs)) \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ [valid_item_set G' k \<gamma>], parserS_conf_scheduler = xs @ x # y @ [Do]\<rparr>) \<and> (\<exists>e. dP (Suc (length xs)) = Some (pair e \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB (xs @ [x])), parserS_conf_scheduler = y @ [Do]\<rparr>)) \<and> get_labels dP (Suc (length xs)) = \<pi>')"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(rule_tac
      x="\<pi>' @ [Some \<lparr> rule_lpop=[valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop=x#(take (k - 1) y @ take ((k - 1) - length y) [Do]), rule_lpush=[valid_item_set G' k (\<gamma> @ liftB xs),valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush=take (k - 1) y @ take ((k - 1) - length y) [Do]\<rparr>]"
      in exI)
  apply(subgoal_tac "\<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - Suc 0) y @ take (k - Suc (length y)) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - Suc 0) y @ take (k - Suc (length y)) [Do]\<rparr> \<in> parser_rules P")
   prefer 2
   apply(subgoal_tac "set ((\<gamma> @ liftB xs) @ [teB x]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    prefer 2
    apply(subgoal_tac "set ([teB x]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
     apply(subgoal_tac "setB (\<gamma> @ liftB (xs @ [x])) \<subseteq> cfg_events G' \<and> setA (\<gamma> @ liftB (xs @ [x])) \<subseteq> cfg_nonterminals G'")
      prefer 2
      apply(rule valid_item_set_nonempty_only_on_Sigma_Strings)
       apply(force)
      apply(force)
     apply(rule_tac
      t="(\<gamma> @ liftB xs) @ [teB x]"
      and s="\<gamma> @ liftB (xs @ [x])"
      in ssubst)
      apply(rule_tac
      s="liftB xs @ [teB x]"
      and t="liftB (xs @ [x])"
      in ssubst)
       apply(rule liftB_commute_one_elem_app)
      apply(force)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(simp add: two_elements_construct_domain_def)
    apply(rule disjI2)
    apply(rule inMap)
    apply(rule_tac
      x="x"
      in bexI)
     apply(force)
    apply(rule_tac
      A="cfg_events G"
      in set_mp)
     apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
     apply(force)
    apply(force)
   apply(rule_tac
      t="liftB (xs @ [x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
    apply(rule liftB_commute_one_elem_app)
   apply(rule_tac
      t="valid_item_set G' k (\<gamma> @ liftB xs @ [teB x])"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<gamma> @ liftB xs @ [teB x]))"
      in ssubst)
    apply(rule F_LR_MACHINE_all_SOUND_NotNil)
           apply(force)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(force)
      apply(rule two_elements_construct_domain_setA)
      apply(force)
     apply(rule two_elements_construct_domain_setB)
     apply(force)
    apply(force)
   apply(rule_tac
      t="valid_item_set G' k (\<gamma> @ liftB xs)"
      and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<gamma> @ liftB xs))"
      in ssubst)
    apply(rule F_LR_MACHINE_all_SOUND_prime)
          apply(force)
         apply(simp add: AF_LR_PARSER_input_def)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(force)
      apply(force)
     apply(rule two_elements_construct_domain_setA)
     apply(force)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<gamma> @ liftB xs @ [teB x]))"
      and s="F_DFA_GOTO M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<gamma> @ liftB xs))) (teB x)"
      in ssubst)
    apply(rule_tac
      t="(\<gamma> @ liftB xs @ [teB x])"
      and s="((\<gamma> @ liftB xs) @ [teB x])"
      in ssubst)
     apply(force)
    apply(rule F_DFA_GOTO_SEQUENCE_dropTerminal_last)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(subgoal_tac "\<exists>w'. (\<gamma> @ liftB (xs @ [x]))=(teB Do)#w'")
    prefer 2
    apply(rule_tac
      I="\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>' @ [teB x], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr>"
      and G="G"
      in F_CFG_AUGMENT__dollar_first)
      apply(simp add: F_CFG_AUGMENT__input_def)
      apply(simp only: AF_LR_PARSER_input_def)
     apply(simp only: AF_LR_PARSER_input_def)
    apply(force)
   apply(erule exE)+
   apply(rename_tac w')(*strict*)
   apply(case_tac w')
    apply(rename_tac w')(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac w')(*strict*)
     apply(force)
    apply(rename_tac w')(*strict*)
    apply(clarsimp)
    apply(case_tac \<gamma>)
     apply(clarsimp)
     apply(case_tac xs)
      apply(clarsimp)
      apply(subgoal_tac "Do \<notin> cfg_events G")
       apply(force)
      apply(rule_tac
      s="F_FRESH (cfg_events G)"
      and t="Do"
      in ssubst)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rule F_FRESH_is_fresh)
      apply(simp add: AF_LR_PARSER_input_def valid_cfg_def)
     apply(rename_tac a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac list)(*strict*)
     apply(subgoal_tac "length (liftB (list@[x])) = length (list@[x])")
      apply(rename_tac list)(*strict*)
      apply(subgoal_tac "length [] = length (list@[x])")
       apply(rename_tac list)(*strict*)
       apply(force)
      apply(rename_tac list)(*strict*)
      apply(rule_tac
      t="[]"
      and s="liftB (list @ [x])"
      in ssubst)
       apply(rename_tac list)(*strict*)
       apply(rule sym)
       apply(force)
      apply(rename_tac list)(*strict*)
      apply(blast)
     apply(rename_tac list)(*strict*)
     apply(rule sym)
     apply(rule liftB_reflects_length)
    apply(rename_tac a list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "length (liftB (xs@[x])) = length (xs@[x])")
     apply(subgoal_tac "length [] = length (xs@[x])")
      apply(force)
     apply(rule_tac
      t="[]"
      and s="liftB (xs @ [x])"
      in ssubst)
      apply(rule sym)
      apply(force)
     apply(blast)
    apply(rule sym)
    apply(rule liftB_reflects_length)
   apply(rename_tac w' a list)(*strict*)
   apply(subgoal_tac "w'\<noteq>[]")
    apply(rename_tac w' a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w' a list)(*strict*)
   apply(thin_tac "w'=a#list")
   apply(subgoal_tac "\<exists>\<gamma>'. \<gamma>=teB Do#\<gamma>'")
    apply(rename_tac w' a list)(*strict*)
    prefer 2
    apply(subgoal_tac "length (liftB (xs@[x])) = length (xs@[x])")
     apply(rename_tac w' a list)(*strict*)
     prefer 2
     apply(rule sym)
     apply(rule liftB_reflects_length)
    apply(rename_tac w' a list)(*strict*)
    apply(case_tac "\<gamma>")
     apply(rename_tac w' a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac w')(*strict*)
     apply(case_tac xs)
      apply(rename_tac w')(*strict*)
      apply(clarsimp)
     apply(rename_tac w' a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac list)(*strict*)
     apply(subgoal_tac "Do \<notin> cfg_events G")
      apply(rename_tac list)(*strict*)
      apply(force)
     apply(rename_tac list)(*strict*)
     apply(rule_tac
      s="F_FRESH (cfg_events G)"
      and t="Do"
      in ssubst)
      apply(rename_tac list)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac list)(*strict*)
     apply(rule F_FRESH_is_fresh)
     apply(simp add: AF_LR_PARSER_input_def valid_cfg_def)
    apply(rename_tac w' a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' a list)(*strict*)
   apply(rule_tac
      \<delta>="drop (Suc 0) (\<gamma>@liftB xs)"
      and G="G"
      and A="A"
      and \<alpha>="\<alpha>'"
      and \<beta>="\<beta>"
      and z="z"
      in X6_3_InformationOnRules_shift1)
             apply(rename_tac w' a list)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(simp add: AF_LR_PARSER_input_def)
            apply(force)
           apply(rename_tac w' a list)(*strict*)
           apply(force)
          apply(rename_tac w' a list)(*strict*)
          apply(force)
         apply(rename_tac w' a list)(*strict*)
         apply(force)
        apply(rename_tac w' a list)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac w' a list)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w' a list)(*strict*)
      apply(rule_tac
      t="F_FRESH (cfg_events G)"
      and s="Do"
      in ssubst)
       apply(rename_tac w' a list)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w' a list)(*strict*)
      apply(rule_tac
      t="F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) Do"
      and s="G'"
      in ssubst)
       apply(rename_tac w' a list)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac w' a list)(*strict*)
      apply(erule exE)+
      apply(rename_tac w' a list \<gamma>')(*strict*)
      apply(rule_tac
      t="(teB Do # drop (Suc 0) (\<gamma> @ liftB xs))"
      and s="\<gamma>@liftB xs"
      in ssubst)
       apply(rename_tac w' a list \<gamma>')(*strict*)
       apply(rule first_drop)
       apply(force)
      apply(rename_tac w' a list \<gamma>')(*strict*)
      apply(rule_tac
      t=" teB x # \<beta>"
      and s="[teB x]@\<beta>"
      in ssubst)
       apply(rename_tac w' a list \<gamma>')(*strict*)
       apply(force)
      apply(rename_tac w' a list \<gamma>')(*strict*)
      apply(rule valid_item_set_shift_symbol_back)
      apply(rule_tac
      t="\<alpha>' @ [teB x]"
      and s="\<alpha>"
      in ssubst)
       apply(rename_tac w' a list \<gamma>')(*strict*)
       apply(force)
      apply(rename_tac w' a list \<gamma>')(*strict*)
      apply(rule_tac
      t="(\<gamma> @ liftB xs) @ [teB x]"
      and s="\<gamma> @ liftB (xs @ [x])"
      in subst)
       apply(rename_tac w' a list \<gamma>')(*strict*)
       apply(simp (no_asm_use))
       apply(rename_tac w' \<gamma>')(*strict*)
       apply(rule liftB_commute_one_elem_app)
      apply(rename_tac w' a list \<gamma>')(*strict*)
      apply(force)
     apply(rename_tac w' a list)(*strict*)
     apply(subgoal_tac "item_core \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>' @ [teB x], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> cfg_productions G")
      apply(rename_tac w' a list)(*strict*)
      prefer 2
      apply(rule F_CFG_AUGMENT__ItemInvalid)
             apply(rename_tac w' a list)(*strict*)
             apply(simp add: AF_LR_PARSER_input_def)
            apply(rename_tac w' a list)(*strict*)
            apply(force)
           apply(rename_tac w' a list)(*strict*)
           apply(force)
          apply(rename_tac w' a list)(*strict*)
          apply(force)
         apply(rename_tac w' a list)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac w' a list)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac w' a list)(*strict*)
       apply(force)
      apply(rename_tac w' a list)(*strict*)
      apply(force)
     apply(rename_tac w' a list)(*strict*)
     apply(simp add: item_core_def)
    apply(rename_tac w' a list)(*strict*)
    apply(rule_tac
      t="(F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))"
      and s="G'"
      in ssubst)
     apply(rename_tac w' a list)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac w' a list)(*strict*)
    apply(rule_tac
      t="take (k - Suc 0) y @ take (k - Suc (length y)) [Do]"
      and s="take (k - Suc 0) (y@[Do])"
      in ssubst)
     apply(rename_tac w' a list)(*strict*)
     apply(force)
    apply(rename_tac w' a list)(*strict*)
    apply(rule_tac
      t="1"
      and s="Suc 0"
      in ssubst)
     apply(rename_tac w' a list)(*strict*)
     apply(force)
    apply(rename_tac w' a list)(*strict*)
    apply(force)
   apply(rename_tac w' a list)(*strict*)
   apply(erule exE)+
   apply(rename_tac w' a list \<gamma>')(*strict*)
   apply(rule_tac
      t="(teB (F_FRESH (cfg_events G)) # drop (Suc 0) (\<gamma> @ liftB xs))"
      and s="\<gamma>@liftB xs"
      in ssubst)
    apply(rename_tac w' a list \<gamma>')(*strict*)
    apply(rule first_drop)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac w' a list \<gamma>')(*strict*)
   apply(subgoal_tac "length (\<gamma> @ liftB xs) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<gamma> @ liftB xs))")
    apply(rename_tac w' a list \<gamma>')(*strict*)
    prefer 2
    apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac w' a list \<gamma>')(*strict*)
         apply(force)
        apply(rename_tac w' a list \<gamma>')(*strict*)
        apply(force)
       apply(rename_tac w' a list \<gamma>')(*strict*)
       apply(force)
      apply(rename_tac w' a list \<gamma>')(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac w' a list \<gamma>')(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac w' a list \<gamma>')(*strict*)
    apply(force)
   apply(rename_tac w' a list \<gamma>')(*strict*)
   apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rule_tac
      t="tau (parser_marker P) (get_labels dP (length xs) @ [Some \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - (Suc 0)) y @ take (k - Suc (length y)) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - (Suc 0)) y @ take (k - Suc (length y)) [Do]\<rparr>])"
      and s="tau (parser_marker P) (get_labels dP (length xs)) @ (tau (parser_marker P) [Some \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - (Suc 0)) y @ take (k - Suc (length y)) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - (Suc 0)) y @ take (k - Suc (length y)) [Do]\<rparr>])"
      in ssubst)
    apply(rule tau_append_commutes)
   apply(clarsimp)
   apply(subgoal_tac "parser_marker P \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - Suc 0) y @ take (k - Suc (length y)) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - Suc 0) y @ take (k - Suc (length y)) [Do]\<rparr> = Some None")
    apply(clarsimp)
   apply(subgoal_tac "parser_marker P \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - Suc 0) y @ take (k - Suc (length y)) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - Suc 0) y @ take (k - Suc (length y)) [Do]\<rparr> \<noteq> None")
    prefer 2
    apply(rule_tac
      G="G"
      in X6_3_InformationOnRules_EffectNotNone)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(force)
   apply(case_tac "parser_marker P \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - Suc 0) y @ take (k - Suc (length y)) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - Suc 0) y @ take (k - Suc (length y)) [Do]\<rparr>")
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(case_tac a)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a aa)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac a aa)(*strict*)
    apply(force)
   apply(rename_tac a aa)(*strict*)
   apply(case_tac aa)
   apply(rename_tac a aa prod_lhs prod_rhs)(*strict*)
   apply(rename_tac A' XSEQ')
   apply(rename_tac a aa A' XSEQ')(*strict*)
   apply(subgoal_tac "x # take (k - Suc 0) y @ take (k - Suc (length y)) [Do]=take (k - Suc 0) y @ take (k - Suc (length y)) [Do] \<and> \<lparr>prod_lhs=A',prod_rhs=XSEQ'\<rparr> \<in> (cfg_productions G) \<and> (\<exists>q\<delta>. [valid_item_set G' k (\<gamma> @ liftB xs)]=q\<delta>#F_DFA_GOTO_SEQUENCE M q\<delta> XSEQ' \<and> [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))]=q\<delta>#(F_DFA_GOTO_SEQUENCE M q\<delta> [teA A']) \<and> (\<exists>\<delta>. \<lparr>cfg_item_lhs = A',cfg_item_rhs1 = XSEQ',cfg_item_rhs2 = [],cfg_item_look_ahead = x # take (k - Suc 0) y @ take (k - Suc (length y)) [Do]\<rparr> \<in> valid_item_set G' k (teB Do#\<delta>@XSEQ') \<and> q\<delta>=last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#\<delta>))))")
    apply(rename_tac a aa A' XSEQ')(*strict*)
    apply(force)
   apply(rename_tac a aa A' XSEQ')(*strict*)
   apply(rule X6_3_InformationOnRules_reduce2)
            apply(rename_tac a aa A' XSEQ')(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(simp add: AF_LR_PARSER_input_def)
           apply(force)
          apply(rename_tac a aa A' XSEQ')(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac a aa A' XSEQ')(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac a aa A' XSEQ')(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac a aa A' XSEQ')(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac a aa A' XSEQ')(*strict*)
      apply(force)
     apply(rename_tac a aa A' XSEQ')(*strict*)
     apply(force)
    apply(rename_tac a aa A' XSEQ')(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac a aa A' XSEQ')(*strict*)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(subgoal_tac "set ((\<gamma> @ liftB (xs @ [x]))) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   prefer 2
   apply(subgoal_tac "setB (\<gamma> @ liftB (xs @ [x])) \<subseteq> cfg_events G' \<and> setA (\<gamma> @ liftB (xs @ [x])) \<subseteq> cfg_nonterminals G'")
    prefer 2
    apply(rule valid_item_set_nonempty_only_on_Sigma_Strings)
     apply(force)
    apply(force)
   apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
    apply(force)
   apply(force)
  apply(rule_tac
      x = "derivation_append dP (der2 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs), parserS_conf_scheduler = x#y@[Do]\<rparr> \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - 1) y @ take (k - 1 - length y) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - 1) y @ take (k - 1 - length y) [Do]\<rparr> \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB (xs @ [x])), parserS_conf_scheduler = y@[Do]\<rparr>) (length xs)"
      in exI)
  apply(rule context_conjI)
   apply(rule parserS.derivation_concat2)
      apply(force)
     apply(force)
    apply(rule parserS.der2_is_derivation)
    apply(simp add: parserS_step_relation_def)
    apply(rule conjI)
     prefer 2
     apply(case_tac k)
      apply(clarsimp)
     apply(rename_tac nat)(*strict*)
     apply(clarsimp)
     apply(case_tac "nat-length y")
      apply(rename_tac nat)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      x="drop nat y @ [Do]"
      in exI)
      apply(clarsimp)
     apply(rename_tac nat nata)(*strict*)
     apply(clarsimp)
    apply(rule_tac
      x="butlast (F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs))"
      in exI)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs)"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ (valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs))"
      in ssubst)
     apply(force)
    apply(rule_tac
      t="valid_item_set G' k (\<gamma> @ liftB xs)"
      and s="last (epda_initial SSM # F_DFA_GOTO_SEQUENCE SSM (epda_initial SSM) SSw)" for SSM SSw
      in ssubst)
     apply(rule F_LR_MACHINE_all_SOUND_prime)
           apply(force)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rule two_elements_construct_domain_setA)
      apply(rule_tac
      B="set (\<gamma> @ liftB (xs @ [x]))"
      in subset_trans)
       apply(rule_tac
      t="liftB (xs @ [x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
        apply(rule liftB_commute_one_elem_app)
       apply(force)
      apply(force)
     apply(rule two_elements_construct_domain_setB)
     apply(rule_tac
      B="set (\<gamma> @ liftB (xs @ [x]))"
      in subset_trans)
      apply(rule_tac
      t="liftB (xs @ [x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
       apply(rule liftB_commute_one_elem_app)
      apply(force)
     apply(force)
    apply(rule_tac
      t="valid_item_set G' k \<gamma>"
      and s="last (epda_initial SSM # F_DFA_GOTO_SEQUENCE SSM (epda_initial SSM) SSw)" for SSM SSw
      in ssubst)
     apply(rule F_LR_MACHINE_all_SOUND_prime)
           apply(force)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rule two_elements_construct_domain_setA)
      apply(force)
     apply(rule two_elements_construct_domain_setB)
     apply(force)
    apply(rule_tac
      t="valid_item_set G' k (\<gamma> @ liftB (xs@[x]))"
      and s="last (epda_initial SSM # F_DFA_GOTO_SEQUENCE SSM (epda_initial SSM) SSw)" for SSM SSw
      in ssubst)
     apply(rule F_LR_MACHINE_all_SOUND_prime)
           apply(force)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rule two_elements_construct_domain_setA)
      apply(force)
     apply(rule two_elements_construct_domain_setB)
     apply(force)
    apply(rule_tac
      t="F_LR_MACHINE G' F k"
      and s="M"
      in ssubst)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rule_tac
      t="liftB (xs @ [x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
     apply(rule liftB_commute_one_elem_app)
    apply(subgoal_tac "length \<gamma> = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) \<gamma>)")
     prefer 2
     apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(force)
    apply(subgoal_tac "length (\<gamma> @ liftB xs) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<gamma> @ liftB xs))")
     prefer 2
     apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rule_tac
      s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      and t="epda_events M"
      in ssubst)
       apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
      apply(rule set_concat_subset)
       apply(force)
      apply(rule_tac
      B="set (liftB (xs @ [x]))"
      in subset_trans)
       apply(rule set_liftB_commute)
       apply(force)
      apply(force)
     apply(force)
    apply(thin_tac "dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi> @ [valid_item_set G' k \<gamma>], parserS_conf_scheduler = xs @ x # y @ [Do]\<rparr>)")
    apply(thin_tac "dP (length xs) = Some (pair e \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi> @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs), parserS_conf_scheduler = x # y @ [Do]\<rparr>)")
    apply(thin_tac "\<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - Suc 0) y @ take (k - Suc (length y)) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - Suc 0) y @ take (k - Suc (length y)) [Do]\<rparr> \<in> parser_rules P")
    apply(simp only: Lemma6__31_input_def)
    apply(erule exE)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="\<gamma>"
      and s="\<Phi>@[a]"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="(F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi> @ last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>@[a])) # F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>@[a]))) (liftB xs))"
      and s="(F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi> @ [last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>@[a]))]) @ F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>@[a]))) (liftB xs)"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi> @ last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a])) # F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a]))) (liftB xs @ [teB x])"
      and s="(F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi> @[ last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a]))])@ F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a]))) (liftB xs @ [teB x])"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi> @ [last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a]))]"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a])"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(rule F_DFA_GOTOSeq_drop_tail)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
       apply(rename_tac a)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac a)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a]) @ F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a]))) (liftB xs @ [teB x])"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a])@(liftB xs @ [teB x]))"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(rule sym)
     apply(rule F_DFA_GOTO_SEQUENCE_append_split)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
       apply(rename_tac a)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac a)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      B="set(liftB (xs @ [x]))"
      in subset_trans)
      apply(rename_tac a)(*strict*)
      apply (metis liftB_commute_one_elem_app equalityE)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a]) @ F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a]))) (liftB xs)"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a])@(liftB xs))"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(rule sym)
     apply(rule F_DFA_GOTO_SEQUENCE_append_split)
          apply(rename_tac a)(*strict*)
          apply(force)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
       apply(rename_tac a)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac a)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      B="set(liftB (xs @ [x]))"
      in subset_trans)
      apply(rename_tac a)(*strict*)
      apply (metis set_liftB_commute set_app_subset)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule conjI)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="butlast (F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs)) @ [last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs)), last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs @ [teB x]))]"
      and s="(butlast (F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs)) @ [last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs))])@[ last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs @ [teB x]))]"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="butlast (F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs)) @ [last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs))]"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs)"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a]) @ liftB xs @ [teB x])"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a] @ liftB xs) @ [teB x])"
      in ssubst)
     apply(rename_tac a)(*strict*)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a] @ liftB xs) @ [teB x])"
      and s="F_DFA_GOTO_SEQUENCE SSM (epda_initial SSM) SSw @ [last (epda_initial SSM # F_DFA_GOTO_SEQUENCE SSM (epda_initial SSM) (SSw @ [SSa]))]" for SSM SSw SSa
      in subst)
     apply(rename_tac a)(*strict*)
     apply(rule F_DFA_GOTOSeq_drop_tail)
         apply(rename_tac a)(*strict*)
         apply(force)
        apply(rename_tac a)(*strict*)
        apply(force)
       apply(rename_tac a)(*strict*)
       apply(force)
      apply(rename_tac a)(*strict*)
      apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
       apply(rename_tac a)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
      apply(rename_tac a)(*strict*)
      apply (metis ConsApp liftB_commutes_over_concat concat_asso set_append1 set_concat_subset subset_trans)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac a)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(rename_tac a)(*strict*)
     apply(rule_tac
      A="set (liftB (xs @ [x]))"
      in set_mp)
      apply(rename_tac a)(*strict*)
      apply(force)
     apply(rename_tac a)(*strict*)
     apply (metis head_in_set set_liftB_insert set_append_contra2)
    apply(rename_tac a)(*strict*)
    apply(rule_tac
      t=" [last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a] @ liftB xs) @ [teB x]))]"
      and s="[last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi> @ [a] @ liftB xs) @ [last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) ((\<Phi> @ [a] @ liftB xs) @ [teB x]))])]"
      in ssubst)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
   apply(simp add: der2_def)
  apply(rule conjI)
   apply(rule_tac
      t="Suc (length xs)"
      and s="length xs + (Suc 0)"
      in ssubst)
    apply(force)
   apply(rule_tac concat_has_max_dom)
    apply(force)
   apply(rule der2_maximum_of_domain)
  apply(rule conjI)
   apply(simp add: derivation_append_def)
  apply(rule conjI)
   apply(rule_tac
      x="(Some \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - 1) y @ take (k - 1 - length y) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - 1) y @ take (k - 1 - length y) [Do]\<rparr>)"
      in exI)
   apply(simp add: derivation_append_def)
   apply(simp add: der2_def)
  apply(rule_tac
      t="Suc (length xs)"
      and s="length xs + (Suc 0)"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="get_labels (derivation_append dP (der2 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs), parserS_conf_scheduler = x # y @ [Do]\<rparr> \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - 1) y @ take (k - 1 - length y) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - 1) y @ take (k - 1 - length y) [Do]\<rparr> \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB (xs @ [x])), parserS_conf_scheduler = y @ [Do]\<rparr>) (length xs)) (length xs + Suc 0)"
      and s="get_labels dP (length xs) @ get_labels ((der2 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs), parserS_conf_scheduler = x # y @ [Do]\<rparr> \<lparr>rule_lpop = [valid_item_set G' k (\<gamma> @ liftB xs)], rule_rpop = x # take (k - 1) y @ take (k - 1 - length y) [Do], rule_lpush = [valid_item_set G' k (\<gamma> @ liftB xs), valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))], rule_rpush = take (k - 1) y @ take (k - 1 - length y) [Do]\<rparr> \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB (xs @ [x])), parserS_conf_scheduler = y @ [Do]\<rparr>)) (Suc 0)"
      in ssubst)
   apply(rule derivation_concat_get_labels)
    apply(force)
   apply(force)
  apply(simp add: get_labels_def)
  apply(rule_tac
      t="nat_seq (Suc 0) (Suc 0)"
      and s="[Suc 0]"
      in ssubst)
   apply(rule natUptTo_n_n)
  apply(clarsimp)
  apply(simp add: get_label_def der2_def)
  done

theorem Lemma6__31: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> viable_prefix G' \<gamma>
  \<Longrightarrow> valid_item G' k
          \<lparr>cfg_item_lhs = A,
            cfg_item_rhs1 = \<alpha>,
            cfg_item_rhs2 = \<beta>,
            cfg_item_look_ahead = z\<rparr>
  \<Longrightarrow> set y \<subseteq> cfg_events G
  \<Longrightarrow> set a \<subseteq> cfg_events G
  \<Longrightarrow> \<lparr>cfg_item_lhs = A,
        cfg_item_rhs1 = \<alpha>,
        cfg_item_rhs2 = \<beta>,
        cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB a)
  \<Longrightarrow> take k (y @ [Do]) \<in> cfgSTD_first G' k (\<beta> @ liftB z)
  \<Longrightarrow> Lemma6__31_input \<Phi> \<gamma>
  \<Longrightarrow> \<exists>\<pi>' dP e.
        length \<pi>' = length a
        \<and> length (tau (parser_marker P) \<pi>') = 0
        \<and> parserS.derivation P dP
        \<and> maximum_of_domain dP (length a)
        \<and> dP 0
            = Some (pair None
                \<lparr>parserS_conf_stack =
                    F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi>
                    @ [valid_item_set G' k \<gamma>],
                parserS_conf_scheduler = a @ y @ [Do]\<rparr>)
        \<and> dP (length a)
            = Some (pair e
                \<lparr>parserS_conf_stack =
                    F_DFA_GOTO_SEQUENCE M (epda_initial M) \<Phi>
                    @ [valid_item_set G' k \<gamma>]
                    @ F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB a),
                parserS_conf_scheduler = y @ [Do]\<rparr>)
        \<and> get_labels dP (length a) = \<pi>'"
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
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
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
  apply(induct a arbitrary: A \<alpha> \<beta> z y rule: rev_induct)
   apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x = "der1 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ [valid_item_set G' k \<gamma>], parserS_conf_scheduler = y@[Do]\<rparr>"
      in exI)
   apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
   apply(rule conjI)
    apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
    apply(rule parserS.der1_is_derivation)
   apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
   apply(rule conjI)
    apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
   apply(simp add: der1_def)
   apply(simp add: get_labels_def)
   apply(rule conjI)
    apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
    apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) [])")
     apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
     prefer 2
     apply(rule F_DFA_GOTO_SEQUENCESound_main1)
          apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
          apply(force)
         apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
         apply(force)
        apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
        apply(force)
       apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
      apply(rule LRM_contains_theEqClasses2)
         apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
      apply(rule viable_prefix_in_CFG)
       apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
       apply(force)
      apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
      apply(force)
     apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
     apply(force)
    apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> \<beta> z y)(*strict*)
   apply(rule nat_seqEmpty)
   apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
  apply(clarsimp)
  apply(case_tac "\<alpha>\<noteq>[]")
   apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
   apply(subgoal_tac "\<exists>\<alpha>'. \<alpha>=\<alpha>'@[teB x]")
    apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
    prefer 2
    apply(subgoal_tac "\<exists>n. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set_n G' k n (\<gamma> @ liftB (xs@[x]))")
     apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
     prefer 2
     apply(simp add: valid_item_set_def)
    apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs A \<alpha> \<beta> z y n)(*strict*)
    apply(simp add: valid_item_set_n_def)
    apply(clarsimp)
    apply(rename_tac x xs A \<alpha> \<beta> z y n d \<delta> e1 e2 za)(*strict*)
    apply(rule last_elem_liftB_eq)
     apply(rename_tac x xs A \<alpha> \<beta> z y n d \<delta> e1 e2 za)(*strict*)
     apply(force)
    apply(rename_tac x xs A \<alpha> \<beta> z y n d \<delta> e1 e2 za)(*strict*)
    apply(force)
   apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
   apply(erule exE)+
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
   prefer 2
   apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
   apply(subgoal_tac "\<alpha>=[]")
    apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xs A \<alpha> \<beta> z y)(*strict*)
   apply(thin_tac "\<not> \<alpha> \<noteq> []")
   apply(clarsimp)
   apply(rename_tac x xs A \<beta> z y)(*strict*)
   apply(subgoal_tac "set(\<gamma> @ liftB (xs @ [x])) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(rename_tac x xs A \<beta> z y)(*strict*)
    prefer 2
    apply(rule viable_prefix_in_CFG)
     apply(rename_tac x xs A \<beta> z y)(*strict*)
     apply(force)
    apply(rename_tac x xs A \<beta> z y)(*strict*)
    apply(rule Fact6_12__1)
    apply(force)
   apply(rename_tac x xs A \<beta> z y)(*strict*)
   apply(subgoal_tac "\<exists>n. \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = [], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set_n G' k n (\<gamma> @ liftB (xs @ [x]))")
    apply(rename_tac x xs A \<beta> z y)(*strict*)
    prefer 2
    apply(simp add: valid_item_set_def)
   apply(rename_tac x xs A \<beta> z y)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs A \<beta> z y n)(*strict*)
   apply(case_tac n)
    apply(rename_tac x xs A \<beta> z y n)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs A \<beta> z y)(*strict*)
    apply(simp add: valid_item_set_n_def)
    apply(clarsimp)
    apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
    apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=(cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))),prod_rhs=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>) \<lparr>cfg_conf=[teB (F_FRESH (cfg_events G)),teA (cfg_initial G),teB (F_FRESH (cfg_events G))]\<rparr>)")
     apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
     prefer 2
     apply(rule_tac
      n="0"
      in F_CFG_AUGMENT__FirstStep)
            apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
            apply(simp add: AF_LR_PARSER_input_def)
           apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
    apply(case_tac \<gamma>)
     apply(rename_tac x xs A \<beta> z y d e2 za)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs A \<beta> z y d za)(*strict*)
     apply(case_tac za)
      apply(rename_tac x xs A \<beta> z y d za)(*strict*)
      apply(clarsimp)
      apply(rename_tac x xs z y d)(*strict*)
      apply(subgoal_tac "liftB (xs@[x])\<noteq>[]")
       apply(rename_tac x xs z y d)(*strict*)
       apply(force)
      apply(rename_tac x xs z y d)(*strict*)
      apply(rule_tac
      t="liftB (xs@[x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
       apply(rename_tac x xs z y d)(*strict*)
       apply(rule liftB_commute_one_elem_app)
      apply(rename_tac x xs z y d)(*strict*)
      apply(blast)
     apply(rename_tac x xs A \<beta> z y d za a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac x xs A \<beta> z y d e2 za a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xs A \<beta> z y n nat)(*strict*)
   apply(rename_tac x xs B w z y n nat)
   apply(rename_tac x xs B w z y n nat)(*strict*)
   apply(simp add: valid_item_set_n_def)
   apply(clarsimp)
   apply(rename_tac x xs B w z y nat d e1 e2 za)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (Suc nat) = Some (pair (Some e) c)")
    apply(rename_tac x xs B w z y nat d e1 e2 za)(*strict*)
    prefer 2
    apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac x xs B w z y nat d e1 e2 za)(*strict*)
      apply(blast)
     apply(rename_tac x xs B w z y nat d e1 e2 za)(*strict*)
     apply(blast)
    apply(rename_tac x xs B w z y nat d e1 e2 za)(*strict*)
    apply(arith)
   apply(rename_tac x xs B w z y nat d e1 e2 za)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
   apply(subgoal_tac "Lemma6__2_Goal G' (derivation_take d (Suc nat)) nat e (\<gamma> @ liftB (xs@[x])) [teA B] za (\<gamma> @ liftB (xs@[x])) B")
    apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
    prefer 2
    apply(rule Lemma6__2)
          apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
          apply(force)
         apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
         apply(force)
        apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
        apply(rule_tac cfgRM.derivation_take_preserves_derivation)
        apply(force)
       apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
       apply(rule_tac
      t="(Suc nat + Suc 0)"
      and s="Suc(Suc nat)"
      in ssubst)
        apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
       apply(rule_tac
      m="Suc 0"
      in cfgRM.derivation_take_preserves_generates_maximum_of_domain)
        apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
       apply(rule_tac
      t="(Suc nat + Suc 0)"
      and s="Suc(Suc nat)"
      in ssubst)
        apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
       apply(force)
      apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
      apply(simp add: derivation_take_def)
     apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
     apply(simp add: derivation_take_def)
    apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y nat d e2 za e)(*strict*)
   apply(simp add: Lemma6__2_Goal_def)
   apply(clarsimp)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
   apply(case_tac \<alpha>')
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<beta>' y' A' d'' m)(*strict*)
    apply(subgoal_tac "liftB (xs @ [x]) \<noteq> []")
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<beta>' y' A' d'' m)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<beta>' y' A' d'' m)(*strict*)
    apply(rule_tac
      t="liftB (xs @ [x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<beta>' y' A' d'' m)(*strict*)
     apply(rule liftB_commute_one_elem_app)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<beta>' y' A' d'' m)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m a list)(*strict*)
   apply(subgoal_tac "\<exists>x1 x2. \<alpha>'=x1@[x2]")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<alpha>' \<beta>' y' A' d'' m a list)(*strict*)
   apply(thin_tac "\<alpha>'=a#list")
   apply(clarsimp)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
   apply(subgoal_tac "Suc 0 \<le> length (liftB (xs @ [x]))")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    prefer 2
    apply(rule_tac
      t="liftB (xs @ [x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
     apply(rule liftB_commute_one_elem_app)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
   apply(subgoal_tac "take (Suc 0 - length (liftB (xs @ [x]))) (List.rev \<gamma>)=[]")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    prefer 2
    apply(case_tac \<gamma>)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
     apply(clarsimp)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2 a list)(*strict*)
    apply(subgoal_tac "\<exists>x1 x2. \<gamma>=x1@[x2]")
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2 a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2 a list)(*strict*)
    apply(thin_tac "\<gamma>=a#list")
    apply(clarsimp)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2 x1a x2a)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
   apply(subgoal_tac "take (Suc 0) (List.rev (liftB (xs @ [x]))) = [teB x]")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    prefer 2
    apply(rule_tac
      t="liftB (xs @ [x])"
      and s="liftB xs @ [teB x]"
      in ssubst)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
     apply(rule liftB_commute_one_elem_app)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
   apply(subgoal_tac "x2=teB x")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    prefer 2
    apply(subgoal_tac "[x2] = take (Suc 0) (List.rev (liftB (xs @ [x]))) @ []")
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    apply(thin_tac "[x2] = take (Suc 0) (List.rev (liftB (xs @ [x]))) @ take (Suc 0 - length (liftB (xs @ [x]))) (List.rev \<gamma>)")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="x2"
      and s="last(take (Suc 0) (List.rev (liftB (xs @ [x]))))"
      in ssubst)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
     apply(rule_tac
      t="take (Suc 0) (List.rev (liftB (xs @ [x])))"
      and s="[x2]"
      in ssubst)
      apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
      apply(force)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
     apply(simp (no_asm_use))
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    apply(rule_tac
      t="take (Suc 0) (List.rev (liftB (xs @ [x])))"
      and s="[teB x]"
      in ssubst)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 x2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
   apply(subgoal_tac "\<delta>'@x1=\<gamma>@liftB xs")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    prefer 2
    apply(subgoal_tac "\<delta>' @ x1 @ [teB x] = \<gamma> @ liftB xs @ [teB x]")
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     prefer 2
     apply(rule_tac
      s="liftB (xs @ [x])"
      and t="liftB xs @ [teB x]"
      in subst)
      apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
      apply(rule liftB_commute_one_elem_app)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(rule_tac
      x="teB x"
      in drop_last_both_eq)
    apply(clarsimp)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
   apply(thin_tac "\<delta>' @ x1 @ [teB x] = \<gamma> @ liftB (xs @ [x])")
   apply(thin_tac "take (Suc 0) (List.rev (liftB (xs @ [x]))) = [teB x]")
   apply(thin_tac "Suc 0 \<le> length (liftB (xs @ [x]))")
    (*
d:
  0 / / S'
  n'+m+1 / e / \<gamma>.xs.[x].B.za
  n'+m+2 / e2 / \<gamma>.xs.[x].w.za
d':
  0 / / S'
  n' / e1 / \<delta>'.A'.y'
  n'+1 / e2a / \<delta>'.x1.[x].\<beta>'.y'
d'':
  0 / / \<beta>'.y'
  m / ?e3 / B.za
k:za=z
\<delta>'.x1=\<gamma>.xs
\<lparr>B\<rightarrow>\<bullet>w,z\<rparr> \<in> valid_item_set G' k (\<gamma>.xs.x)
k:y$ \<in> cfgSTD_first G' k (w.z)

therefore we get: \<lparr>A'\<rightarrow>\<delta>'.x1\<bullet>x.\<beta>',k:y'\<rparr> \<in> valid_item_set G' k (\<gamma>.xs)
*)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
   apply(subgoal_tac " \<lparr>cfg_item_lhs = A', cfg_item_rhs1 = x1, cfg_item_rhs2 = teB x#\<beta>', cfg_item_look_ahead = take k (filterB y')\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB xs)")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    prefer 2
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(simp (no_asm) add: valid_item_set_def valid_item_set_n_def)
    apply(rule_tac
      x="n'"
      in exI)
    apply(rule_tac
      x="d'"
      in exI)
    apply(rule conjI)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(rule conjI)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(rule_tac
      x="\<delta>'"
      in exI)
    apply(rule_tac
      x="e1"
      in exI)
    apply(rule_tac
      x="Some e2a"
      in exI)
    apply(rule_tac
      x="y'"
      in exI)
    apply(rule conjI)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(rule conjI)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(rule conjI)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(rule_tac
      t="liftB (take k (filterB y'))"
      and s="take k (liftB (filterB y'))"
      in ssubst)
      apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
      apply(rule sym)
      apply(rule take_liftB)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(rule_tac
      t="liftB (filterB y')"
      and s="y'"
      in ssubst)
      apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
      apply(rule liftBDeConv2)
      apply(force)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(rule conjI)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(rule conjI)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
   apply(subgoal_tac "take (ord_class.max k 1) (x#y@[Do]) \<in> cfgSTD_first G' (ord_class.max k 1) (teB x#\<beta>'@(take k y'))")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    prefer 2
    apply(thin_tac "\<And>A \<alpha> \<beta> z y. valid_item G' k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<Longrightarrow> set y \<subseteq> cfg_events G \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB xs) \<Longrightarrow> take k y @ take (k - length y) [Do] \<in> cfgSTD_first G' k (\<beta> @ liftB z) \<Longrightarrow> \<exists>\<pi>'. length \<pi>' = length xs \<and> tau (parser_marker P) \<pi>' = [] \<and> (\<exists>dP. parserS.derivation P dP \<and> maximum_of_domain dP (length xs) \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ [valid_item_set G' k \<gamma>], parserS_conf_scheduler = xs @ y @ [Do]\<rparr>) \<and> (\<exists>e. dP (length xs) = Some (pair e \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (\<Phi>) @ valid_item_set G' k \<gamma> # F_DFA_GOTO_SEQUENCE M (valid_item_set G' k \<gamma>) (liftB xs), parserS_conf_scheduler = y @ [Do]\<rparr>)) \<and> get_labels dP (length xs) = \<pi>') ")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(rule cfgSTD_first_drop_first_terminal)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
    apply(simp add: cfgSTD_first_def del: take_append)
    apply(rule inMap)
    apply(simp del: take_append)
    apply(clarify)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
    apply(subgoal_tac "\<exists>x. x@z=xa")
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
     apply(subgoal_tac "\<exists>x. x@y'=za")
      apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
      apply(clarsimp)
      apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
      apply(rule_tac
      x="xb @ filterB xa @ (take k (filterB y'))"
      in exI)
      apply(rule conjI)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       prefer 2
       apply(rule sym)
       apply(rule_tac
      t="take (k - Suc 0) y @ take (k - Suc (length y)) [Do]"
      and s="take (k - Suc 0) (y@[Do])"
      in ssubst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(rule_tac
      n="Suc 0"
      in take_take_bi)
       apply(rule_tac
      t="take k (y @ [Do])"
      and s="take k xb @ take (k - length xb) z"
      in ssubst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(clarsimp)
       apply(rule_tac
      t="z"
      and s="filterB (take k xa @ take (k - length xa) y')"
      in ssubst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(rule_tac
      t="z"
      and s="filterB (liftB z)"
      in ssubst)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
         apply(rule sym)
         apply(rule liftBDeConv1)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(clarsimp)
        apply(force)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(rule_tac
      t="ord_class.min (k - (length xb + length (filterB xa))) k"
      and s="(k - (length xb + length (filterB xa)))"
      in ssubst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(rule_tac
      t="take k xa @ take (k - length xa) y'"
      and s="take k (xa@y')"
      in ssubst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(rule_tac
      t="k - (length xb + length (filterB xa))"
      and s="(k - length xb) - length (filterB xa)"
      in ssubst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(rule_tac
      t="take (k - length xb) (filterB xa) @ take (k - length xb - length (filterB xa)) (filterB y')"
      and s="take (k - length xb) ((filterB xa) @ (filterB y'))"
      in ssubst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(rule_tac
      t="filterB (take k (xa @ y'))"
      and s="take k (filterB (xa @ y'))"
      in ssubst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(rule filterB_take)
        apply(force)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(rule_tac
      t="filterB xa @ filterB y'"
      and s="filterB (xa @ y')"
      in subst)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(rule filterB_commutes_over_concat)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(rule sym)
       apply(rule take_take_prime)
       apply(force)
    (*
d?:
  0 / / \<beta>'@(take k y')
  n? / / xb.take k(xa@y')
d:
  0 / / S'
  n'+m+1 / e / \<gamma>.xs.[x].B.xa.y'
  n'+m+2 / e2 / \<gamma>.xs.[x].w.xa.y'
d':
  0 / / S'
  n' / e1 / \<delta>'.A'.y'
  n'+1 / e2a / \<delta>'.x1.[x].\<beta>'.y'
d'':
  0 / / \<beta>'.y'
  m / ?e3 / B.xa.y'
da:
  0 / / w.z
  n / ?e1a / xb.z
    construction:
f_1 := fst(split(da,w,z))
  0 / / w
  n' / / xb
f_2 := concat((B\<rightarrow>w),f_1)
  0 / / B
  1 / / w
  n'+1 / / xb
f_3 := append(xa,f_2)
  0 / / B.xa
  1 / / w.xa
  n'+1 / / xb.xa
f_4 := fst(split(d'',\<beta>',y'))
  0 / / \<beta>'
  m' / / B.xa
f_5 := concat(f_4,f_3)
  0 / / \<beta>'
  m' / / B.xa
  m'+1 / / w.xa
  m'+n'+1 / / xb.xa
f_6 := append(f_5,take k y')
  0 / / \<beta>'.take k y'
  m' / / B.xa.take k y'
  m'+1 / / w.xa.take k y'
  m'+n'+1 / / xb.xa.take k y'

f_6 := append(concat(fst(split(d'',\<beta>',y')),append(xa,concat((B\<rightarrow>w),fst(split(da,w,z))))),take k y')
*)
    (*f_6*)
      apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
      apply(subgoal_tac "\<exists>f6 n6 e6. cfgSTD.derivation G' f6 \<and> maximum_of_domain f6 n6 \<and> f6 0 = Some (pair None \<lparr>cfg_conf = \<beta>'@take k y'\<rparr>) \<and> f6 n6 = Some (pair e6 \<lparr>cfg_conf = liftB xb@xa@take k y'\<rparr>)")
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       prefer 2
    (*f_5*)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(subgoal_tac "\<exists>f5 n5 e5. cfgSTD.derivation G' f5 \<and> maximum_of_domain f5 n5 \<and> f5 0 = Some (pair None \<lparr>cfg_conf = \<beta>'\<rparr>) \<and> f5 n5 = Some (pair e5 \<lparr>cfg_conf = liftB xb@xa\<rparr>)")
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        prefer 2
    (*f_4*)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(subgoal_tac "\<exists>f4 n4 e4. cfgSTD.derivation G' f4 \<and> maximum_of_domain f4 n4 \<and> f4 0 = Some (pair None \<lparr>cfg_conf = \<beta>'\<rparr>) \<and> f4 n4 = Some (pair e4 \<lparr>cfg_conf = [teA B]@xa\<rparr>)")
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
         prefer 2
         apply(subgoal_tac "\<exists>d x'. cfgSTD.derivation G' d \<and> maximum_of_domain d m \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta>'\<rparr>) \<and> d m = Some (pair e3 \<lparr>cfg_conf = x'\<rparr>) \<and> x' @ liftB (filterB y') = [teA B]@xa@y'")
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
          prefer 2
          apply(rule_tac
      d="d''"
      in TailTerminal_can_be_removed_from_derivation)
              apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
              apply(force)
             apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
             apply(rule cfgRM_derivations_are_cfg_derivations)
             apply(force)
            apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
            apply(force)
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
           apply(clarsimp)
           apply(rule sym)
           apply(rule liftBDeConv2)
           apply(force)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
          apply(force)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
         apply(clarsimp)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa db x')(*strict*)
         apply(rule_tac
      x="db"
      in exI)
         apply(clarsimp)
         apply(rule_tac
      x="m"
      in exI)
         apply(clarsimp)
         apply(rule append_injective1)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa db x')(*strict*)
          apply(force)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa db x')(*strict*)
         apply(rule liftBDeConv2)
         apply(force)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
        apply(clarsimp)
    (*f4 done*)
    (*f_3*)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
        apply(subgoal_tac "\<exists>f3 n3 e3. cfgSTD.derivation G' f3 \<and> maximum_of_domain f3 n3 \<and> f3 0 = Some (pair None \<lparr>cfg_conf = [teA B]@xa\<rparr>) \<and> f3 n3 = Some (pair e3 \<lparr>cfg_conf = liftB xb@xa\<rparr>)")
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
         prefer 2
    (*f_2*)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
         apply(subgoal_tac "\<exists>d n e1a. cfgSTD.derivation G' d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = [teA B]\<rparr>) \<and> d n = Some (pair e1a \<lparr>cfg_conf = liftB xb\<rparr>)")
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
          prefer 2
    (*f_1*)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
          apply(subgoal_tac "\<exists>d x'. cfgSTD.derivation G' d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>) \<and> d n = Some (pair e1a \<lparr>cfg_conf = x'\<rparr>) \<and> x' @ liftB z = liftB (xb @ z)")
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
           prefer 2
           apply(rule_tac
      d="da"
      in TailTerminal_can_be_removed_from_derivation)
               apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
               apply(force)
              apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
              apply(force)
             apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
             apply(force)
            apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
            apply(force)
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
           apply(force)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
          apply(clarsimp)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 db x')(*strict*)
          apply(rename_tac f1 x1)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 x1)(*strict*)
          apply(subgoal_tac "x1=liftB xb")
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 x1)(*strict*)
           prefer 2
           apply(subgoal_tac "x1@liftB z=liftB xb@liftB z")
            apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 x1)(*strict*)
            apply(force)
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 x1)(*strict*)
           apply(rule_tac
      t="liftB xb @ liftB z"
      and s="liftB (xb @ z)"
      in subst)
            apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 x1)(*strict*)
            apply(rule liftB_commutes_over_concat)
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 x1)(*strict*)
           apply(force)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 x1)(*strict*)
          apply(clarsimp)
    (*f1done*)
    (*f2*)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
          apply(subgoal_tac "\<exists>e c. d (Suc(Suc (n'+m))) = Some (pair (Some e) c)")
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
           prefer 2
           apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
             apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
             apply(blast)
            apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
            apply(blast)
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
           apply(arith)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
          apply(clarsimp)
          apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 ea)(*strict*)
          apply(subgoal_tac "ea=\<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<and> cfgSTD_step_relation G' \<lparr>cfg_conf = [teA B]\<rparr> \<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr>")
           apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 ea)(*strict*)
           prefer 2
           apply(thin_tac "AF_LR_PARSER_input G F Do S' G' M P k")
           apply(thin_tac "viable_prefix G' \<gamma>")
           apply(thin_tac "valid_item G' k \<lparr>cfg_item_lhs = B, cfg_item_rhs1 = [], cfg_item_rhs2 = w, cfg_item_look_ahead = z\<rparr>")
           apply(thin_tac "set y \<subseteq> cfg_events G")
           apply(thin_tac "\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = [], cfg_item_rhs2 = w, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB (xs @ [x]))")
           apply(thin_tac "valid_dfa M")
           apply(thin_tac "some_step_from_every_configuration M")
           apply(thin_tac "x \<in> cfg_events G")
           apply(thin_tac "set xs \<subseteq> cfg_events G")
           apply(thin_tac "set \<gamma> \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
           apply(thin_tac "set (liftB (xs @ [x])) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
           apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
           apply(thin_tac "take k xa @ take (k - length xa) y' = liftB z")
           apply(thin_tac "cfgRM.derivation G' d'")
           apply(thin_tac "maximum_of_domain d' (Suc n')")
           apply(thin_tac "d' 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
           apply(thin_tac "d' n' = Some (pair e1 \<lparr>cfg_conf = \<delta>' @ teA A' # y'\<rparr>)")
           apply(thin_tac "d' (Suc n') = Some (pair (Some e2a) \<lparr>cfg_conf = \<delta>' @ x1a @ teB x # \<beta>' @ y'\<rparr>)")
           apply(thin_tac "setA y' = {}")
           apply(thin_tac "cfgRM.derivation G' d''")
           apply(thin_tac "maximum_of_domain d'' m")
           apply(thin_tac "d'' 0 = Some (pair None \<lparr>cfg_conf = \<beta>' @ y'\<rparr>)")
           apply(thin_tac "d'' m = Some (pair e3 \<lparr>cfg_conf = teA B # xa @ y'\<rparr>)")
           apply(thin_tac "\<forall>i. (i \<le> Suc n' \<longrightarrow> get_label (derivation_take d (Suc (n' + m)) i) = get_label (d' i)) \<and> (Suc n' < i \<longrightarrow> get_label (derivation_take d (Suc (n' + m)) i) = get_label (d'' (i - Suc n')))")
           apply(thin_tac "\<delta>' @ x1a = \<gamma> @ liftB xs")
           apply(thin_tac "\<lparr>cfg_item_lhs = A', cfg_item_rhs1 = x1a, cfg_item_rhs2 = teB x # \<beta>', cfg_item_look_ahead = take k (filterB y')\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB xs)")
           apply(thin_tac "take k y @ take (k - length y) [Do] = take k xb @ take (k - length xb) z")
           apply(thin_tac "cfgSTD.derivation G' da")
           apply(thin_tac "maximum_of_domain da n")
           apply(thin_tac "da 0 = Some (pair None \<lparr>cfg_conf = w @ liftB z\<rparr>)")
           apply(thin_tac "da n = Some (pair e1a \<lparr>cfg_conf = liftB (xb @ z)\<rparr>)")
           apply(thin_tac "cfgSTD.derivation G' f1")
           apply(thin_tac "maximum_of_domain f1 n")
           apply(thin_tac "f1 0 = Some (pair None \<lparr>cfg_conf = w\<rparr>)")
           apply(thin_tac "f1 n = Some (pair e1a \<lparr>cfg_conf = liftB xb\<rparr>)")
           apply(thin_tac "liftB xb @ liftB z = liftB (xb @ z)")
           apply(simp add: cfgRM.derivation_def)
           apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 ea)(*strict*)
           apply(erule_tac
      x="Suc(Suc (n'+m))"
      in allE)
           apply(clarsimp)
           apply(simp add: cfgRM_step_relation_def cfgSTD_step_relation_def)
           apply(clarsimp)
           apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 ea l r)(*strict*)
           apply(case_tac ea)
           apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 ea l r prod_lhsa prod_rhsa)(*strict*)
           apply(clarsimp)
           apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r prod_lhs prod_rhs)(*strict*)
           apply(rename_tac A v)
           apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r A v)(*strict*)
           apply(subgoal_tac "A=B \<and> v=w")
            apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r A v)(*strict*)
            apply(clarsimp)
            apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r)(*strict*)
            apply(rule_tac
      x="[]"
      in exI)
            apply(rule_tac
      x="[]"
      in exI)
            apply(clarsimp)
           apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r A v)(*strict*)
           apply(subgoal_tac "xa@y'=r")
            apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r A v)(*strict*)
            apply(clarsimp)
           apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r A v)(*strict*)
           apply(thin_tac "valid_cfg G'")
           apply(thin_tac "d (Suc (n' + m)) = Some (pair (Some e) \<lparr>cfg_conf = l @ teA A # r\<rparr>)")
           apply(thin_tac "d (Suc (Suc (n' + m))) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = v\<rparr>) \<lparr>cfg_conf = l @ v @ r\<rparr>)")
           apply(thin_tac "maximum_of_domain d (Suc (Suc (n' + m)))")
           apply(thin_tac "\<lparr>prod_lhs = A, prod_rhs = v\<rparr> \<in> cfg_productions G'")
           apply(thin_tac "\<gamma> @ liftB (xs @ [x]) @ w @ xa @ y' = l @ v @ r")
           apply(rule sym)
           apply(rule_tac
      ?v2.0="\<gamma> @ liftB (xs @ [x])"
      and ?v1.0="l"
      and A="A"
      and B="B"
      in terminalTailEquals1)
             apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r A v)(*strict*)
             apply(force)
            apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r A v)(*strict*)
            apply(force)
           apply(rename_tac x xs B w d e n' \<beta>' y' m xa f4 n4 e4 l r A v)(*strict*)
           apply(clarsimp)
          apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1 ea)(*strict*)
          apply(clarsimp)
          apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
          apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA B]\<rparr> \<lparr>prod_lhs = B, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr>) f1 (Suc 0)"
      in exI)
          apply(rule context_conjI)
           apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
           apply(rule cfgSTD.derivation_concat2)
              apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
              apply(rule cfgSTD.der2_is_derivation)
              apply(force)
             apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
             apply(rule der2_maximum_of_domain)
            apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
            apply(force)
           apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
           apply(simp add: der2_def)
          apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
          apply(rule_tac
      x="Suc 0+n"
      in exI)
          apply(rule context_conjI)
           apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
           apply(rule_tac concat_has_max_dom)
            apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
            apply(rule der2_maximum_of_domain)
           apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
           apply(force)
          apply(rename_tac x xs B w z y d e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1a da e1a n xb xa f4 n4 e4 f1)(*strict*)
          apply(simp add: der2_def derivation_append_def)
          apply(clarsimp)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
         apply(clarsimp)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 db na e1aa)(*strict*)
         apply(rename_tac f2 n2 e2)
    (*f2done*)
    (*f3*)
         apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
         apply(rule_tac
      x = "derivation_map f2 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@xa\<rparr>)"
      in exI)
         apply(rule context_conjI)
          apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
          apply(rule cfgSTD.from_to_is_der)
          apply(rule_tac
      w="xa"
      and dF="\<lparr>cfg_conf = [teA B]\<rparr>"
      and dT="\<lparr>cfg_conf=liftB xb\<rparr>"
      in contextExtendIsFromTo)
             apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
             apply(force)
            apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
            apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
            apply(rule_tac
      x="n2"
      in exI)
            apply(clarsimp)
            apply(simp add: maximum_of_domain_def)
           apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
           apply(force)
          apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
          apply(force)
         apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
         apply(rule_tac
      x="n2"
      in exI)
         apply(rule conjI)
          apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
          apply(rule derivation_map_preserves_maximum_of_domain)
          apply(blast)
         apply(rename_tac x xs B w z y d e2a e d' n' e1 e2aa e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f2 n2 e2)(*strict*)
         apply(simp add: derivation_map_def)+
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4)(*strict*)
        apply(clarsimp)
    (*f3done*)
    (*f5*)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
        apply(rule_tac
      x = "derivation_append f4 f3 n4"
      in exI)
        apply(rule context_conjI)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
         apply(rule cfgSTD.derivation_concat2)
            apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
            apply(force)
           apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
           apply(force)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
          apply(force)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
         apply(clarsimp)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
        apply(rule_tac
      x="n4+n3"
      in exI)
        apply(rule context_conjI)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
         apply(rule_tac concat_has_max_dom)
          apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
          apply(force)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
         apply(force)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f4 n4 e4 f3 n3 e3a)(*strict*)
        apply(simp add: derivation_append_def)
        apply(clarsimp)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
       apply(clarsimp)
    (*f5done*)
    (*f6*)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
       apply(rule_tac
      x = "derivation_map f5 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@(take k y')\<rparr>)"
      in exI)
       apply(rule context_conjI)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
        apply(rule cfgSTD.from_to_is_der)
        apply(rule_tac
      w="take k y'"
      and dF="\<lparr>cfg_conf = \<beta>'\<rparr>"
      and dT="\<lparr>cfg_conf=liftB xb@xa\<rparr>"
      in contextExtendIsFromTo)
         apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
         apply(force)
        apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
        apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
        apply(rule_tac
    x="n5"
    in exI)
        apply(clarsimp)
        apply(simp add: maximum_of_domain_def)
       apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
       apply(force)
      apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
      apply(force)
     apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
     apply(rule_tac
    x="n5"
    in exI)
     apply(rule conjI)
      apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(blast)
     apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f5 n5 e5)(*strict*)
     apply(simp add: derivation_map_def)+
    apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa)(*strict*)
    apply(clarsimp)
  (*f6done*)
    apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
    apply(rule_tac
    x="f6"
    in exI)
    apply(clarsimp)
    apply(rule_tac
    x="e6"
    in exI)
    apply(rule_tac
    x="n6"
    in exI)
    apply(clarsimp)
    apply(rule_tac
    t="liftB (xb @ filterB xa @ take k (filterB y'))"
    and s="liftB xb @ liftB (filterB xa @ take k (filterB y'))"
    in ssubst)
     apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
     apply(rule liftB_commutes_over_concat)
    apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
    apply(clarsimp)
    apply(rule_tac
    t="liftB (filterB xa @ take k (filterB y'))"
    and s="liftB (filterB xa) @ liftB (take k (filterB y'))"
    in ssubst)
     apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
     apply(rule liftB_commutes_over_concat)
    apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
    apply(rule_tac
    t="liftB (filterB xa)"
    and s="xa"
    in ssubst)
     apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
     apply(rule liftBDeConv2)
     apply(simp only: setAConcat concat_asso)
     apply(force)
    apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
    apply(clarsimp)
    apply(rule_tac
    P="\<lambda>q. take k q = liftB (take k (filterB y'))"
    and t="y'"
    and s="liftB (filterB y')"
    in subst)
     apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
     apply(rule liftBDeConv2)
     apply(force)
    apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
    apply(rule_tac
    t="take k (liftB (filterB y'))"
    and s="liftB (take k (filterB y'))"
    in ssubst)
     apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
     apply(rule take_liftB)
    apply(rename_tac x xs B w z y d e2 e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb xa f6 n6 e6)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
   apply(subgoal_tac "\<exists>v e. d'' (0+m) = Some (pair e \<lparr>cfg_conf=v@y'\<rparr>)")
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
    prefer 2
    apply(rule TailTerminalStringsGrow)
       apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
      apply(force)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb v)(*strict*)
   apply(case_tac v)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb v)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 da e1a n xb v a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
  apply(subgoal_tac "\<exists>v e. da (0+n) = Some (pair e \<lparr>cfg_conf=v@(liftB z)\<rparr>)")
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
   prefer 2
   apply(rule TailTerminalStringsGrow)
      apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
      apply(force)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
     apply(rule setA_liftB)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
   apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
  apply(rule_tac
    x="filterB v"
    in exI)
  apply(rule_tac
    s="filterB (liftB z)"
    and t="z"
    in ssubst)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
   apply(rule sym)
   apply(rule liftBDeConv1)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
  apply(rule_tac
    s="filterB (liftB xa)"
    and t="xa"
    in ssubst)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
   apply(rule sym)
   apply(rule liftBDeConv1)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
  apply(rule_tac
    t="filterB v @ filterB (liftB z)"
    and s="filterB (v @ (liftB z))"
    in ssubst)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
   apply(rule sym)
   apply(rule filterB_commutes_over_concat)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
  apply(rule_tac
    t="v @ liftB z"
    and s="liftB xa"
    in ssubst)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
   apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1 xa da e1a n v)(*strict*)
  apply(blast)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
  prefer 2
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(erule_tac
    x="A"
    in meta_allE)
  apply(erule_tac
    x="\<alpha>'"
    in meta_allE)
  apply(erule_tac
    x="[teB x]@\<beta>"
    in meta_allE)
  apply(erule_tac
    x="z"
    in meta_allE)
  apply(erule_tac
    x="x#y"
    in meta_allE)
  apply(erule meta_impE)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(rule Lemma6__24_2_items_rev)
  apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(erule meta_impE)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(rule set_take_head2)
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
   apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(erule meta_impE)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(rule valid_item_set_shift_symbol_back)
  apply(rule_tac
    t="(\<gamma> @ liftB xs) @ [teB x]"
    and s="\<gamma> @ liftB (xs @ [x])"
    in subst)
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs A \<beta> z y \<alpha>')(*strict*)
   apply(rule liftB_commute_one_elem_app)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(erule meta_impE)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(rule cfgSTD_first_add_terminal_front)
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
   apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>')(*strict*)
  apply(erule exE)+
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>')(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
  apply(subgoal_tac "take (k - Suc 0) (y @ [Do]) \<in> cfgSTD_first G' (k - Suc 0) (\<beta> @ liftB z)")
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
  prefer 2
  apply(rule_tac
    t="take (k - Suc 0) (y @ [Do])"
    and s="take (k - Suc 0) (take k (y @ [Do]))"
    in ssubst)
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
   apply(rule sym)
   apply(rule_tac
    s="take (ord_class.min (k - Suc 0) k) (y@[Do])"
    and t="take (k - Suc 0) (take k (y@[Do]))"
    in ssubst)
    apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
    apply(rule take_take)
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
   apply(rule_tac
    t="ord_class.min (k-Suc 0) k"
    and s="k-Suc 0"
    in ssubst)
    apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
  apply(rule_tac
    k="k"
    in cfgSTD_first_take)
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
  apply(rule Lemma6__31_hlp)
                    apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
                    apply(force)
                   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
                   apply(force)
                  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
                  apply(force)
                 apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
                 apply(force)
                apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
                apply(force)
               apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
               apply(force)
              apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
              apply(force)
             apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
             apply(force)
            apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
            apply(force)
           apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
           apply(force)
          apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
          apply(force)
         apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
         apply(force)
        apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
        apply(force)
       apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
       apply(force)
      apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
      apply(force)
     apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac x xs A \<alpha> \<beta> z y \<alpha>' \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta>' y' A' d'' m x1)(*strict*)
  apply(rename_tac \<beta> y' A d'' m \<alpha>')
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(erule_tac
    x="A"
    in meta_allE)
  apply(erule_tac
    x="\<alpha>'"
    in meta_allE)
  apply(erule_tac
    x="[teB x]@\<beta>"
    in meta_allE)
  apply(erule_tac
    x="take k (filterB y')"
    in meta_allE)
  apply(erule_tac
    x="x#y"
    in meta_allE)
  apply(erule meta_impE)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(rule_tac
    \<gamma>="(\<gamma> @ liftB xs)"
    in Fact6_12__2)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(rule_tac
    t="[teB x]@\<beta>"
    and s="teB x#\<beta>"
    in ssubst)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(erule meta_impE)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(rule set_take_head2)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(erule meta_impE)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(rule_tac
    t="[teB x]@\<beta>"
    and s="teB x#\<beta>"
    in ssubst)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(erule meta_impE)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(case_tac k)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  prefer 2
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
  apply(rule_tac
    t="take k (x # y) @ take (k - length (x # y)) [Do]"
    and s="take k (x # y @ [Do])"
    in ssubst)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
   apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
  apply(rule_tac
    t="(([teB x] @ \<beta>) @ liftB (take k (filterB y')))"
    and s="(teB x # \<beta> @ take k y')"
    in ssubst)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule_tac
    P="\<lambda>q. take (Suc nat) q = liftB (take (Suc nat) (filterB y'))"
    and t="y'"
    and s="liftB (filterB y')"
    in subst)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
    apply(rule liftBDeConv2)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
   apply(rule_tac
    t="take (Suc nat) (liftB (filterB y'))"
    and s="liftB (take (Suc nat) ((filterB y')))"
    in ssubst)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
    apply(rule take_liftB)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
   apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' nat)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(clarsimp)
  apply(rule_tac
    t="[]"
    and s="take 0 [x]"
    in ssubst)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(rule cfgSTD_first_take)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>')(*strict*)
  apply(erule exE)+
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>')(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>'@[teB x], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = take k (filterB y')\<rparr> \<in> valid_item_set G' k (\<gamma> @ liftB (xs@[x]))")
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  prefer 2
  apply(rule_tac
    t="\<gamma> @ liftB (xs @ [x])"
    and s="(\<gamma> @ liftB xs) @ [teB x]"
    in ssubst)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(rule_tac
    t="liftB (xs @ [x])"
    and s="liftB xs @ [teB x]"
    in ssubst)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
   apply(rule liftB_commute_one_elem_app)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(rule_tac \<gamma>="(\<gamma> @ liftB xs)" in Lemma6__24_2_prime)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(rule_tac
    t="[teB x] @ \<beta>"
    and s="teB x # \<beta>"
    in ssubst)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
   apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(subgoal_tac "valid_item G' k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>'@[teB x], cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = take k (filterB y')\<rparr>")
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  prefer 2
  apply(rule Fact6_12__2)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(subgoal_tac "take (k - Suc 0) (y @ [Do]) \<in> cfgSTD_first G' (k - Suc 0) (\<beta> @ liftB (take k (filterB y')))")
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  prefer 2
  apply(rule_tac
    t="liftB (take k (filterB y'))"
    and s="take k y'"
    in subst)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(rule liftB_take_prime)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(subgoal_tac "take (k - Suc 0) (y @ [Do]) \<in> cfgSTD_first G' (k - 1) (\<beta> @ take k y')")
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  prefer 2
  apply(rule cfgSTD_first_drop_head_terminal)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
   apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(rule_tac
    G="G"
    and S'="S'"
    and A="A"
    and \<alpha>="\<alpha>'@[teB x]"
    and \<beta>="\<beta>"
    and z="take k (filterB y')"
    in Lemma6__31_hlp)
                   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
                   apply(force)
                  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
                  apply(force)
                 apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
                 apply(force)
                apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
                apply(force)
               apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
               apply(force)
              apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
              apply(force)
             apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
             apply(force)
            apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
            apply(force)
           apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
           apply(force)
          apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
          apply(force)
         apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
         apply(force)
        apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
        apply(force)
       apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
       apply(force)
      apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
      apply(force)
     apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
     apply(force)
    apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
    apply(force)
   apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
   apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  apply(rename_tac x xs B w z y d e2 za e d' n' e1 e2a e3 \<delta>' \<beta> y' A d'' m \<alpha>' \<pi>' dP ea)(*strict*)
  apply(force)
  done

lemma AF_LR_PARSER_apply_parser_marker: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> (r, Some v) \<in> AF_LR_PARSER__rules G G' M k
  \<Longrightarrow> tau (parser_marker P) [Some r] = [Some v]"
  apply(simp add: tau_def)
  apply(subgoal_tac "\<exists>!y. ((r,y) \<in> (AF_LR_PARSER__rules G G' M k))")
   prefer 2
   apply(rule X6_3_InformationOnRules_UniqueEffect)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(simp add: AF_LR_PARSER_input_def)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(simp only: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(force)
  apply(simp only: AF_LR_PARSER_input_def AF_LR_PARSER_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(rule_tac
      t="THE y. (r, y) \<in> AF_LR_PARSER__rules G (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k) k"
      and s="y"
      in ssubst)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac y)(*strict*)
  apply(force)
  done

theorem Lemma6__32: "
  AF_LR_PARSER_input G F Do S' G' M P k
  \<Longrightarrow> set XSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> set YSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> set x \<subseteq> cfg_events G
  \<Longrightarrow> set y \<subseteq> cfg_events G
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> valid_item G' k
          \<lparr>cfg_item_lhs = A,
            cfg_item_rhs1 = \<alpha>,
            cfg_item_rhs2 = \<beta>,
            cfg_item_look_ahead = z\<rparr>
  \<Longrightarrow> cfgRM.derivation G d
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> n = length \<pi>
  \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>)
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = YSEQ @ (liftB x) \<rparr>)
  \<Longrightarrow> filter
        (\<lambda>x. case x of None \<Rightarrow> False | Some x \<Rightarrow> True)
        (get_labels d n)
      = List.rev (map Some \<pi>)
  \<Longrightarrow> \<lparr>cfg_item_lhs = A,
        cfg_item_rhs1 = \<alpha>,
        cfg_item_rhs2 = \<beta>,
        cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k ([teB Do] @ XSEQ)
  \<Longrightarrow> take k (y @ [Do]) \<in> cfgSTD_first G' k (\<beta> @ (liftB z))
  \<Longrightarrow> \<forall>YSEQ' YSEQt. YSEQ = YSEQ' @ [YSEQt] \<longrightarrow> YSEQt \<in> teA ` (cfg_nonterminals G)
  \<Longrightarrow> \<exists>\<pi>' dP e.
        tau (parser_marker P) \<pi>' = map Some \<pi>
        \<and> length \<pi>' = length \<pi> + length x
        \<and> parserS.derivation P dP
        \<and> maximum_of_domain dP (length \<pi>')
        \<and> dP 0 = Some (pair None
              \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ),
              parserS_conf_scheduler = x @ y @ [Do]\<rparr>)
        \<and> dP (length \<pi>') = Some (pair e
              \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ),
              parserS_conf_scheduler = y @ [Do]\<rparr>)
        \<and> get_labels dP (length \<pi>') = \<pi>'"
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
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add: AF_LR_PARSER_input_def)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(force)
  apply(subgoal_tac "cfg_events G \<subseteq> cfg_events G'")
   prefer 2
   apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
   apply(force)
  apply(subgoal_tac "set ([teB Do]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   prefer 2
   apply(clarsimp)
   apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(subgoal_tac "two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   prefer 2
   apply(rule F_CFG_AUGMENT__two_elements_construct_domain_subset)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(force)
    apply(force)
   apply(simp add: AF_LR_PARSER_input_def)
  apply(induct \<pi> arbitrary: n d YSEQ e YSEQ x)
   apply(rename_tac n d YSEQ e x)(*strict*)
   apply(clarsimp)
   apply(rename_tac d YSEQ x)(*strict*)
   apply(subgoal_tac "\<exists>\<pi>' dP e. length \<pi>'=length x \<and> length (tau (parser_marker P) \<pi>') = 0 \<and> parserS.derivation P dP \<and> maximum_of_domain dP (length x) \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do#YSEQ))@[valid_item_set G' k (teB Do # YSEQ)],parserS_conf_scheduler=x@y@[Do]\<rparr>) \<and> dP (length x) = Some (pair e \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do#YSEQ)) @[valid_item_set G' k (teB Do # YSEQ)] @(F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB x)), parserS_conf_scheduler=y@[Do]\<rparr>) \<and> get_labels dP (length x) = \<pi>'")
    apply(rename_tac d YSEQ x)(*strict*)
    prefer 2
    apply(rule_tac Lemma6__31)
           apply(rename_tac d YSEQ x)(*strict*)
           apply(force)
          apply(rename_tac d YSEQ x)(*strict*)
          apply(rule_tac
      w="(teB Do # YSEQ @ liftB x)"
      in viable_prefix_nonempty_on_every_prefix)
               apply(rename_tac d YSEQ x)(*strict*)
               apply(force)
              apply(simp add: AF_LR_PARSER_input_def)
              apply(force)
             apply(rename_tac d YSEQ x)(*strict*)
             apply(rule Fact6_12__1)
             apply(force)
            apply(rename_tac d YSEQ x)(*strict*)
            apply(force)
           apply(rename_tac d YSEQ x)(*strict*)
           apply(rule_tac
      t="teB Do # YSEQ @ liftB x"
      and s="[teB Do] @ YSEQ @ liftB x"
      in ssubst)
            apply(rename_tac d YSEQ x)(*strict*)
            apply(force)
           apply(rename_tac d YSEQ x)(*strict*)
           apply(rule_tac
      A="cfg_nonterminals G'"
      and B="cfg_events G'"
      in two_elements_construct_domain_setA)
           apply(rule set_concat_subset)
            apply(rename_tac d YSEQ x)(*strict*)
            apply(force)
           apply(rename_tac d YSEQ x)(*strict*)
           apply(rule set_concat_subset)
            apply(rename_tac d YSEQ x)(*strict*)
            apply(force)
           apply(rename_tac d YSEQ x)(*strict*)
           apply(force)
          apply(rename_tac d YSEQ x)(*strict*)
          apply(rule_tac
      t="teB Do # YSEQ @ liftB x"
      and s="[teB Do] @ YSEQ @ liftB x"
      in ssubst)
           apply(rename_tac d YSEQ x)(*strict*)
           apply(force)
          apply(rename_tac d YSEQ x)(*strict*)
          apply(rule_tac
      A="cfg_nonterminals G'"
      and B="cfg_events G'"
      in two_elements_construct_domain_setB)
          apply(rule set_concat_subset)
           apply(rename_tac d YSEQ x)(*strict*)
           apply(force)
          apply(rename_tac d YSEQ x)(*strict*)
          apply(rule set_concat_subset)
           apply(rename_tac d YSEQ x)(*strict*)
           apply(force)
          apply(rename_tac d YSEQ x)(*strict*)
          apply(force)
         apply(rename_tac d YSEQ x)(*strict*)
         apply(force)
        apply(rename_tac d YSEQ x)(*strict*)
        apply(force)
       apply(rename_tac d YSEQ x)(*strict*)
       apply(force)
      apply(rename_tac d YSEQ x)(*strict*)
      apply(force)
     apply(rename_tac d YSEQ x)(*strict*)
     apply(force)
    apply(rename_tac d YSEQ x)(*strict*)
    apply(simp add: Lemma6__31_input_def)
    apply(clarsimp)
    apply(rule_tac
      x="last YSEQ"
      in exI)
    apply(force)
   apply(rename_tac d YSEQ x)(*strict*)
   apply(erule exE)+
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(erule conjE)+
   apply(rule_tac
      x="\<pi>'"
      in exI)
   apply(rule conjI)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(rule conjI)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(rule_tac
      x="dP"
      in exI)
   apply(rule conjI)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(rule conjI)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ)) @ [valid_item_set G' k (teB Do # YSEQ)] = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ)")
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ)) @ [valid_item_set G' k (teB Do # YSEQ)] @ F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB x) = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ liftB x)")
     apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCE_append_valid_item_set)
         apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
       apply(force)
      apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def)
     apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ)) @ [valid_item_set G' k (teB Do # YSEQ)] @ F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB x)"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ)@F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB x)"
      in ssubst)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(rule_tac
      t="teB Do # YSEQ @ liftB x"
      and s="(teB Do # YSEQ) @ liftB x"
      in ssubst)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((teB Do # YSEQ) @ liftB x)"
      and s="F_DFA_GOTO_SEQUENCE SSM SSp SSw1 @ F_DFA_GOTO_SEQUENCE SSM (last (SSp # F_DFA_GOTO_SEQUENCE SSM SSp SSw1)) SSw2" for SSM SSp SSw1 SSw2
      in ssubst)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(rule F_DFA_GOTO_SEQUENCE_append_split)
         apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
         apply(force)
        apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
        apply(force)
       apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
       apply(force)
      apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
     apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(subgoal_tac "valid_item_set G' k (teB Do # YSEQ) = last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ))")
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
           apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
           apply(force)
          apply(simp add: AF_LR_PARSER_input_def)
          apply(force)
         apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
        apply(force)
       apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
       apply(force)
      apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
      apply(rule two_elements_construct_domain_setA)
      apply(force)
     apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
     apply(rule two_elements_construct_domain_setB)
     apply(force)
    apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac d YSEQ x \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac a \<pi> n d YSEQ e x)(*strict*)
  apply(case_tac a)
  apply(rename_tac a \<pi> n d YSEQ e x prod_lhs prod_rhs)(*strict*)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega>)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega>)(*strict*)
  apply(case_tac n)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega>)(*strict*)
   apply(clarsimp)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> nat)(*strict*)
  apply(rename_tac n')
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n')(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc n') = Some (pair (Some e) c)")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n')(*strict*)
   prefer 2
   apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n')(*strict*)
     apply(blast)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n')(*strict*)
    apply(blast)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n')(*strict*)
   apply(arith)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n')(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
  apply(subgoal_tac "d (Suc n') = Some (pair (Some ea) \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>)")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
  apply(thin_tac " d (Suc n') = Some (pair (Some ea) c)")
  apply(thin_tac "d n = Some (pair e \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>)")
  apply(subgoal_tac "r1=ea")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
   prefer 2
   apply(subgoal_tac "Some ea=Some \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr>")
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
    prefer 2
    apply(rule_tac
      t="Some ea"
      and s="last(filter (case_option False (\<lambda>x. True)) (get_labels d (Suc (length \<pi>1))))"
      in ssubst)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
     apply(subgoal_tac "last(get_labels d (Suc (length \<pi>1)))=Some ea")
      apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
      prefer 2
      apply(rule_tac
      t="last (get_labels d (Suc (length \<pi>1)))"
      and s="(get_labels d (Suc (length \<pi>1))) ! (length \<pi>1)"
      in ssubst)
       apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
       apply(rule last_nth3)
       apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
       apply(rule sym)
       apply(rule get_labels_length)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
      apply(rule get_labels_Not_None)
       apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
     apply(case_tac "get_labels d (Suc (length \<pi>1))")
      apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. get_labels d (Suc (length \<pi>1)) = w' @ [x']")
      apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c a list)(*strict*)
     apply(thin_tac "get_labels d (Suc (length \<pi>1)) = a # list")
     apply(erule exE)+
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c a list w' x')(*strict*)
     apply(subgoal_tac "Some ea=x'")
      apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c a list w' x')(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c a list w' x')(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
  apply(subgoal_tac "d (Suc n') = Some (pair (Some r1) \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>)")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
  apply(thin_tac "d (Suc n') = Some (pair (Some ea) \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>)")
  apply(thin_tac "r1=ea")
  apply(subgoal_tac "\<exists>ZSEQ x1 v e. d n' = Some (pair e \<lparr>cfg_conf=ZSEQ@[teA B]@(liftB x1)\<rparr>) \<and> YSEQ @ liftB x = ZSEQ@\<omega>@(liftB x1) \<and> x=v@x1 \<and> ZSEQ@\<omega>=YSEQ@(liftB v) ")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
   prefer 2
   apply(thin_tac "\<And>n d YSEQ e x. AF_LR_PARSER_input G F Do S' G' M P k \<Longrightarrow> set XSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<Longrightarrow> set YSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<Longrightarrow> set x \<subseteq> cfg_events G \<Longrightarrow> set y \<subseteq> cfg_events G \<Longrightarrow> set \<pi>1 \<subseteq> cfg_productions G \<Longrightarrow> valid_item G' k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<Longrightarrow> cfgRM.derivation G d \<Longrightarrow> maximum_of_domain d n \<Longrightarrow> n = length \<pi>1 \<Longrightarrow> d 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>) \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>) \<Longrightarrow> filter (case_option False (\<lambda>x. True)) (get_labels d n) = rev (map Some \<pi>1) \<Longrightarrow> \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr> \<in> valid_item_set G' k ([teB Do] @ XSEQ) \<Longrightarrow> take k (y @ [Do]) \<in> cfgSTD_first G' k (\<beta> @ liftB z) \<Longrightarrow> \<forall>YSEQ' YSEQt. YSEQ = YSEQ' @ [YSEQt] \<longrightarrow> YSEQt \<in> teA ` cfg_nonterminals G \<Longrightarrow> valid_cfg G' \<Longrightarrow> valid_dfa M \<Longrightarrow> some_step_from_every_configuration M \<Longrightarrow> every_state_in_some_accessible_configuration M \<Longrightarrow> cfg_events G \<subseteq> cfg_events G' \<Longrightarrow> set [teB Do] \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G') \<Longrightarrow> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G') \<Longrightarrow> \<exists>\<pi>' dP e. tau (parser_marker P) \<pi>' = map Some \<pi>1 \<and> length \<pi>' = length \<pi>1 + length x \<and> parserS.derivation P dP \<and> maximum_of_domain dP (length \<pi>') \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ), parserS_conf_scheduler = x @ y @ [Do]\<rparr>) \<and> dP (length \<pi>') = Some (pair e \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # XSEQ), parserS_conf_scheduler = y @ [Do]\<rparr>) \<and> get_labels dP (length \<pi>') = \<pi>'")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega>)(*strict*)
   apply(subgoal_tac "\<exists>e c. d (length \<pi>1) = Some (pair e c)")
    apply(rename_tac \<pi>1 d YSEQ x B \<omega>)(*strict*)
    prefer 2
    apply(rule cfgRM.some_position_has_details_before_max_dom)
      apply(rename_tac \<pi>1 d YSEQ x B \<omega>)(*strict*)
      apply(blast)
     apply(rename_tac \<pi>1 d YSEQ x B \<omega>)(*strict*)
     apply(blast)
    apply(rename_tac \<pi>1 d YSEQ x B \<omega>)(*strict*)
    apply(arith)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega>)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e c)(*strict*)
   apply(case_tac c)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e c cfg_conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e cfg_conf)(*strict*)
   apply(rename_tac c)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e c)(*strict*)
   apply(subgoal_tac "cfgRM_step_relation G \<lparr>cfg_conf = c\<rparr> \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr> \<lparr>cfg_conf = YSEQ @ liftB x\<rparr>")
    apply(rename_tac \<pi>1 d YSEQ x B \<omega> e c)(*strict*)
    prefer 2
    apply(rule_tac
      n="length \<pi>1"
      in cfgRM.position_change_due_to_step_relation)
      apply(rename_tac \<pi>1 d YSEQ x B \<omega> e c)(*strict*)
      apply(blast)
     apply(rename_tac \<pi>1 d YSEQ x B \<omega> e c)(*strict*)
     apply(blast)
    apply(rename_tac \<pi>1 d YSEQ x B \<omega> e c)(*strict*)
    apply(blast)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e c)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r)(*strict*)
   apply(rule_tac
      x="l"
      in exI)
   apply(rule_tac
      x="filterB r"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r)(*strict*)
    apply(clarsimp)
    apply(rule sym)
    apply(rule liftBDeConv2)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r)(*strict*)
   apply(subgoal_tac "\<exists>v. x = v @ filterB r")
    apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> e l r v)(*strict*)
    apply(rule_tac
      a="r"
      and b="liftB (filterB r)"
      in append_injective1)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> e l r v)(*strict*)
     apply(rule_tac
      t="(YSEQ @ liftB v) @ liftB (filterB r)"
      and s="YSEQ @ liftB (v @ (filterB r))"
      in ssubst)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> e l r v)(*strict*)
      apply(rule_tac
      t="liftB (v @ filterB r)"
      and s="(liftB v) @ liftB (filterB r)"
      in ssubst)
       apply(rename_tac \<pi>1 d YSEQ B \<omega> e l r v)(*strict*)
       apply(rule liftB_commutes_over_concat)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> e l r v)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> e l r v)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> e l r v)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r)(*strict*)
   apply(clarsimp)
   apply(case_tac YSEQ)
    apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
    apply(rule_tac
      x="filterB (l@\<omega>)"
      in exI)
    apply(rule liftB_inj)
    apply(rule_tac
      t="liftB (filterB (l @ \<omega>) @ filterB r)"
      and s="liftB (filterB (l @ \<omega>)) @ (liftB (filterB r))"
      in ssubst)
     apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
     apply(rule liftB_commutes_over_concat)
    apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
    apply(rule_tac
      t="liftB (filterB (l @ \<omega>))"
      and s="l@\<omega>"
      in ssubst)
     apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
     apply(rule liftBDeConv2)
     apply(rule order_antisym)
      apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
      apply(rule_tac
      B="setA (l@\<omega>@r)"
      in subset_trans)
       apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
       apply(simp (no_asm) only: setAConcat concat_asso)
       apply(force)
      apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
      apply(rule_tac
      B="setA (liftB x)"
      in subset_trans)
       apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
      apply(rule setA_liftB_subset)
     apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d x B \<omega> e l r)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. YSEQ = w' @ [x']")
    apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ x B \<omega> e l r a list)(*strict*)
   apply(thin_tac "YSEQ=a#list")
   apply(clarsimp)
   apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa)(*strict*)
   apply(subgoal_tac "\<exists>v. liftB x = v @ r")
    apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa)(*strict*)
    prefer 2
    apply(rule_tac
      y="w'"
      and A="xa"
      and w="l@\<omega>"
      in terminal_end_suffix)
     apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
   apply(rule_tac
      x="filterB v"
      in exI)
   apply(rule liftB_inj)
   apply(rule_tac
      t="liftB (filterB v @ filterB r)"
      and s="liftB (filterB v) @ (liftB (filterB r))"
      in ssubst)
    apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
    apply(rule liftB_commutes_over_concat)
   apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
   apply(rule_tac
      t="liftB (filterB v)"
      and s="v"
      in ssubst)
    apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
    apply(rule liftBDeConv2)
    apply(rule order_antisym)
     apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
     apply(rule_tac
      B="setA (v@r)"
      in subset_trans)
      apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
      apply(simp (no_asm) only: setAConcat concat_asso)
      apply(force)
     apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
     apply(rule_tac
      B="setA (liftB x)"
      in subset_trans)
      apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
     apply(rule setA_liftB_subset)
    apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d x B \<omega> e l r w' xa v)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "set [teA B] \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   prefer 2
   apply(subgoal_tac "r1 \<in> cfg_productions G")
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb)(*strict*)
   apply(rule prod_lhs_in_nonterms)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(subgoal_tac "set \<omega> \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   prefer 2
   apply(subgoal_tac "r1 \<in> cfg_productions G")
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(rule prod_rhs_in_cfg_events)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule prod_rhs_in_nonterms)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(subgoal_tac "set v \<subseteq> cfg_events G")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(subgoal_tac "set x1 \<subseteq> cfg_events G")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(subgoal_tac "set ZSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   prefer 2
   apply(rule_tac
      B="set (ZSEQ @ \<omega>)"
      in subset_trans)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(rule set_app_subset)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule_tac
      t="ZSEQ@\<omega>"
      and s="YSEQ @ liftB v"
      in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule set_concat_subset)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule liftB_lift)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule_tac
      x="length \<pi>1"
      in meta_allE)
  apply(erule_tac
      x="derivation_take d (length \<pi>1)"
      in meta_allE)
  apply(erule_tac
      x="ZSEQ@[teA B]"
      in meta_allE)
  apply(erule_tac
      x="eb"
      in meta_allE)
  apply(erule_tac
      x="x1"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule_tac cfgRM.derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule_tac
      m="Suc 0"
      in cfgRM.derivation_take_preserves_generates_maximum_of_domain)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule_tac
      t="get_labels (derivation_take d (length \<pi>1)) (length \<pi>1)"
      and s="take (length \<pi>1) (get_labels d n)"
      in subst)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(rule_tac
      n="Suc 0"
      in derivation_take_preserves_get_labels)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule_tac
      a="filter (case_option False (\<lambda>x. True)) [(get_labels d n)!(length \<pi>1)]"
      and b="[Some r1]"
      in append_injective1)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(rule_tac
      t="List.rev (map Some \<pi>1) @ [Some r1]"
      and s="List.rev (map Some (r1 # \<pi>1))"
      in ssubst)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(rule_tac
      t="filter (case_option False (\<lambda>x. True)) (take (length \<pi>1) (get_labels d n)) @ filter (case_option False (\<lambda>x. True)) [get_labels d n ! length \<pi>1]"
      and s="filter (case_option False (\<lambda>x. True)) (get_labels d n)"
      in ssubst)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
     apply(rule_tac
      P="\<lambda>q. filter (case_option False (\<lambda>x. True)) (take (length \<pi>1) (get_labels d n)) @ filter (case_option False (\<lambda>x. True)) [get_labels d n ! length \<pi>1] = filter (case_option False (\<lambda>x. True)) q"
      and t="get_labels d n"
      and s="take (length \<pi>1) (get_labels d n) @ [get_labels d n ! length \<pi>1]"
      in ssubst)
      apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
      apply(rule_tac
      t="n"
      and s="Suc(length \<pi>1)"
      in ssubst)
       apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
      apply(rule take_nth)
      apply(rule get_labels_length)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
     apply(rule filter_app)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(rule_tac
      t="get_labels d n ! length \<pi>1"
      and s="Some r1"
      in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(rule get_labels_Not_None)
     apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb)(*strict*)
   apply(rule inMap)
   apply(rule_tac
      x="B"
      in bexI)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb)(*strict*)
   apply(rule prod_lhs_in_nonterms)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb \<pi>' dP ec)(*strict*)
  apply(erule conjE)+
  apply(rename_tac \<pi>1' d4 ec)
  apply(rename_tac r1 \<pi>1 n d YSEQ e x B \<omega> n' ea c ZSEQ x1 v eb \<pi>1' d4 ec)(*strict*)
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na da)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na da \<delta> e1 e2 za)(*strict*)
  apply(erule conjE)+
  apply(rename_tac d5 \<delta> e1 e2 z')
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z')(*strict*)
  apply(subgoal_tac "\<exists>u. u \<in> cfgSTD_first G' k \<beta> \<and> take k (y@[Do]) = take k (u@z)")
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z')(*strict*)
   prefer 2
   apply(subgoal_tac "take k (y@[Do]) \<in> kPrefix SSk ` append_language (cfgSTD_first SSG SSk SSw) {SSv}" for SSk SSG SSw SSv)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z')(*strict*)
    prefer 2
    apply(rule_tac
      t="kPrefix SSk ` append_language (cfgSTD_first SSG SSk SSw) {SSv}"
      and s="cfgSTD_first G' k (\<beta> @ liftB z)" for SSG SSk SSw SSv
      in ssubst)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z')(*strict*)
     apply(rule cfgSTD_first_pull_out_terimal_tail_string)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z')(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z')(*strict*)
   apply(simp (no_asm_use) only: append_language_def kPrefix_def)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb d4 ec na d5 \<delta> e1 e2 z' a)(*strict*)
   apply(rule_tac
      x="a"
      in exI)
   apply(clarsimp)
   apply(simp add: kPrefix_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z')(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "u \<in> take SSk ` {r. \<exists>d e1 n. cfgSTD.derivation SSG d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = SSrenGAMMA\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf = liftB r\<rparr>)} " for SSk SSG SSrenGAMMA)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u)(*strict*)
   prefer 2
   apply(simp add: cfgSTD_first_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u)(*strict*)
  apply(subgoal_tac "\<exists>u'. \<exists>d e1 n. cfgSTD.derivation G' d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf = liftB u'\<rparr>) \<and> take k u'=u")
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb d4 ec na d5 \<delta> e1 e2 z' xa da e1a nb)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="da"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="e1a"
      in exI)
   apply(rule_tac
      x="nb"
      in exI)
   apply(clarsimp)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u)(*strict*)
  apply(thin_tac "u \<in> take k ` {r. \<exists>d e1 n. cfgSTD.derivation G' d \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf = liftB r\<rparr>)}")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "take k (u@z) = take k (u'@z)")
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
   prefer 2
   apply(rule_tac
      t="u"
      and s="take k u'"
      in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
   apply(rule_tac
      t="take k (take k u' @ z)"
      and s="take k (take k u') @ (take (k - (length (take k u'))) z)"
      in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
   apply(rule_tac
      t="take k (u' @ z)"
      and s="take k u' @ take (k - length (u')) z"
      in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
   apply(rule_tac
      t="take k (take k u')"
      and s="take k u'"
      in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
   apply(rule_tac
      t="k - length (take k u')"
      and s="k - length u'"
      in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u u' da e1a nb)(*strict*)
  apply(rename_tac u' u d6' e6' n6)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u' u d6' e6' n6)(*strict*)
  apply(subgoal_tac "take k (y @ [Do])=take k (u@z)")
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u' u d6' e6' n6)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u' u d6' e6' n6)(*strict*)
  apply(thin_tac "take k (y @ [Do]) = take k (u'@z)")
  apply(thin_tac "take k (u'@z) = take k (u@z)")
  apply(thin_tac "take k u=u'")
  apply(thin_tac "u' \<in> cfgSTD_first G' k \<beta>")
  apply(simp (no_asm_simp))
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
  apply(subgoal_tac "\<exists>d6 e6. cfgRM.derivation G' d6 \<and> maximum_of_domain d6 n6 \<and> d6 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>) \<and> d6 n6 = Some (pair e6 \<lparr>cfg_conf = liftB u\<rparr>)")
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
   prefer 2
   apply(rule cfg_derivation_can_be_translated_to_cfgRM_derivation)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
   apply(rule setA_liftB)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6)(*strict*)
  apply(thin_tac "cfgSTD.derivation G' d6'")
  apply(thin_tac "maximum_of_domain d6' n6")
  apply(thin_tac "d6' 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>)")
  apply(thin_tac "d6' n6 = Some (pair e6' \<lparr>cfg_conf = liftB u\<rparr>)")
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
  apply(erule conjE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
  apply(subgoal_tac "\<exists>d7 n7 e71 e72. cfgRM.derivation G' d7 \<and> maximum_of_domain d7 (Suc n7) \<and> d7 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>) \<and> d7 n7 = Some (pair e71 \<lparr>cfg_conf = teB Do # (ZSEQ @ teA B # liftB x1) @ (liftB u) @ z'\<rparr>) \<and> d7 (Suc n7) = Some (pair e72 \<lparr>cfg_conf = teB Do # (ZSEQ @ \<omega> @ liftB x1) @ (liftB u) @ z'\<rparr>)")
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
   prefer 2
    (*
d7:
  0 / / S'
  n7 / / $.ZSEQ.B.x1.u.z'
  n7+1 / / $.ZSEQ.\<omega>.x1.u.z'
d:
  0 / / XSEQ
  |\<pi>1| / eb / ZSEQ.B.x1
  |\<pi>1|+1 / (B,\<omega>) / ZSEQ.\<omega>.x1
d5:
  0 / / S'
  na+1 / e2 / $.XSEQ.\<beta>.z'
d6:
  0 / / \<beta>
  n6 / e6 / u
    construction:
f_1 := crop(d,|\<pi>1|)
  0 / / XSEQ
  |\<pi>1| / eb / ZSEQ.B.x1
f_2 := concatBoth(f_1,d6)
  0 / / XSEQ.\<beta>
  f2n / / ZSEQ.B.x1.u
f_3 := prepend($,f_2)
  0 / / $.XSEQ.\<beta>
  f2n / / $.ZSEQ.B.x1.u
f_4 := append(z',f_3)
  0 / / $.XSEQ.\<beta>.z'
  f2n / / $.ZSEQ.B.x1.u.z'
f_5 := concat(d5,f4)
  0 / / S'
  na+1 / / $.XSEQ.\<beta>.z'
  f2n+na+1 / / $.ZSEQ.B.x1.u.z'
f_6 := concat(f5,(B\<rightarrow>\<omega>))
  0 / / S'
  na+1 / / $.XSEQ.\<beta>.z'
  f2n+na+1 / / $.ZSEQ.B.x1.u.z'
  f2n+na+2 / / $.ZSEQ.\<omega>.x1.u.z'
*)
  (*f5 start*)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
  apply(subgoal_tac "\<exists>f5 n5 e5. cfgRM.derivation G' f5 \<and> maximum_of_domain f5 n5 \<and> f5 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>) \<and> f5 n5 = Some (pair e5 \<lparr>cfg_conf = (teB Do#((ZSEQ @ teA B # liftB x1) @ (liftB u)))@z'\<rparr>)")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
  prefer 2
  (*f4 start*)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
  apply(subgoal_tac "\<exists>f4 n4 e4. cfgRM.derivation G' f4 \<and> maximum_of_domain f4 n4 \<and> f4 0 = Some (pair None \<lparr>cfg_conf = (teB Do#(XSEQ@\<beta>))@z'\<rparr>) \<and> f4 n4 = Some (pair e4 \<lparr>cfg_conf = (teB Do#((ZSEQ @ teA B # liftB x1) @ (liftB u)))@z'\<rparr>)")
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
   prefer 2
  (*f3 start*)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
   apply(subgoal_tac "\<exists>f3 n3 e31. cfgRM.derivation G' f3 \<and> maximum_of_domain f3 n3 \<and> f3 0 = Some (pair None \<lparr>cfg_conf = teB Do#(XSEQ@\<beta>)\<rparr>) \<and> f3 n3 = Some (pair e31 \<lparr>cfg_conf = teB Do#((ZSEQ @ teA B # liftB x1) @ (liftB u))\<rparr>)")
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
    prefer 2
  (*f2 start*)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
    apply(subgoal_tac "\<exists>f2 n2 e2. cfgRM.derivation G' f2 \<and> maximum_of_domain f2 n2 \<and> f2 0 = Some (pair None \<lparr>cfg_conf = XSEQ@\<beta>\<rparr>) \<and> f2 n2 = Some (pair e2 \<lparr>cfg_conf = (ZSEQ @ teA B # liftB x1) @ (liftB u)\<rparr>)")
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
     prefer 2
  (*f1 start*)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
     apply(subgoal_tac "\<exists>f1 n1 e1. cfgRM.derivation G' f1 \<and> maximum_of_domain f1 n1 \<and> f1 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>) \<and> f1 n1 = Some (pair e1 \<lparr>cfg_conf = ZSEQ @ teA B # liftB x1\<rparr>)")
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
      prefer 2
      apply(rule_tac
    x="derivation_take d (length (\<pi>1))"
    in exI)
      apply(rule_tac
    x="length (\<pi>1)"
    in exI)
      apply(rule_tac
    x="eb"
    in exI)
      apply(rule conjI)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
       apply(rule_tac cfgRM.derivation_take_preserves_derivation)
       apply(rule_tac
    G="G"
    in F_CFG_AUGMENT__preserves_RMderivation)
           apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
           apply(simp add: AF_LR_PARSER_input_def)
          apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
          apply(simp add: AF_LR_PARSER_input_def)
         apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
         apply(simp add: AF_LR_PARSER_input_def)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
      apply(rule conjI)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
       apply(rule_tac
    m="Suc 0"
    in cfgRM.derivation_take_preserves_generates_maximum_of_domain)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
      apply(rule conjI)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
       apply(simp add: derivation_take_def)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
      apply(simp add: derivation_take_def)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
     apply(erule exE)+
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
     apply(erule conjE)+
  (*f1 end*)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
     apply(subgoal_tac "cfgRM.derivation_from_to G' (derivation_append (derivation_map d6 (\<lambda>v. \<lparr>cfg_conf = XSEQ @ cfg_conf v\<rparr>)) (derivation_map f1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ (liftB u)\<rparr>)) n6) {pair None \<lparr>cfg_conf = XSEQ @ \<beta>\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = (ZSEQ @ teA B # liftB x1) @ (liftB u)\<rparr>}")
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
      prefer 2
      apply(rule cfgRM_concatExtendIsFromToBoth)
           apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
           apply(force)
          apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
          apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
          apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a)(*strict*)
          apply(rule_tac
    x="n1"
    in exI)
          apply(simp add: maximum_of_domain_def)
         apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
         apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
         apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a)(*strict*)
         apply(rule_tac
    x="n6"
    in exI)
         apply(simp add: maximum_of_domain_def)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
        apply(rule setA_liftB)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f1 n1 e1a)(*strict*)
     apply(simp add: cfgRM.derivation_from_to_def cfgRM.derivation_from_def cfgRM.derivation_to_def)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a)(*strict*)
     apply(erule conjE)+
     apply(erule exE)+
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a nb)(*strict*)
     apply(erule conjE)+
     apply(erule exE)+
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a nb ya)(*strict*)
     apply(erule conjE)+
     apply(erule exE)+
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a nb ya xa)(*strict*)
     apply(rule_tac
    x="(derivation_append (derivation_map d6 (\<lambda>v. \<lparr>cfg_conf = XSEQ @ cfg_conf v\<rparr>)) (derivation_map f1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ liftB u\<rparr>)) n6)"
    in exI)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a nb ya xa)(*strict*)
     apply(rule conjI)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a nb ya xa)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a nb ya xa)(*strict*)
     apply(rule_tac
    x="nb"
    in exI)
     apply(rule conjI)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a nb ya xa)(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f1 n1 e1a nb ya xa)(*strict*)
     apply(simp add: derivation_append_def derivation_map_def)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
    apply(erule exE)+
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f2 n2 e2a)(*strict*)
    apply(erule conjE)+
  (*f2 end*)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f2 n2 e2a)(*strict*)
    apply(rule_tac
    x = "derivation_map f2 (\<lambda>v. \<lparr>cfg_conf = [teB Do]@(cfg_conf v)\<rparr>)"
    in exI)
    apply(rule_tac
    x="n2"
    in exI)
    apply(rule_tac
    x="e2a"
    in exI)
    apply(rule context_conjI)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f2 n2 e2a)(*strict*)
     apply(rule cfgRM.derivation_map_preserves_derivation2)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f2 n2 e2a)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f2 n2 e2a)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f2 n2 e2a)(*strict*)
     apply(clarsimp)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f2 n2 e2a a e b l r)(*strict*)
     apply(rule_tac
    x="teB Do#l"
    in exI)
     apply(rule_tac
    x="r"
    in exI)
     apply(clarsimp)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f2 n2 e2a)(*strict*)
    apply(rule context_conjI)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f2 n2 e2a)(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(blast)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f2 n2 e2a)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
   apply(erule exE)+
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f3 n3 e31)(*strict*)
   apply(erule conjE)+
  (*f3 end*)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f3 n3 e31)(*strict*)
   apply(rule_tac
    x = "derivation_map f3 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@z'\<rparr>)"
    in exI)
   apply(rule_tac
    x="n3"
    in exI)
   apply(rule_tac
    x="e31"
    in exI)
   apply(rule context_conjI)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f3 n3 e31)(*strict*)
    apply(rule cfgRM.derivation_map_preserves_derivation2)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f3 n3 e31)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f3 n3 e31)(*strict*)
    apply(simp add: cfgRM_step_relation_def)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f3 n3 e31)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f3 n3 e31 a e b l r)(*strict*)
    apply(rule_tac
    x="l"
    in exI)
    apply(rule_tac
    x="r@z'"
    in exI)
    apply(clarsimp)
    apply(simp (no_asm) only: setAConcat concat_asso)
    apply(clarsimp)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f3 n3 e31)(*strict*)
   apply(rule context_conjI)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f3 n3 e31)(*strict*)
    apply(rule derivation_map_preserves_maximum_of_domain)
    apply(blast)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f3 n3 e31)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
  apply(erule conjE)+
  (*f4 end*)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
  apply(rule_tac
    x="derivation_append d5 f4 (Suc na)"
    in exI)
  apply(rule_tac
    x="Suc na+n4"
    in exI)
  apply(rule_tac
    x="if (n4=0) then e2 else e4"
    in exI)
  apply(rule conjI)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
   apply(rule cfgRM.derivation_concat2)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
   apply(clarsimp)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
  apply(rule conjI)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
   apply(rule_tac concat_has_max_dom)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f4 n4 e4)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f4 n4 e4)(*strict*)
  apply(clarsimp)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(erule conjE)+
  (*f5 end*)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(rule_tac
    x="derivation_append f5 (der2 \<lparr>cfg_conf = (teB Do # (ZSEQ @ teA B # liftB x1) @ liftB u) @ z'\<rparr> \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr> \<lparr>cfg_conf = teB Do # (ZSEQ @ \<omega> @ liftB x1) @ liftB u @ z'\<rparr>) n5"
    in exI)
  apply(rule_tac
    x="n5"
    in exI)
  apply(rule_tac
    x="e5"
    in exI)
  apply(rule_tac
    x="Some \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr>"
    in exI)
  apply(rule context_conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(rule cfgRM.derivation_concat2)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
   apply(rule cfgRM.der2_is_derivation)
   apply(simp add: cfgRM_step_relation_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f5 n5 e5)(*strict*)
   apply(rule conjI)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f5 n5 e5)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_CFG_AUGMENT_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f5 n5 e5)(*strict*)
   apply(rule_tac
    x="teB Do#ZSEQ"
    in exI)
   apply(rule_tac
    x="liftB x1 @ liftB u @ z'"
    in exI)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f5 n5 e5)(*strict*)
   apply(simp (no_asm) only: setAConcat concat_asso)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f5 n5 e5)(*strict*)
    apply(rule setA_liftB_empty)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f5 n5 e5)(*strict*)
   apply(rule setA_liftB_empty)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v eb d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 f5 n5 e5)(*strict*)
  apply(simp add: der2_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(rule_tac
    t="Suc n5"
    and s="n5+Suc 0"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(rule_tac concat_has_max_dom)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(rule der2_maximum_of_domain)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 f5 n5 e5)(*strict*)
  apply(simp add: derivation_append_def der2_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(erule conjE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = \<omega>, cfg_item_rhs2 = [], cfg_item_look_ahead = take k (x1@y@[Do])\<rparr> \<in> valid_item_set G' k (teB Do#ZSEQ@\<omega>)")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  prefer 2
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    x="n7"
    in exI)
  apply(rule_tac
    x="d7"
    in exI)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    x="teB Do # ZSEQ"
    in exI)
  apply(rule_tac
    x="e71"
    in exI)
  apply(rule_tac
    x="e72"
    in exI)
  apply(rule_tac
    x="liftB x1 @ liftB u @ z'"
    in exI)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="take k x1 @ take (k - length x1) y @ take (k - (length x1 + length y)) [Do]"
    and s="take k (x1@y@[Do])"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="take k (liftB x1 @ liftB u @ z')"
    and s="take k (liftB x1 @ liftB u @ (liftB z))"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule_tac
    t="liftB z"
    and s="take k z'"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule_tac
    t="take k (liftB x1 @ liftB u @ z') = take k (liftB x1 @ liftB u @ take k z')"
    and s="take k ((liftB x1 @ liftB u) @ z') = take k ((liftB x1 @ liftB u) @ take k z')"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule take_shift)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="take k (x1 @ y @ [Do])"
    and s="take k (x1 @ (take k (y@[Do])))"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule take_shift)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="take k (y@[Do])"
    and s="take k (u@z)"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="take k (x1 @ take k (u @ z))"
    and s="take k (x1@u@z)"
    in subst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule take_shift)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="liftB x1 @ liftB u @ liftB z"
    and s="liftB (x1 @ u@z)"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(simp (no_asm) add: liftB_commutes_over_concat)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule take_liftB)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule order_antisym)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule setA_app)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule setA_liftB_subset)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule setA_app)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule setA_liftB_subset)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(thin_tac "valid_item G' k \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = z\<rparr>")
  apply(thin_tac "cfgRM.derivation G d")
  apply(thin_tac "maximum_of_domain d (Suc (length \<pi>1))")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = XSEQ\<rparr>)")
  apply(thin_tac "\<forall>YSEQ' YSEQt. YSEQ = YSEQ' @ [YSEQt] \<longrightarrow> YSEQt \<in> teA ` cfg_nonterminals G")
  apply(thin_tac "d (Suc (length \<pi>1)) = Some (pair (Some \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr>) \<lparr>cfg_conf = ZSEQ @ \<omega> @ liftB x1\<rparr>)")
  apply(thin_tac "d (length \<pi>1) = Some (pair eb \<lparr>cfg_conf = ZSEQ @ teA B # liftB x1\<rparr>)")
  apply(thin_tac "cfgRM.derivation G' d5")
  apply(thin_tac "d5 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
  apply(thin_tac "d5 na = Some (pair e1 \<lparr>cfg_conf = \<delta> @ teA A # z'\<rparr>)")
  apply(thin_tac "d5 (Suc na) = Some (pair e2 \<lparr>cfg_conf = \<delta> @ \<alpha> @ \<beta> @ z'\<rparr>)")
  apply(thin_tac "maximum_of_domain d5 (Suc na)")
  apply(thin_tac "cfgRM.derivation G' d6")
  apply(thin_tac "maximum_of_domain d6 n6")
  apply(thin_tac "d6 0 = Some (pair None \<lparr>cfg_conf = \<beta>\<rparr>)")
  apply(thin_tac "d6 n6 = Some (pair e6 \<lparr>cfg_conf = liftB u\<rparr>)")
  apply(thin_tac "cfgRM.derivation G' d7")
  apply(thin_tac "maximum_of_domain d7 (Suc n7)")
  apply(thin_tac "d7 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G')]\<rparr>)")
  apply(thin_tac "d7 n7 = Some (pair e71 \<lparr>cfg_conf = teB Do # (ZSEQ @ teA B # liftB x1) @ liftB u @ z'\<rparr>)")
  apply(thin_tac "d7 (Suc n7) = Some (pair e72 \<lparr>cfg_conf = teB Do # (ZSEQ @ \<omega> @ liftB x1) @ liftB u @ z'\<rparr>)")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = \<omega>, cfg_item_rhs2 = [], cfg_item_look_ahead = take k (x1@y@[Do])\<rparr> \<in> valid_item_set G' k (teB Do#YSEQ@liftB v)")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  prefer 2
  apply(rule_tac
    t="YSEQ@liftB v"
    and s="ZSEQ@\<omega>"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(subgoal_tac "\<exists>\<pi>' dP e. length \<pi>'=length v \<and> length (tau (parser_marker P) \<pi>') = 0 \<and> parserS.derivation P dP \<and> maximum_of_domain dP (length v) \<and> dP 0 = Some (pair None \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ))@[valid_item_set G' k (teB Do # YSEQ)],parserS_conf_scheduler=v@(x1@y)@[Do]\<rparr>) \<and> dP (length v) = Some (pair e \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) ((butlast (teB Do # YSEQ))) @[valid_item_set G' k (teB Do # YSEQ)] @(F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB v)), parserS_conf_scheduler=(x1@y)@[Do]\<rparr>) \<and> get_labels dP (length v) = \<pi>'")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  prefer 2
  apply(rule Lemma6__31)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
       apply(rule_tac
    x="liftB v"
    in viable_prefix_nonempty_on_every_prefix)
            apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
            apply(force)
           apply(simp add: AF_LR_PARSER_input_def)
           apply(force)
          apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
          prefer 2
          apply(force)
         apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
         apply(rule Fact6_12__1)
         apply(force)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
        apply(rule two_elements_construct_domain_setA)
        apply(rule viable_prefix_in_CFG)
         apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
         apply(force)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
        apply(rule Fact6_12__1)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
       apply(rule two_elements_construct_domain_setB)
       apply(rule viable_prefix_in_CFG)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
       apply(rule Fact6_12__1)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
      apply(rule Fact6_12__2)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="([] @ liftB (take k x1 @ take (k - length x1) y @ take (k - (length x1 + length y)) [Do]))"
    and s="liftB (take k (x1@y@[Do]))"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="cfgSTD_first G' k (liftB (take k (x1 @ y @ [Do])))"
    and s="{kPrefix SSk (filterB SSw)}" for SSk SSw
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule cfgSTD_first_on_terminal_string_is_kPrefix)
   apply(rule setA_liftB_empty)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(simp only: kPrefix_def)
  apply(rule_tac
    t="filterB (liftB (take k (x1 @ y @ [Do])))"
    and s="take k (x1@y@[Do])"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule liftBDeConv1)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="take k (take k (x1 @ y @ [Do]))"
    and s="(take (ord_class.min k k ) (x1 @ y @ [Do]))"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(rule take_take)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(rule_tac
    t="ord_class.min k k"
    and s="k"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(simp add: Lemma6__31_input_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v \<pi>1' d4 ec \<delta> z' u)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u)(*strict*)
  apply(rule_tac
    x="last YSEQ"
    in exI)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(erule conjE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(subgoal_tac "(\<lparr>rule_lpop= last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))# F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop=take k (x1@y@[Do]),rule_lpush=last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))#F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush=take k (x1@y@[Do])\<rparr>,Some\<lparr>prod_lhs=B,prod_rhs=\<omega>\<rparr>) \<in> AF_LR_PARSER__rules G G' M k")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  prefer 2
  apply(rule_tac
    A="{(\<lparr>rule_lpop=q#q_seq, rule_rpop=y,rule_lpush=[q,qA], rule_rpush=y\<rparr>,Some \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=(cfg_item_rhs1 I)@(cfg_item_rhs2 I)\<rparr>)| q q_seq I y qA. q \<in> epda_states M \<and> I \<in> q \<and> \<lparr>prod_lhs=cfg_item_lhs I,prod_rhs=cfg_item_rhs2 I\<rparr> \<in> cfg_productions G \<and> (cfg_item_rhs1 I=[]) \<and> qA \<in> (F_EPDA_GOTO M q (teA (cfg_item_lhs I))) \<and> q_seq \<in> (F_EPDA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) \<and> \<lparr>cfg_item_lhs=cfg_item_lhs I,cfg_item_rhs1=cfg_item_rhs2 I,cfg_item_rhs2=[],cfg_item_look_ahead=y\<rparr> \<in> last (q#q_seq)}"
    in set_mp)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(simp add: AF_LR_PARSER__rules_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) \<in> epda_states M")
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  prefer 2
  apply(rule_tac
    ?q0.0="epda_initial M"
    and w="(teB Do # ZSEQ)"
    in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
        apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule_tac
    t="teB Do # ZSEQ"
    and s="[teB Do] @ ZSEQ"
    in ssubst)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(subgoal_tac "length \<omega> = length (F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>)")
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  prefer 2
  apply(rule_tac
    w="\<omega>"
    and q="(last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)))"
    in F_DFA_GOTO_SEQUENCESound_main1)
       apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ liftB v))=valid_item_set G' k (teB Do # YSEQ @ liftB v)")
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  prefer 2
  apply(rule sym)
  apply(rule F_LR_MACHINE_all_SOUND_NotNil)
         apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule_tac
    t="teB Do # YSEQ @ liftB v"
    and s="[teB Do] @ YSEQ @ liftB v"
    in ssubst)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(rule set_concat_subset)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule set_concat_subset)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule liftB_lift)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule_tac
    t="teB Do # YSEQ @ liftB v"
    and s="[teB Do] @ YSEQ @ liftB v"
    in ssubst)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(rule set_concat_subset)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule set_concat_subset)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule liftB_lift)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))=valid_item_set G' k (teB Do # ZSEQ)")
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  prefer 2
  apply(rule sym)
  apply(rule F_LR_MACHINE_all_SOUND_NotNil)
         apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
         apply(force)
        apply(simp add: AF_LR_PARSER_input_def)
        apply(force)
       apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
       apply(simp add: AF_LR_PARSER_input_def)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule_tac
    t="teB Do # ZSEQ"
    and s="[teB Do] @ ZSEQ"
    in ssubst)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(rule set_concat_subset)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule_tac
    t="teB Do # ZSEQ"
    and s="[teB Do] @ ZSEQ"
    in ssubst)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(rule set_concat_subset)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    x="\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = [], cfg_item_rhs2 = [], cfg_item_look_ahead = take k x1 @ take (k - length x1) y @ take (k - (length x1 + length y)) [Do]\<rparr>"
    in exI)
  apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    x="F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ liftB v))) (teA B)"
    in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
      apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
   apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac \<pi>1 d YSEQ B x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(clarsimp)
  apply(rule_tac
    x="\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = [], cfg_item_rhs2 = \<omega>, cfg_item_look_ahead = take k x1 @ take (k - length x1) y @ take (k - (length x1 + length y)) [Do]\<rparr>"
    in exI)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    x="F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) (teA B)"
    in exI)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="\<omega>"
    and s="\<omega>@[]"
    in ssubst)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    v="\<omega>"
    in valid_item_set_shift_symbol_back_mult)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule F_DFA_GOTO_in_F_EPDA_GOTO_for_complete_DFA)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_in_F_EPDA_GOTO_SEQUENCE_for_complete_DFA)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="last (F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # ZSEQ)) \<omega>)"
    and s="valid_item_set G' k (teB Do # YSEQ @ liftB v)"
    in ssubst)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="valid_item_set G' k (teB Do # ZSEQ)"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))"
    in ssubst)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="valid_item_set G' k (teB Do # YSEQ @ liftB v)"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ liftB v))"
    in ssubst)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="YSEQ @ liftB v"
    and s="ZSEQ @ \<omega>"
    in ssubst)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule_tac
    t="teB Do # ZSEQ @ \<omega>"
    and s="(teB Do # ZSEQ) @ \<omega>"
    in ssubst)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_concat)
        apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
     apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(subgoal_tac "\<exists>d11. parserS.derivation P d11 \<and> maximum_of_domain d11 (Suc 0) \<and> d11 0 = Some (pair None \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#ZSEQ@\<omega>),parserS_conf_scheduler=x1@y@[Do]\<rparr>) \<and> d11 (Suc 0) = Some (pair (Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>) \<lparr>parserS_conf_stack=F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do#ZSEQ@[teA B]),parserS_conf_scheduler=x1@y@[Do]\<rparr>)")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  prefer 2
  apply(rule_tac
    x="der2 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ \<omega>), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr> \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr> \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ [teA B]), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>"
    in exI)
  apply(rule_tac
    t="YSEQ @ liftB v"
    and s="ZSEQ @ \<omega>"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="parserS_conf_stack \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ \<omega>), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ \<omega>)"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="rule_lpop \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="parserS_conf_stack \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ [teA B]), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ [teA B])"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="rule_lpush \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B]"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule parserS.der2_is_derivation)
  apply(simp only: parserS_step_relation_def)
  apply(rule conjI)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def AF_LR_PARSER_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v \<pi>1' d4 ec \<delta> z' u \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>"
    and s="(F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))]) @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B]"
    and s="(F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))]) @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B]"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="rule_lpop \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="rule_rpop \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>"
    and s="take k (x1 @ y @ [Do])"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="parserS_conf_stack \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ liftB v), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ liftB v)"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="rule_lpush \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>"
    and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B]"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="rule_rpush \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>"
    and s="take k (x1 @ y @ [Do])"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="parserS_conf_scheduler \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ [teA B]), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>"
    and s="x1 @ y @ [Do]"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="parserS_conf_stack \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ [teA B]), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ [teA B])"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="parserS_conf_scheduler \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ liftB v), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>"
    and s="x1 @ y @ [Do]"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule conjI)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   prefer 2
   apply(rule_tac
    x="drop k (x1@y@[Do])"
    in exI)
   apply(rule conjI)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(rule sym)
    apply(rule append_take_drop_id)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(rule sym)
   apply(rule append_take_drop_id)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    x="F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ))"
    in exI)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>"
    and s="(F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))]) @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B]"
    and s="(F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))]) @ F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B]"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # ZSEQ)) @ [last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))]"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(rule sym)
   apply(subgoal_tac "\<exists>w x. teB Do#ZSEQ=w@[x]")
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(erule exE)+
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
   apply(rule_tac
    t="teB Do#ZSEQ"
    and s="w@[xa]"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
   apply(rule_tac
    t="butlast(w@[xa])"
    and s="w"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
   apply(rule sym)
   apply(subgoal_tac "set (w@[xa]) \<subseteq> epda_events M")
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
    apply(rule F_DFA_GOTO_SEQUENCE_butlast_last)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
   apply(rule_tac
    t="w@[xa]"
    and s="[teB Do]@ZSEQ"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
   apply(rule set_concat_subset)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e w xa)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="YSEQ@liftB v"
    and s="ZSEQ @ \<omega>"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(thin_tac "ZSEQ @ \<omega> = YSEQ @ liftB v")
  apply(rule_tac
    t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))"
    and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(subgoal_tac "length (teB Do # ZSEQ) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))")
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    prefer 2
    apply(rule_tac
    w="(teB Do # ZSEQ)"
    and q="(epda_initial M)"
    in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
         apply(force)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
      apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(rule_tac
    t="teB Do # ZSEQ"
    and s="[teB Do]@ZSEQ"
    in ssubst)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(rule set_concat_subset)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule conjI)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(rule_tac
    t="teB Do # ZSEQ @ \<omega>"
    and s="(teB Do # ZSEQ) @ \<omega>"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_append_split)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(rule_tac
    t="teB Do # ZSEQ"
    and s="[teB Do]@ZSEQ"
    in ssubst)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(rule set_concat_subset)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="teB Do # ZSEQ @ [teA B]"
    and s="(teB Do # ZSEQ) @ [teA B]"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_append_split)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(rule_tac
    t="teB Do # ZSEQ"
    and s="[teB Do]@ZSEQ"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(rule set_concat_subset)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
   apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(rule der2_maximum_of_domain)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e)(*strict*)
  apply(simp add: der2_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e)(*strict*)
  apply(erule exE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(erule conjE)+
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    x="(\<pi>'@[Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>])@\<pi>1'"
    in exI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="tau (parser_marker P) ((\<pi>' @ [Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>]) @ \<pi>1')"
    and s="tau (parser_marker P) ((\<pi>' @ [Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>])) @ tau (parser_marker P) (\<pi>1')"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule tau_append_commutes)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="tau (parser_marker P) (\<pi>' @ [Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>])"
    and s="tau (parser_marker P) (\<pi>') @ tau (parser_marker P) [Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>]"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule tau_append_commutes)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="tau (parser_marker P) \<pi>'"
    and s="[]"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="tau (parser_marker P) \<pi>1'"
    and s="map Some \<pi>1"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="tau (parser_marker P) [Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>]"
    and s="[Some \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr>]"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule AF_LR_PARSER_apply_parser_marker)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule context_conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="length ((\<pi>' @ [Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>]) @ \<pi>1')"
    and s="Suc (length \<pi>1 + (length v + length x1))"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(thin_tac "length ((\<pi>' @ [Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>]) @ \<pi>1') = Suc (length \<pi>1 + (length v + length x1))")
  (*
d11:
  0 / SEQ($.ZSEQ.\<omega>) | x1.y.$
  1 / SEQ($.ZSEQ.B) | x1.y.$
d4:
  0 / SEQ($.ZSEQ.B) | x1.y.$
  |\<pi>1.x1| / SEQ($.XSEQ) | y.$
dP=d9:
  0 / SEQ($.YSEQ) | v.x1.y.$
  |v| / SEQ($.ZSEQ.\<omega>) | x1.y.$
??:
  0 / SEQ($.YSEQ) | v.x1.y.$
          / SEQ($.XSEQ) | y.$
    construction:
f_1 := concat(dP,d11)
  0 / SEQ($.YSEQ) | v.x1.y.$
  |v|+1 / SEQ($.ZSEQ.B) | x1.y.$
f_2 := concat(f_1,d4)
  0 / SEQ($.YSEQ) | v.x1.y.$
  |v|+1+|\<pi>1.x1| / SEQ($.ZSEQ) | y.$
*)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(subgoal_tac "\<exists>f1 e1. parserS.derivation P f1 \<and> maximum_of_domain f1 (length v+Suc 0) \<and> f1 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ), parserS_conf_scheduler = v @ x1 @ y @ [Do]\<rparr>) \<and> f1 (length v+Suc 0) = Some (pair e1 \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ [teA B]), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>) \<and> get_labels f1 (length v+Suc 0) =\<pi>' @ [Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>] ")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  prefer 2
  apply(rule_tac
    x="derivation_append dP d11 (length v)"
    in exI)
  apply(rule_tac
    x="Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr> "
    in exI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ)) @ [valid_item_set G' k (teB Do # YSEQ)] = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ)")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  prefer 2
  apply(rule F_DFA_GOTO_SEQUENCE_append_valid_item_set)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
       apply(force)
      apply(simp add: AF_LR_PARSER_input_def)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ)) @ [valid_item_set G' k (teB Do # YSEQ)] @ F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB v) = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ @ liftB v)")
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  prefer 2
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ)) @ [valid_item_set G' k (teB Do # YSEQ)] @ F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB v)"
    and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ)@F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB v)"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="teB Do # YSEQ @ liftB v"
    and s="(teB Do # YSEQ) @ liftB v"
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((teB Do # YSEQ) @ liftB v)"
    and s="F_DFA_GOTO_SEQUENCE SSM SSp SSw1 @ F_DFA_GOTO_SEQUENCE SSM (last (SSp # F_DFA_GOTO_SEQUENCE SSM SSp SSw1)) SSw2" for SSM SSp SSw1 SSw2
    in ssubst)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_append_split)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
        apply(force)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
    apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
     apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(rule_tac
    t="epda_events M"
    and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
    in ssubst)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
    apply(simp add: AF_LR_PARSER_input_def F_LR_MACHINE_def)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(rule liftB_lift)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(subgoal_tac "valid_item_set G' k (teB Do # YSEQ) = last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # YSEQ))")
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
          apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
          apply(force)
         apply(simp add: AF_LR_PARSER_input_def)
         apply(force)
        apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
        apply(simp add: AF_LR_PARSER_input_def)
       apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
       apply(force)
      apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
      apply(force)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule parserS.derivation_concat2)
     apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
     apply(force)
    apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
    apply(force)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac concat_has_max_dom)
   apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
   apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule conjI)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="get_labels (derivation_append dP d11 (length v)) (length v + Suc 0)"
    and s="get_labels dP (length v) @ (get_labels d11 (Suc 0))"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule derivation_append_preserves_get_labels)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="get_labels d11 (Suc 0)"
    and s="[Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>]"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(simp add: get_labels_def)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v \<pi>1' d4 ec \<delta> z' u \<pi>' dP e d11)(*strict*)
  apply(rule_tac
    t="nat_seq (Suc 0) (Suc 0)"
    and s="[Suc 0]"
    in ssubst)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v \<pi>1' d4 ec \<delta> z' u \<pi>' dP e d11)(*strict*)
  apply(rule natUptTo_n_n)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v \<pi>1' d4 ec \<delta> z' u \<pi>' dP e d11)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 d YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> z' u dP e d11)(*strict*)
  apply(simp add: get_label_def)
  (*f1 end*)
  apply(rename_tac r1 \<pi>1 n d YSEQ x B \<omega> n' ZSEQ x1 v eb \<pi>1' d4 ec na d5 \<delta> e1 e2 z' u d6' e6' n6 d6 e6 d7 n7 e71 e72 \<pi>' dP e d11)(*strict*)
  apply(thin_tac "AF_LR_PARSER_input G F Do S' G' M P k")
  apply(thin_tac "set XSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(thin_tac "set YSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(thin_tac "set y \<subseteq> cfg_events G")
  apply(thin_tac "n' = length \<pi>1")
  apply(thin_tac "filter (case_option False (\<lambda>x. True)) (get_labels d (Suc (length \<pi>1))) = List.rev (map Some \<pi>1) @ [Some \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr>]")
  apply(thin_tac "take k y @ take (k - length y) [Do] \<in> cfgSTD_first G' k (\<beta> @ liftB z)")
  apply(thin_tac "valid_cfg G'")
  apply(thin_tac "valid_dfa M")
  apply(thin_tac "some_step_from_every_configuration M")
  apply(thin_tac "cfg_events G \<subseteq> cfg_events G'")
  apply(thin_tac "teB Do \<in> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
  apply(thin_tac "two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
  apply(thin_tac "r1 = \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr>")
  apply(thin_tac "n = Suc (length \<pi>1)")
  apply(thin_tac "YSEQ @ liftB (v @ x1) = ZSEQ @ \<omega> @ liftB x1")
  apply(thin_tac "x = v @ x1")
  apply(thin_tac "ZSEQ @ \<omega> = YSEQ @ liftB v")
  apply(thin_tac "teA B \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(thin_tac "set \<omega> \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(thin_tac "set v \<subseteq> cfg_events G")
  apply(thin_tac "set x1 \<subseteq> cfg_events G")
  apply(thin_tac "set ZSEQ \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(thin_tac "tau (parser_marker P) \<pi>1' = map Some \<pi>1")
  apply(thin_tac "length \<pi>1' = length \<pi>1 + length x1")
  apply(thin_tac "\<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr> \<in> cfg_productions G")
  apply(thin_tac "set \<pi>1 \<subseteq> cfg_productions G")
  apply(thin_tac "take k z' = liftB z")
  apply(thin_tac "setA z' = {}")
  apply(thin_tac "take k (y @ [Do]) = take k (u @ z)")
  apply(thin_tac "\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = \<omega>, cfg_item_rhs2 = [], cfg_item_look_ahead = take k (x1 @ y @ [Do])\<rparr> \<in> valid_item_set G' k (teB Do # ZSEQ @ \<omega>)")
  apply(thin_tac "\<lparr>cfg_item_lhs = B, cfg_item_rhs1 = \<omega>, cfg_item_rhs2 = [], cfg_item_look_ahead = take k (x1 @ y @ [Do])\<rparr> \<in> valid_item_set G' k (teB Do # YSEQ @ liftB v)")
  apply(thin_tac "length \<pi>' = length v")
  apply(thin_tac "length (tau (parser_marker P) \<pi>') = 0")
  apply(thin_tac "parserS.derivation P dP")
  apply(thin_tac "maximum_of_domain dP (length v)")
  apply(thin_tac "dP 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ)) @ [valid_item_set G' k (teB Do # YSEQ)], parserS_conf_scheduler = v @ (x1 @ y) @ [Do]\<rparr>)")
  apply(thin_tac "dP (length v) = Some (pair e \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (teB Do # YSEQ)) @ [valid_item_set G' k (teB Do # YSEQ)] @ F_DFA_GOTO_SEQUENCE M (valid_item_set G' k (teB Do # YSEQ)) (liftB v), parserS_conf_scheduler = (x1 @ y) @ [Do]\<rparr>)")
  apply(thin_tac "get_labels dP (length v) = \<pi>'")
  apply(thin_tac "(\<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>, Some \<lparr>prod_lhs = B, prod_rhs = \<omega>\<rparr>) \<in> AF_LR_PARSER__rules G G' M k")
  apply(thin_tac "parserS.derivation P d11")
  apply(thin_tac "maximum_of_domain d11 (Suc 0)")
  apply(thin_tac "d11 0 = Some (pair None \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ \<omega>), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>)")
  apply(thin_tac "d11 (Suc 0) = Some (pair (Some \<lparr>rule_lpop = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) \<omega>, rule_rpop = take k (x1 @ y @ [Do]), rule_lpush = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ)) # F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ))) [teA B], rule_rpush = take k (x1 @ y @ [Do])\<rparr>) \<lparr>parserS_conf_stack = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # ZSEQ @ [teA B]), parserS_conf_scheduler = x1 @ y @ [Do]\<rparr>)")
  apply(clarsimp)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule_tac
    x="derivation_append f1 d4 (Suc (length v))"
    in exI)
  apply(rule conjI)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule parserS.derivation_concat2)
    apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule_tac
    t="(Suc (length \<pi>1 + (length v + length x1)))"
    and s="(Suc (length v))+(length \<pi>1 + length x1)"
    in ssubst)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule_tac concat_has_max_dom)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(force)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(simp add: derivation_append_def)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule conjI)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(simp add: derivation_append_def)
  apply(clarsimp)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule_tac
    t="get_labels (derivation_append f1 d4 (Suc (length v))) (Suc (length v) + (length \<pi>1 + length x1))"
    and s="get_labels f1 (Suc (length v)) @ (get_labels d4 (length \<pi>1 + length x1))"
    in ssubst)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(rule derivation_append_preserves_get_labels)
  apply(rename_tac \<pi>1 YSEQ B \<omega> ZSEQ x1 v d4 ec \<delta> \<pi>' f1 e1)(*strict*)
  apply(force)
  done

end
