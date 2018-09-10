section {*I\_kparser\_lemmas*}
theory
  I_kparser_lemmas

imports
  I_kparser_main

begin

lemma parserFS_parserHFS_conf_correspond1: "
  valid_parser G
  \<Longrightarrow> \<lparr>parserFS_conf_fixed=f1, parserFS_conf_stack = l1, parserFS_conf_scheduler=r1\<rparr> \<in> parserFS_configurations G
  \<Longrightarrow> \<lparr>parserHFS_conf_fixed=f1, parserHFS_conf_history=butlast_if_match f1 (parser_bottom G), parserHFS_conf_stack = l1, parserHFS_conf_scheduler=f1@r1\<rparr> \<in> parserHFS_configurations G"
  apply(simp add: parserHFS_configurations_def parserFS_configurations_def)
  apply(clarsimp)
  apply(simp add: prefix_def suffix_def)
  apply(simp add: parser_fixed_schedulers_def parser_unfixed_schedulers_def parser_schedulers_def suffix_closure_def suffix_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac vb vc c vd ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac vb vc c vd ca)(*strict*)
   apply (metis valid_parser_bottom_in_parser_events rotate_simps set_app_subset set_rotate1 set_take_head2 subset_trans)
  apply(rename_tac vb vc c vd ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac vb vc c vd ca)(*strict*)
   apply (metis valid_parser_bottom_in_parser_events rotate_simps set_append2 set_rotate1 set_take_head2 subset_trans)
  apply(rename_tac vb vc c vd ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac vb vc c vd ca)(*strict*)
   apply (metis (full_types) valid_parser_bottom_in_parser_events rotate_simps set_app_subset set_butlast_if_match_subset set_rotate1 set_take_head2 subset_trans)
  apply(rename_tac vb vc c vd ca)(*strict*)
  apply (metis butlast_if_match_take butlast_snoc in_set_takeD takePrecise)
  done

lemma parserFS_parserHFS_conf_correspond2: "
  valid_parser G
  \<Longrightarrow> \<lparr>parserHFS_conf_fixed=f1, parserHFS_conf_history=butlast_if_match f1 (parser_bottom G), parserHFS_conf_stack = l1, parserHFS_conf_scheduler=f1@r1\<rparr> \<in> parserHFS_configurations G
  \<Longrightarrow> \<lparr>parserFS_conf_fixed=f1, parserFS_conf_stack = l1, parserFS_conf_scheduler=r1\<rparr> \<in> parserFS_configurations G"
  apply(simp add: parserHFS_configurations_def parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(simp add: parser_fixed_schedulers_def parser_unfixed_schedulers_def parser_schedulers_def suffix_closure_def suffix_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac w c)(*strict*)
  apply(subgoal_tac "r1=c")
   apply(rename_tac w c)(*strict*)
   prefer 2
   apply (metis dropPrecise)
  apply(rename_tac w c)(*strict*)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(case_tac r1)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac w)(*strict*)
    apply(rule_tac
      x="w @ [parser_bottom G]"
      in exI)
    apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. r1 = w' @ [x']")
   apply(rename_tac w a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(thin_tac "r1 = a # list")
  apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply(rule conjI)
   apply(rename_tac w')(*strict*)
   apply(rule_tac
      x="f1 @ [parser_bottom G]"
      in exI)
   apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply(rule_tac
      x="w' @ [parser_bottom G]"
      in exI)
  apply(clarsimp)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead: "
  valid_parser M
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> parser_fixed_input_length_recN d m \<le> length (parserS_conf_scheduler c)"
  apply(induct m)
   apply(clarsimp)
  apply(rename_tac m)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc m)")
   apply(rename_tac m)(*strict*)
   apply(clarsimp)
  apply(rename_tac m a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d m = Some (pair e1 c1) \<and> d (Suc m) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
   apply(rename_tac m a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc m"
      in parserS.step_detail_before_some_position)
     apply(rename_tac m a)(*strict*)
     apply(force)
    apply(rename_tac m a)(*strict*)
    apply(force)
   apply(rename_tac m a)(*strict*)
   apply(force)
  apply(rename_tac m a)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1 e2 c1 c2)(*strict*)
  apply(case_tac c1)
  apply(rename_tac m e1 e2 c1 c2 parserS_conf_stack parserS_conf_schedulera)(*strict*)
  apply(rename_tac c1l c1r)
  apply(rename_tac m e1 e2 c1 c2 c1l c1r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac m e1 e2 c1 c2 c1l c1r parserS_conf_stack parserS_conf_schedulera)(*strict*)
  apply(rename_tac c2l c2r)
  apply(rename_tac m e1 e2 c1 c2 c1l c1r c2l c2r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac m e1 e2 c1 c2 c1l c1r c2l c2r rule_lpop rule_rpopa rule_lpush rule_rpusha)(*strict*)
  apply(rename_tac l1 r1 cons_l2 r2)
  apply(rename_tac m e1 e2 c1 c2 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(case_tac "parser_fixed_input_length_recN d m \<ge> (length r1)")
   apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
   apply(force)
  apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN d m) (length r1)"
      and s="length r1"
      in ssubst)
   apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
   apply(force)
  apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ (parserS_string_state \<lparr>parserS_conf_stack = x @ l1, parserS_conf_scheduler = r1 @ xa\<rparr>)")
   apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
   prefer 2
   apply(rule_tac
      j="m"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
        apply(force)
       apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
       apply(force)
      apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
      apply(force)
     apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
     apply(force)
    apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
    apply(force)
   apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
   apply(force)
  apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa w)(*strict*)
  apply(simp add: parserS_string_state_def)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_minimum: "
  valid_parser M
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> d (Suc m) = Some (pair (Some e) c)
  \<Longrightarrow> parser_fixed_input_length_recN d (Suc m) \<ge> length (rule_rpush e)"
  apply(clarsimp)
  apply(subgoal_tac "e \<in> parser_rules M")
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="Suc m"
      in allE)
   apply(clarsimp)
   apply(simp add: parser_step_labels_def)
  apply(subgoal_tac "length (rule_rpush e) \<le> length (rule_rpop e)")
   prefer 2
   apply(rule valid_parser_rules_rhs_gets_shorter)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(case_tac "(parser_fixed_input_length_recN d m) \<ge> (length (rule_rpop e))")
   apply(rule_tac
      t="max (parser_fixed_input_length_recN d m) (length (rule_rpop e))"
      and s="parser_fixed_input_length_recN d m"
      in ssubst)
    apply(force)
   prefer 2
   apply(rule_tac
      t="max (parser_fixed_input_length_recN d m) (length (rule_rpop e))"
      and s="length (rule_rpop e)"
      in ssubst)
    apply(force)
   apply(clarsimp)
  apply(arith)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_derivation: "
  valid_parser M
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead = parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast(parserS_conf_scheduler c)) (n - 1)@[parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.derivation M d'"
  apply(case_tac "parser_fixed_input_length_recN d m < length (parserS_conf_scheduler c')")
   apply(simp (no_asm_simp) add: parserS.derivation_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_map_def)
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(rename_tac n)
   apply(rename_tac n)(*strict*)
   apply(case_tac "d (Suc n)")
    apply(rename_tac n)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac n a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
    apply(rename_tac n a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
      apply(rename_tac n a)(*strict*)
      apply(force)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(simp add: derivation_map_def)
   apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ (parserS_string_state c1)")
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    prefer 2
    apply(rule_tac
      j="n"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c2)")
    apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
    prefer 2
    apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(subgoal_tac "m\<ge>Suc n")
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    prefer 2
    apply(rule parserS.allPreMaxDomSome_prime)
      apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    prefer 2
    apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 wa waa wb)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c' = w @ [parser_bottom M]")
    apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
    prefer 2
    apply(simp add: parserS.belongs_def)
    apply(erule_tac
      x="m"
      in allE)
    apply(clarsimp)
    apply(simp add: parserS_configurations_def)
    apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="butlast (wa @ wb @ wc @ [parser_bottom M])"
      and s="wa@wb@wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="wa @ wb @ wc @ [parser_bottom M]"
      and s="(wa @ wb @ wc) @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule butlast_snoc)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="butlast (wb @ wc @ [parser_bottom M])"
      and s="wb@wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="wb @ wc @ [parser_bottom M]"
      and s="(wb @ wc) @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule butlast_snoc)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="butn (wa @ wb @ wc) (length wc - parser_fixed_input_length_recN d m)"
      and s="wa@wb@butn wc (length wc - parser_fixed_input_length_recN d m)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="wa@wb@wc"
      and s="(wa@wb)@wc"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="wa @ wb @ butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="(wa @ wb) @ butn wc (length wc - parser_fixed_input_length_recN d m)"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule butn_shift)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="butn (wb @ wc) (length wc - parser_fixed_input_length_recN d m)"
      and s="wb@butn wc (length wc - parser_fixed_input_length_recN d m)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule butn_shift)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
   apply(case_tac xa)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN d m = Suc (length wc)")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     prefer 2
     apply(rule PARSER_UnseenPartStrictlyDecreases)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n) = 0")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "length (parserS_conf_scheduler c') - parser_fixed_input_length_recN d (Suc n + (m - Suc n)) \<le> length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="rule_rpop e2"
      and s="wa @ rule_rpush e2"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "wa @ rule_rpush e2 = rule_rpop e2")
    apply(clarsimp)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wb @ wc @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "wb @ wc @ [parser_bottom M] = rule_rpush e2")
    apply(clarsimp)
    apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c1)")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
   apply(thin_tac "xa=a#list")
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(rule_tac
      t="butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="take (parser_fixed_input_length_recN d m) wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(rule butn_take)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(subgoal_tac "\<exists>x. wb @ take (parser_fixed_input_length_recN d m) wc @ [parser_bottom M] = rule_rpush e2 @ x")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    prefer 2
    apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w' wd)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(subgoal_tac "prefix (rule_rpush e2) wd \<or> prefix wd (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(erule disjE)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "wc=ca@w'")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule_tac
      w="wd"
      in append_linj)
    apply(rule_tac
      t="wd@wc"
      and s="rule_rpush e2@w'"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "take (parser_fixed_input_length_recN d m) ca = ca")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
    apply(rule_tac
      x="take (parser_fixed_input_length_recN d m - length ca) w' @ [parser_bottom M]"
      in exI)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d m \<ge> length ca")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d (Suc n) \<ge> length (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule PARSER_UnseenPartStrictlyDecreases)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      c="length wd"
      in add_le_imp_le_right)
   apply(rule_tac
      t="length ca + length wd"
      and s="length(wd@ca)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      t="wd@ca"
      and s="rule_rpush e2"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      j="parser_fixed_input_length_recN d (Suc n)"
      in le_trans)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      a="length (parserS_conf_scheduler c')"
      and b="length (parserS_conf_scheduler c2)"
      in nat_le_step)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
         apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
   apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
   apply(simp (no_asm_use))
  apply(clarsimp)
  apply(simp add: butn_def)
  apply(rule_tac
      t="derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler := butlast (parserS_conf_scheduler c) @ [parser_bottom M]\<rparr>)"
      and s="d"
      in ssubst)
   apply(rule ext)
   apply(rename_tac x)(*strict*)
   apply(case_tac "d x")
    apply(rename_tac x)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
   apply(case_tac a)
   apply(rename_tac x a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x option b)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_conf_scheduler b = w @ [parser_bottom M]")
    apply(rename_tac x option b)(*strict*)
    prefer 2
    apply(simp add: parserS.belongs_def)
    apply(erule_tac
      x="x"
      in allE)
    apply(clarsimp)
    apply(simp add: parserS_configurations_def)
    apply(clarsimp)
   apply(rename_tac x option b)(*strict*)
   apply(clarsimp)
  apply(force)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_derivation_prime_prime: "
  valid_parser M
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead = parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast(parserS_conf_scheduler c)) (n - 1)@v@[parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parser_fixed_input_length_recN d m < length (parserS_conf_scheduler c')
  \<Longrightarrow> parserS.derivation M d'"
  apply(simp (no_asm_simp) add: parserS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac n)(*strict*)
  apply(case_tac "d (Suc n)")
   apply(rename_tac n)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
   apply(rename_tac n a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ (parserS_string_state c1)")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      j="n"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c2)")
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "m\<ge>Suc n")
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   prefer 2
   apply(rule parserS.allPreMaxDomSome_prime)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   prefer 2
   apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa waa wb)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c' = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="m"
      in allE)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wb @ wc @ [parser_bottom M])"
      and s="wa@wb@wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa @ wb @ wc @ [parser_bottom M]"
      and s="(wa @ wb @ wc) @ [parser_bottom M]"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butlast_snoc)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butlast (wb @ wc @ [parser_bottom M])"
      and s="wb@wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wb @ wc @ [parser_bottom M]"
      and s="(wb @ wc) @ [parser_bottom M]"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butlast_snoc)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb @ wc) (length wc - parser_fixed_input_length_recN d m)"
      and s="wa@wb@butn wc (length wc - parser_fixed_input_length_recN d m)"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa@wb@wc"
      and s="(wa@wb)@wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa @ wb @ butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="(wa @ wb) @ butn wc (length wc - parser_fixed_input_length_recN d m)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butn_shift)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butn (wb @ wc) (length wc - parser_fixed_input_length_recN d m)"
      and s="wb@butn wc (length wc - parser_fixed_input_length_recN d m)"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butn_shift)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
  apply(case_tac xa)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d m = Suc (length wc)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    prefer 2
    apply(rule PARSER_UnseenPartStrictlyDecreases)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(subgoal_tac "length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n) = 0")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(thin_tac "length (parserS_conf_scheduler c') - parser_fixed_input_length_recN d (Suc n + (m - Suc n)) \<le> length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n)")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="rule_rpop e2"
      and s="wa @ rule_rpush e2"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(thin_tac "wa @ rule_rpush e2 = rule_rpop e2")
   apply(clarsimp)
   apply(rule_tac
      t="rule_rpush e2"
      and s="wb @ wc @ [parser_bottom M]"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(thin_tac "wb @ wc @ [parser_bottom M] = rule_rpush e2")
   apply(clarsimp)
   apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c1)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
  apply(thin_tac "xa=a#list")
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
  apply(rule_tac
      t="butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="take (parser_fixed_input_length_recN d m) wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(rule butn_take)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
  apply(subgoal_tac "\<exists>x. wb @ take (parser_fixed_input_length_recN d m) wc @ v @ [parser_bottom M] = rule_rpush e2 @ x")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   prefer 2
   apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w' wd)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
  apply(subgoal_tac "prefix (rule_rpush e2) wd \<or> prefix wd (rule_rpush e2)")
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
  apply(erule disjE)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(subgoal_tac "wc=ca@w'")
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   prefer 2
   apply(rule_tac
      w="wd"
      in append_linj)
   apply(rule_tac
      t="wd@wc"
      and s="rule_rpush e2@w'"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(subgoal_tac "take (parser_fixed_input_length_recN d m) ca = ca")
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
   apply(rule_tac
      x="take (parser_fixed_input_length_recN d m - length ca) w' @ v @ [parser_bottom M]"
      in exI)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d m \<ge> length ca")
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d (Suc n) \<ge> length (rule_rpush e2)")
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   prefer 2
   apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   prefer 2
   apply(rule PARSER_UnseenPartStrictlyDecreases)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(rule_tac
      c="length wd"
      in add_le_imp_le_right)
  apply(rule_tac
      t="length ca + length wd"
      and s="length(wd@ca)"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(rule_tac
      t="wd@ca"
      and s="rule_rpush e2"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(rule_tac
      j="parser_fixed_input_length_recN d (Suc n)"
      in le_trans)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(rule_tac
      a="length (parserS_conf_scheduler c')"
      and b="length (parserS_conf_scheduler c2)"
      in nat_le_step)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
  apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
  apply(simp (no_asm_use))
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_derivation_prime: "
  valid_parser M
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead \<ge> parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast(parserS_conf_scheduler c)) (n - 1)@[parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.derivation M d'"
  apply(case_tac "parser_fixed_input_length_recN d m < length (parserS_conf_scheduler c')")
   apply(simp (no_asm_simp) add: parserS.derivation_def)
   apply(clarsimp)
   apply(rename_tac i)(*strict*)
   apply(case_tac i)
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_map_def)
   apply(rename_tac i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(rename_tac n)
   apply(rename_tac n)(*strict*)
   apply(case_tac "d (Suc n)")
    apply(rename_tac n)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac n a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
    apply(rename_tac n a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
      apply(rename_tac n a)(*strict*)
      apply(force)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(simp add: derivation_map_def)
   apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ (parserS_string_state c1)")
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    prefer 2
    apply(rule_tac
      j="n"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c2)")
    apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
    prefer 2
    apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(subgoal_tac "m\<ge>Suc n")
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    prefer 2
    apply(rule parserS.allPreMaxDomSome_prime)
      apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    prefer 2
    apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 wa waa wb)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c' = w @ [parser_bottom M]")
    apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
    prefer 2
    apply(simp add: parserS.belongs_def)
    apply(erule_tac
      x="m"
      in allE)
    apply(clarsimp)
    apply(simp add: parserS_configurations_def)
    apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="butlast (wa @ wb @ wc @ [parser_bottom M])"
      and s="wa@wb@wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="wa @ wb @ wc @ [parser_bottom M]"
      and s="(wa @ wb @ wc) @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule butlast_snoc)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="butlast (wb @ wc @ [parser_bottom M])"
      and s="wb@wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="wb @ wc @ [parser_bottom M]"
      and s="(wb @ wc) @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule butlast_snoc)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="butn (wa @ wb @ wc) (length wc - additionalOverhead)"
      and s="wa@wb@butn wc (length wc - additionalOverhead)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="wa@wb@wc"
      and s="(wa@wb)@wc"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="wa @ wb @ butn wc (length wc - additionalOverhead)"
      and s="(wa @ wb) @ butn wc (length wc - additionalOverhead)"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule butn_shift)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="butn (wb @ wc) (length wc - additionalOverhead)"
      and s="wb@butn wc (length wc - additionalOverhead)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule butn_shift)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(subgoal_tac "parserS_step_relation M (c1\<lparr>parserS_conf_scheduler := (wa @ wb @ butn wc (length wc - (parser_fixed_input_length_recN d m))) @ [parser_bottom M]\<rparr>) e2 (c2\<lparr>parserS_conf_scheduler := (wb @ butn wc (length wc - (parser_fixed_input_length_recN d m))) @ [parser_bottom M]\<rparr>)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(case_tac "parser_fixed_input_length_recN d m = additionalOverhead")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(rule_tac
      t="additionalOverhead"
      and s="parser_fixed_input_length_recN d m"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    prefer 2
    apply(thin_tac "parser_fixed_input_length_recN d m \<le> additionalOverhead")
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(simp add: parserS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
    apply(case_tac xa)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(subgoal_tac "parser_fixed_input_length_recN d m = Suc (length wc)")
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      prefer 2
      apply(rule PARSER_UnseenPartStrictlyDecreases)
          apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(subgoal_tac "length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n) = 0")
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(thin_tac "length (parserS_conf_scheduler c') - parser_fixed_input_length_recN d (Suc n + (m - Suc n)) \<le> length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n)")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="rule_rpop e2"
      and s="wa @ rule_rpush e2"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(thin_tac "wa @ rule_rpush e2 = rule_rpop e2")
     apply(clarsimp)
     apply(rule_tac
      t="rule_rpush e2"
      and s="wb @ wc @ [parser_bottom M]"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(thin_tac "wb @ wc @ [parser_bottom M] = rule_rpush e2")
     apply(clarsimp)
     apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c1)")
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
    apply(thin_tac "xa=a#list")
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(rule_tac
      t="butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="take (parser_fixed_input_length_recN d m) wc"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
     apply(rule butn_take)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(subgoal_tac "\<exists>x. wb @ take (parser_fixed_input_length_recN d m) wc @ [parser_bottom M] = rule_rpush e2 @ x")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
     prefer 2
     apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
          apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w' wd)(*strict*)
    apply(simp add: parserS_string_state_def)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    apply(subgoal_tac "prefix (rule_rpush e2) wd \<or> prefix wd (rule_rpush e2)")
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
     prefer 2
     apply(rule mutual_prefix_prefix)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    apply(erule disjE)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(subgoal_tac "wc=ca@w'")
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     prefer 2
     apply(rule_tac
      w="wd"
      in append_linj)
     apply(rule_tac
      t="wd@wc"
      and s="rule_rpush e2@w'"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(simp (no_asm_use))
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(subgoal_tac "take (parser_fixed_input_length_recN d m) ca = ca")
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
     apply(rule_tac
      x="take (parser_fixed_input_length_recN d m - length ca) w' @ [parser_bottom M]"
      in exI)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN d m \<ge> length ca")
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN d (Suc n) \<ge> length (rule_rpush e2)")
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     prefer 2
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     prefer 2
     apply(rule PARSER_UnseenPartStrictlyDecreases)
         apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule_tac
      c="length wd"
      in add_le_imp_le_right)
    apply(rule_tac
      t="length ca + length wd"
      and s="length(wd@ca)"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(simp (no_asm_use))
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule_tac
      t="wd@ca"
      and s="rule_rpush e2"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule_tac
      j="parser_fixed_input_length_recN d (Suc n)"
      in le_trans)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule_tac
      a="length (parserS_conf_scheduler c')"
      and b="length (parserS_conf_scheduler c2)"
      in nat_le_step)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
          apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
         apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(simp add: butn_def)
   apply(rule_tac
      t="derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler := butlast (parserS_conf_scheduler c) @ [parser_bottom M]\<rparr>)"
      and s="d"
      in ssubst)
    apply(rule ext)
    apply(rename_tac x)(*strict*)
    apply(case_tac "d x")
     apply(rename_tac x)(*strict*)
     apply(simp add: derivation_map_def)
    apply(rename_tac x a)(*strict*)
    apply(clarsimp)
    apply(simp add: derivation_map_def)
    apply(case_tac a)
    apply(rename_tac x a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac x option b)(*strict*)
    apply(subgoal_tac "\<exists>w. parserS_conf_scheduler b = w @ [parser_bottom M]")
     apply(rename_tac x option b)(*strict*)
     prefer 2
     apply(simp add: parserS.belongs_def)
     apply(erule_tac
      x="x"
      in allE)
     apply(clarsimp)
     apply(simp add: parserS_configurations_def)
     apply(clarsimp)
    apply(rename_tac x option b)(*strict*)
    apply(clarsimp)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d m<additionalOverhead")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(thin_tac "parser_fixed_input_length_recN d m \<le> additionalOverhead")
  apply(thin_tac "parser_fixed_input_length_recN d m \<noteq> additionalOverhead")
  apply(subgoal_tac "parserS_step_relation M c1 e2 c2")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(simp add: parserS.derivation_def)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(thin_tac "parserS_conf_stack c2 = xa @ rule_lpush e2")
  apply(thin_tac "parserS_conf_stack c1 = xa @ rule_lpop e2")
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c = w @ wa @ rule_rpush e2 @ xb")
   apply(simp only: parserS.belongs_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(simp add: parserS_configurations_def)
   apply(rename_tac n e1 e2 c1 c2 wa wb wc x xb)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c1 = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c1 = wa @ rule_rpush e2 @ xb")
   apply(simp add: parserS.belongs_def)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c2 = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c2 = rule_rpush e2 @ xb")
   apply(simp add: parserS.belongs_def)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   apply(erule_tac
      x="Suc n"
      in allE)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb we)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
  apply(subgoal_tac "\<exists>w. butn wc (length wc - additionalOverhead) = butn wc (length wc - parser_fixed_input_length_recN d m) @ w")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   prefer 2
   apply(simp add: butn_def)
   apply(case_tac "length wc - additionalOverhead")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="drop (parser_fixed_input_length_recN d m) wc"
      in exI)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length wc - Suc nat \<ge> parser_fixed_input_length_recN d m")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
   apply(rule_tac
      x="take ((length wc - Suc nat)-(parser_fixed_input_length_recN d m)) (drop (parser_fixed_input_length_recN d m) wc)"
      in exI)
   apply(rule take_mult_drop)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
  apply(erule_tac exE)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(rule_tac
      t="butn wc (length wc - additionalOverhead)"
      and s="butn wc (length wc - parser_fixed_input_length_recN d m) @ wd"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. wb @ butn wc (length wc - additionalOverhead) @ [parser_bottom M] = rule_rpush e2 @ x")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(case_tac "length wc - parser_fixed_input_length_recN d m")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat)(*strict*)
  apply(subgoal_tac "butn wc (length wc - parser_fixed_input_length_recN d m) = take (parser_fixed_input_length_recN d m) wc")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat)(*strict*)
   prefer 2
   apply(rule butn_take)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat)(*strict*)
  apply(clarsimp)
  apply(case_tac "\<exists>w. rule_rpush e2=w@[parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat we)(*strict*)
   apply(case_tac x)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat we)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat)(*strict*)
    apply(case_tac xb)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat)(*strict*)
     apply(subgoal_tac "wd=[]")
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat)(*strict*)
     apply(rule_tac
      w="wc"
      in take_max_no_append)
     apply(simp add: butn_def)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat a list)(*strict*)
    apply(thin_tac "xb=a#list")
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat w')(*strict*)
    apply(subgoal_tac "(parser_bottom M) \<in> set wc")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat w')(*strict*)
     apply(subgoal_tac "False")
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat w')(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat w')(*strict*)
     apply(simp add: parserS.belongs_def)
     apply(erule_tac
      x="n"
      in allE)
     apply(clarsimp)
     apply(simp add: parserS_configurations_def)
     apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat w')(*strict*)
    apply(rule_tac
      t="wc"
      and s="take (parser_fixed_input_length_recN d m) wc @ parser_bottom M # w'"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat w')(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat w')(*strict*)
    apply(simp (no_asm_use) only: set_append set_Cons)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat we a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. x = w' @ [x']")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat we a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat we a list)(*strict*)
   apply(thin_tac "x=a#list")
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat we w')(*strict*)
   apply(case_tac xb)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat we w')(*strict*)
    apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat we w' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat we w' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat we w' a list)(*strict*)
   apply(thin_tac "xb=a#list")
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat we w' w'a)(*strict*)
   apply(subgoal_tac "(parser_bottom M) \<in> set (wb@wc)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat we w' w'a)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat we w' w'a)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat we w' w'a)(*strict*)
    apply(simp add: parserS.belongs_def)
    apply(erule_tac
      x="n"
      in allE)
    apply(clarsimp)
    apply(simp add: parserS_configurations_def)
    apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat we w' w'a)(*strict*)
   apply(rule_tac
      t="wb@wc"
      and s="we @ parser_bottom M # w'a"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat we w' w'a)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc wd nat we w' w'a)(*strict*)
   apply(simp (no_asm_use) only: set_append set_Cons)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat)(*strict*)
  apply(clarsimp)
  apply(case_tac x)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat)(*strict*)
   apply(erule_tac
      x="wb @ take (parser_fixed_input_length_recN d m) wc"
      in allE)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. x = w' @ [x']")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd nat a list)(*strict*)
  apply(thin_tac "x=a#list")
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat w')(*strict*)
  apply(rule_tac
      t="wb @ take (parser_fixed_input_length_recN d m) wc @ wd @ [parser_bottom M]"
      and s="(wb @ take (parser_fixed_input_length_recN d m) wc) @ wd @ [parser_bottom M]"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat w')(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat w')(*strict*)
  apply(rule_tac
      t="wb @ take (parser_fixed_input_length_recN d m) wc"
      and s="rule_rpush e2 @ w'"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat w')(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc xb wd nat w')(*strict*)
  apply(rule_tac
      x="w' @ wd @ [parser_bottom M]"
      in exI)
  apply(force)
  done

lemma help_lemma2: "
  Om < Suc (length ca + length w')
  \<Longrightarrow> Om < additionalOverhead
  \<Longrightarrow> length ((wb @ ca)) \<le> On + length ((wb @ ca)) - length (wa @ (wb @ ca))
  \<Longrightarrow> Suc (length ca + length w') - Om \<le> Suc (length wb + (length ca + length w') + length ((wa @ (wb @ ca)))) - (On + length ((wb @ ca)))
  \<Longrightarrow> length ((wb @ ca)) \<le> length ((wa @ (wb @ ca)))
  \<Longrightarrow> length ((wa @ (wb @ ca))) \<le> On
  \<Longrightarrow> length ca \<le> Om"
  apply(force)
  done

lemma help_lemma3: "
  Om < Suc (length ca + length w')
  \<Longrightarrow> Om < additionalOverhead
  \<Longrightarrow> Suc (length ca + length w') - Om \<le> Suc (length wb + (length ca + length w')) - length (wb @ ca)
  \<Longrightarrow> length ca \<le> Om"
  apply(force)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_derivation_prime_prime_prime: "
  valid_parser M
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> \<not> parser_observes_input_terminator M
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead \<ge> parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast(parserS_conf_scheduler c)) (n - 1)@MARK@[parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parser_fixed_input_length_recN d m < length (parserS_conf_scheduler c')
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.derivation M d'"
  apply(simp (no_asm_simp) add: parserS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac n)(*strict*)
  apply(case_tac "d (Suc n)")
   apply(rename_tac n)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
   apply(rename_tac n a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ (parserS_string_state c1)")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      j="n"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c2)")
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "m\<ge>Suc n")
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   prefer 2
   apply(rule parserS.allPreMaxDomSome_prime)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   prefer 2
   apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa waa wb)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c' = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="m"
      in allE)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wb @ wc @ [parser_bottom M])"
      and s="wa@wb@wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa @ wb @ wc @ [parser_bottom M]"
      and s="(wa @ wb @ wc) @ [parser_bottom M]"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butlast_snoc)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butlast (wb @ wc @ [parser_bottom M])"
      and s="wb@wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wb @ wc @ [parser_bottom M]"
      and s="(wb @ wc) @ [parser_bottom M]"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butlast_snoc)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb @ wc) (length wc - additionalOverhead)"
      and s="wa@wb@butn wc (length wc - additionalOverhead)"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa@wb@wc"
      and s="(wa@wb)@wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa @ wb @ butn wc (length wc - additionalOverhead)"
      and s="(wa @ wb) @ butn wc (length wc - additionalOverhead)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butn_shift)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butn (wb @ wc) (length wc - additionalOverhead)"
      and s="wb@butn wc (length wc - additionalOverhead)"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butn_shift)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(subgoal_tac "parserS_step_relation M (c1\<lparr>parserS_conf_scheduler := (wa @ wb @ butn wc (length wc - (parser_fixed_input_length_recN d m))) @ MARK@ [parser_bottom M]\<rparr>) e2 (c2\<lparr>parserS_conf_scheduler := (wb @ butn wc (length wc - (parser_fixed_input_length_recN d m))) @ MARK@[parser_bottom M]\<rparr>)")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(case_tac "parser_fixed_input_length_recN d m = additionalOverhead")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="additionalOverhead"
      and s="parser_fixed_input_length_recN d m"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(thin_tac "parser_fixed_input_length_recN d m \<le> additionalOverhead")
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
   apply(case_tac xa)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN d m = Suc (length wc)")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     prefer 2
     apply(rule PARSER_UnseenPartStrictlyDecreases)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n) = 0")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "length (parserS_conf_scheduler c') - parser_fixed_input_length_recN d (Suc n + (m - Suc n)) \<le> length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="rule_rpop e2"
      and s="wa @ rule_rpush e2"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "wa @ rule_rpush e2 = rule_rpop e2")
    apply(clarsimp)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wb @ wc @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "wb @ wc @ [parser_bottom M] = rule_rpush e2")
    apply(clarsimp)
    apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c1)")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
   apply(thin_tac "xa=a#list")
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(rule_tac
      t="butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="take (parser_fixed_input_length_recN d m) wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(rule butn_take)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(subgoal_tac "\<exists>x. wb @ take (parser_fixed_input_length_recN d m) wc @ MARK @[parser_bottom M] = rule_rpush e2 @ x")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    prefer 2
    apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w' wd)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(subgoal_tac "prefix (rule_rpush e2) wd \<or> prefix wd (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(erule disjE)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "wc=ca@w'")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule_tac
      w="wd"
      in append_linj)
    apply(rule_tac
      t="wd@wc"
      and s="rule_rpush e2@w'"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "take (parser_fixed_input_length_recN d m) ca = ca")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
    apply(rule_tac
      x="take (parser_fixed_input_length_recN d m - length ca) w' @ MARK @ [parser_bottom M]"
      in exI)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d m \<ge> length ca")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d (Suc n) \<ge> length (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule PARSER_UnseenPartStrictlyDecreases)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      c="length wd"
      in add_le_imp_le_right)
   apply(rule_tac
      t="length ca + length wd"
      and s="length(wd@ca)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      t="wd@ca"
      and s="rule_rpush e2"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      j="parser_fixed_input_length_recN d (Suc n)"
      in le_trans)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      a="length (parserS_conf_scheduler c')"
      and b="length (parserS_conf_scheduler c2)"
      in nat_le_step)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
         apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
   apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d m<additionalOverhead")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(thin_tac "parser_fixed_input_length_recN d m \<le> additionalOverhead")
  apply(thin_tac "parser_fixed_input_length_recN d m \<noteq> additionalOverhead")
  apply(subgoal_tac "parserS_step_relation M c1 e2 c2")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(simp add: parserS.derivation_def)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(thin_tac "parserS_conf_stack c2 = xa @ rule_lpush e2")
  apply(thin_tac "parserS_conf_stack c1 = xa @ rule_lpop e2")
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c = w @ wa @ rule_rpush e2 @ xb")
   apply(simp only: parserS.belongs_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(simp add: parserS_configurations_def)
   apply(rename_tac n e1 e2 c1 c2 wa wb wc x xb)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c1 = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c1 = wa @ rule_rpush e2 @ xb")
   apply(simp add: parserS.belongs_def)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c2 = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c2 = rule_rpush e2 @ xb")
   apply(simp add: parserS.belongs_def)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   apply(erule_tac
      x="Suc n"
      in allE)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb we)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
  apply(subgoal_tac "\<exists>w. butn wc (length wc - additionalOverhead) = butn wc (length wc - parser_fixed_input_length_recN d m) @ w")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   prefer 2
   apply(simp add: butn_def)
   apply(case_tac "length wc - additionalOverhead")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="drop (parser_fixed_input_length_recN d m) wc"
      in exI)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length wc - Suc nat \<ge> parser_fixed_input_length_recN d m")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
   apply(rule_tac
      x="take ((length wc - Suc nat)-(parser_fixed_input_length_recN d m)) (drop (parser_fixed_input_length_recN d m) wc)"
      in exI)
   apply(rule take_mult_drop)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
  apply(erule_tac exE)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(rule_tac
      t="butn wc (length wc - additionalOverhead)"
      and s="butn wc (length wc - parser_fixed_input_length_recN d m) @ wd"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. wb @ butn wc (length wc - additionalOverhead) @ MARK@[parser_bottom M] = rule_rpush e2 @ x")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(case_tac "\<exists>w. rule_rpush e2=w@[parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(simp add: parser_observes_input_terminator_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
   apply(erule_tac
      x="e2"
      in ballE)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
    apply(subgoal_tac "parser_bottom M \<in> set (rule_rpop e2)")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
    apply(rule_tac
      t="rule_rpop e2"
      and s="wa @ we @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
    apply(simp (no_asm_use) only: set_append set_Cons)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(clarsimp)
  apply(case_tac xb)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd a list)(*strict*)
  apply(thin_tac "xb=a#list")
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
  apply(subgoal_tac "\<exists>w'. wb @ butn wc (length wc - parser_fixed_input_length_recN d m) = rule_rpush e2 @ w'")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' w'a)(*strict*)
   apply(rule_tac
      x="w'a @ wd@MARK@[parser_bottom M]"
      in exI)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
  apply(rule_tac
      t="butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="take (parser_fixed_input_length_recN d m) wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
   apply(rule butn_take)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
  apply(subgoal_tac "prefix (rule_rpush e2) wb \<or> prefix wb (rule_rpush e2)")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
   apply(erule disjE)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
    apply(simp add: prefix_def)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "wc=ca@w'")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    prefer 2
    apply(rule_tac
      w="wb"
      in append_linj)
    apply(rule_tac
      t="wb@wc"
      and s="rule_rpush e2 @ w'"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wb@ca"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(rule_tac
      t="rule_rpush e2"
      and s="wb@ca"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "\<exists>w'. take (parser_fixed_input_length_recN d m) wc = ca @ w'")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(erule exE)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca w'a)(*strict*)
    apply(rule_tac
      x="w'a"
      in exI)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d (Suc n) \<ge> length (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    prefer 2
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m-Suc n)))")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    prefer 2
    apply(rule PARSER_UnseenPartStrictlyDecreases)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d m \<ge> length ca")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "length (rule_rpop e2) \<ge> length (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
    apply(case_tac "(parser_fixed_input_length_recN d n) \<ge> (length (rule_rpop e2))")
     apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
     apply(subgoal_tac "max (parser_fixed_input_length_recN d n) (length (rule_rpop e2)) = (parser_fixed_input_length_recN d n)")
      apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      wb="wb"
      and wa="wa"
      and On="parser_fixed_input_length_recN d n"
      in help_lemma2)
          apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
    apply(subgoal_tac "max (parser_fixed_input_length_recN d n) (length (rule_rpop e2)) = (length (rule_rpop e2))")
     apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      wb="wb"
      in help_lemma3)
      apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(rule_tac
      t="rule_rpop e2"
      and s="wa@rule_rpush e2"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

lemma PARSER_not_seen_entire_not_read_bottom: "
  valid_parser M
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> n>0
  \<Longrightarrow> d n = Some (pair (Some e) c)
  \<Longrightarrow> parser_fixed_input_length_recN d n < length(parserS_conf_scheduler c)
  \<Longrightarrow> parser_bottom M \<notin> set (rule_rpush e)"
  apply(case_tac "parser_bottom M \<notin> set (rule_rpush e)")
   apply(force)
  apply(subgoal_tac "parser_fixed_input_length_recN d n = length(parserS_conf_scheduler c)")
   apply(force)
  apply(thin_tac "parser_fixed_input_length_recN d n < length (parserS_conf_scheduler c)")
  apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c)")
   prefer 2
   apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule order_antisym)
   apply(force)
  apply(thin_tac "parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c)")
  apply(case_tac n)
   apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 c1)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d nat \<le> length (parserS_conf_scheduler c1)")
   apply(rename_tac nat e1 c1)(*strict*)
   prefer 2
   apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(rename_tac nat e1 c1)(*strict*)
      apply(force)
     apply(rename_tac nat e1 c1)(*strict*)
     apply(force)
    apply(rename_tac nat e1 c1)(*strict*)
    apply(force)
   apply(rename_tac nat e1 c1)(*strict*)
   apply(force)
  apply(rename_tac nat e1 c1)(*strict*)
  apply(subgoal_tac "c \<in> parserS_configurations M")
   apply(rename_tac nat e1 c1)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
  apply(rename_tac nat e1 c1)(*strict*)
  apply(subgoal_tac "c1 \<in> parserS_configurations M")
   apply(rename_tac nat e1 c1)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="nat"
      in allE)
   apply(clarsimp)
  apply(rename_tac nat e1 c1)(*strict*)
  apply(subgoal_tac "valid_parser_step_label M e")
   apply(rename_tac nat e1 c1)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="Suc nat"
      in allE)
   apply(clarsimp)
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(erule_tac
      x="e"
      in ballE)
    apply(rename_tac nat e1 c1)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat e1 c1)(*strict*)
   apply(simp add: parser_step_labels_def)
  apply(rename_tac nat e1 c1)(*strict*)
  apply(simp add: parserS_configurations_def valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
  apply(subgoal_tac "length (kPrefix k (w @ [parser_bottom M])) \<ge> length (rule_rpush e)")
   apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
   prefer 2
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom M])"
      and s="xa @ rule_rpush e"
      in ssubst)
    apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (parserS_conf_scheduler \<lparr>parserS_conf_stack = la, parserS_conf_scheduler = wb @ [parser_bottom M]\<rparr>) - (parser_fixed_input_length_recN d nat) \<ge> length (parserS_conf_scheduler \<lparr>parserS_conf_stack = l, parserS_conf_scheduler = wa @ [parser_bottom M]\<rparr>) - (parser_fixed_input_length_recN d (nat+(Suc 0)))")
   apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
   prefer 2
   apply(rule PARSER_UnseenPartStrictlyDecreases)
       apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
       apply(force)
      apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
      apply(force)
     apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
  apply(clarsimp)
  apply(simp add: kPrefix_def)
  apply(subgoal_tac "parser_fixed_input_length_recN d (Suc nat) \<ge> length (rule_rpush e)")
   apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
   prefer 2
   apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
      apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
      apply(force)
     apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 l la k w wa wb xa)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
  apply(case_tac "k-length w")
   apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "min (length w) k = k")
    apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
    prefer 2
    apply(rule Orderings.min_absorb2)
    apply(force)
   apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (rule_rpush e@xb) = Suc (length wa)")
    apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
    prefer 2
    apply(rule_tac
      t="rule_rpush e@xb"
      and s="wa @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
     apply(force)
    apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
   apply(case_tac xb)
    apply(rename_tac nat e1 k w wa wb xa x xb)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat e1 k w wa wb xa x xb a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
    apply(rename_tac nat e1 k w wa wb xa x xb a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac nat e1 k w wa wb xa x xb a list)(*strict*)
   apply(thin_tac "xb=a#list")
   apply(clarsimp)
  apply(rename_tac nat e1 k w wa wb xa x xb nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 k w wa wb xa x xb nata xc)(*strict*)
  apply(case_tac xb)
   apply(rename_tac nat e1 k w wa wb xa x xb nata xc)(*strict*)
   prefer 2
   apply(rename_tac nat e1 k w wa wb xa x xb nata xc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
    apply(rename_tac nat e1 k w wa wb xa x xb nata xc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac nat e1 k w wa wb xa x xb nata xc a list)(*strict*)
   apply(thin_tac "xb=a#list")
   apply(clarsimp)
  apply(rename_tac nat e1 k w wa wb xa x xb nata xc)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
  apply(subgoal_tac "min (length w) k = length w")
   apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
   prefer 2
   apply(rule Orderings.min_absorb1)
   apply(rule length_diff)
   apply(force)
  apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
  apply(clarsimp)
  apply(case_tac "(parser_fixed_input_length_recN d nat) \<ge> (Suc (length w))")
   apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
   apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) (Suc (length w))=(parser_fixed_input_length_recN d nat)")
    apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) (Suc (length w))=Suc (length w)")
   apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "xa@wa=w")
   apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
   prefer 2
   apply(rule_tac
      v="[parser_bottom M]"
      in append_injr)
   apply(clarsimp)
  apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
  apply(rule_tac
      t="Suc(length wa)"
      and s="length(wa@[parser_bottom M])"
      in ssubst)
   apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
  apply(rule_tac
      t="wa@[parser_bottom M]"
      and s="rule_rpush e"
      in ssubst)
   apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
   apply(force)
  apply(rename_tac nat e1 k w wa xa x nata xc)(*strict*)
  apply(force)
  done

lemma PARSER_not_seen_entire_shifts_back: "
  valid_parser P
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> parser_fixed_input_length_recN d n < length (parserS_conf_scheduler cn)
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d n = Some (pair en cn)
  \<Longrightarrow> i\<le>n
  \<Longrightarrow> parser_fixed_input_length_recN d i < length (parserS_conf_scheduler ci)"
  apply(subgoal_tac "length (parserS_conf_scheduler ci) - (parser_fixed_input_length_recN d i) \<ge> length (parserS_conf_scheduler cn) - (parser_fixed_input_length_recN d (i+(n-i)))")
   prefer 2
   apply(rule PARSER_UnseenPartStrictlyDecreases)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(force)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_derivation_prime_prime_prime_prime: "
  valid_parser M
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead \<ge> parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast(parserS_conf_scheduler c)) (n - 1)@MARK@[parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parser_fixed_input_length_recN d m < length (parserS_conf_scheduler c')
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.derivation M d'"
  apply(simp (no_asm_simp) add: parserS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac n)(*strict*)
  apply(case_tac "d (Suc n)")
   apply(rename_tac n)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
   apply(rename_tac n a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ (parserS_string_state c1)")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule_tac
      j="n"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c2)")
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "m\<ge>Suc n")
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   prefer 2
   apply(rule parserS.allPreMaxDomSome_prime)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   prefer 2
   apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 wa waa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 wa waa wb)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c' = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
   apply(erule_tac
      x="m"
      in allE)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wb @ wc @ [parser_bottom M])"
      and s="wa@wb@wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa @ wb @ wc @ [parser_bottom M]"
      and s="(wa @ wb @ wc) @ [parser_bottom M]"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butlast_snoc)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butlast (wb @ wc @ [parser_bottom M])"
      and s="wb@wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wb @ wc @ [parser_bottom M]"
      and s="(wb @ wc) @ [parser_bottom M]"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butlast_snoc)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb @ wc) (length wc - additionalOverhead)"
      and s="wa@wb@butn wc (length wc - additionalOverhead)"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa@wb@wc"
      and s="(wa@wb)@wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule_tac
      t="wa @ wb @ butn wc (length wc - additionalOverhead)"
      and s="(wa @ wb) @ butn wc (length wc - additionalOverhead)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butn_shift)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(rule_tac
      t="butn (wb @ wc) (length wc - additionalOverhead)"
      and s="wb@butn wc (length wc - additionalOverhead)"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(rule butn_shift)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(subgoal_tac "parserS_step_relation M (c1\<lparr>parserS_conf_scheduler := (wa @ wb @ butn wc (length wc - (parser_fixed_input_length_recN d m))) @ MARK@ [parser_bottom M]\<rparr>) e2 (c2\<lparr>parserS_conf_scheduler := (wb @ butn wc (length wc - (parser_fixed_input_length_recN d m))) @ MARK@[parser_bottom M]\<rparr>)")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(case_tac "parser_fixed_input_length_recN d m = additionalOverhead")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(rule_tac
      t="additionalOverhead"
      and s="parser_fixed_input_length_recN d m"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(thin_tac "parser_fixed_input_length_recN d m \<le> additionalOverhead")
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
   apply(case_tac xa)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN d m = Suc (length wc)")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     prefer 2
     apply(rule PARSER_UnseenPartStrictlyDecreases)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n) = 0")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "length (parserS_conf_scheduler c') - parser_fixed_input_length_recN d (Suc n + (m - Suc n)) \<le> length (parserS_conf_scheduler c2) - parser_fixed_input_length_recN d (Suc n)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="rule_rpop e2"
      and s="wa @ rule_rpush e2"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "wa @ rule_rpush e2 = rule_rpop e2")
    apply(clarsimp)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wb @ wc @ [parser_bottom M]"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(thin_tac "wb @ wc @ [parser_bottom M] = rule_rpush e2")
    apply(clarsimp)
    apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c1)")
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa a list)(*strict*)
   apply(thin_tac "xa=a#list")
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(rule_tac
      t="butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="take (parser_fixed_input_length_recN d m) wc"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(rule butn_take)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(subgoal_tac "\<exists>x. wb @ take (parser_fixed_input_length_recN d m) wc @ MARK @[parser_bottom M] = rule_rpush e2 @ x")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_string_state c2 = w @ (parserS_string_state c')")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    prefer 2
    apply(rule_tac
      j="m - Suc n"
      in parserS.derivation_monotonically_dec)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w')(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x w' wd)(*strict*)
   apply(simp add: parserS_string_state_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(subgoal_tac "prefix (rule_rpush e2) wd \<or> prefix wd (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(erule disjE)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "wc=ca@w'")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule_tac
      w="wd"
      in append_linj)
    apply(rule_tac
      t="wd@wc"
      and s="rule_rpush e2@w'"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "take (parser_fixed_input_length_recN d m) ca = ca")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
    apply(rule_tac
      x="take (parser_fixed_input_length_recN d m - length ca) w' @ MARK @ [parser_bottom M]"
      in exI)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d m \<ge> length ca")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d (Suc n) \<ge> length (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m - Suc n)))")
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    prefer 2
    apply(rule PARSER_UnseenPartStrictlyDecreases)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      c="length wd"
      in add_le_imp_le_right)
   apply(rule_tac
      t="length ca + length wd"
      and s="length(wd@ca)"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      t="wd@ca"
      and s="rule_rpush e2"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      j="parser_fixed_input_length_recN d (Suc n)"
      in le_trans)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(rule_tac
      a="length (parserS_conf_scheduler c')"
      and b="length (parserS_conf_scheduler c2)"
      in nat_le_step)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
         apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(rule_tac
      t="m"
      and s="Suc n + (m - Suc n)"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wc x w' wd ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
   apply(rule_tac
      t="rule_rpush e2"
      and s="wd@ca"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa x w' wd ca)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d m<additionalOverhead")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(thin_tac "parser_fixed_input_length_recN d m \<le> additionalOverhead")
  apply(thin_tac "parser_fixed_input_length_recN d m \<noteq> additionalOverhead")
  apply(subgoal_tac "parserS_step_relation M c1 e2 c2")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
   prefer 2
   apply(simp add: parserS.derivation_def)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(thin_tac "parserS_conf_stack c2 = xa @ rule_lpush e2")
  apply(thin_tac "parserS_conf_stack c1 = xa @ rule_lpop e2")
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c = w @ wa @ rule_rpush e2 @ xb")
   apply(simp only: parserS.belongs_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(simp add: parserS_configurations_def)
   apply(rename_tac n e1 e2 c1 c2 wa wb wc x xb)(*strict*)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c1 = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c1 = wa @ rule_rpush e2 @ xb")
   apply(simp add: parserS.belongs_def)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c2 = w @ [parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
   prefer 2
   apply(thin_tac "parserS_conf_scheduler c2 = rule_rpush e2 @ xb")
   apply(simp add: parserS.belongs_def)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   apply(erule_tac
      x="Suc n"
      in allE)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb we)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
  apply(subgoal_tac "\<exists>w. butn wc (length wc - additionalOverhead) = butn wc (length wc - parser_fixed_input_length_recN d m) @ w")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
   prefer 2
   apply(simp add: butn_def)
   apply(case_tac "length wc - additionalOverhead")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="drop (parser_fixed_input_length_recN d m) wc"
      in exI)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length wc - Suc nat \<ge> parser_fixed_input_length_recN d m")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb nat)(*strict*)
   apply(rule_tac
      x="take ((length wc - Suc nat)-(parser_fixed_input_length_recN d m)) (drop (parser_fixed_input_length_recN d m) wc)"
      in exI)
   apply(rule take_mult_drop)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb)(*strict*)
  apply(erule_tac exE)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(rule_tac
      t="butn wc (length wc - additionalOverhead)"
      and s="butn wc (length wc - parser_fixed_input_length_recN d m) @ wd"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. wb @ butn wc (length wc - additionalOverhead) @ MARK@[parser_bottom M] = rule_rpush e2 @ x")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(case_tac "\<exists>w. rule_rpush e2=w@[parser_bottom M]")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
   apply(subgoal_tac "parser_bottom M \<notin> set (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
   apply(rule PARSER_not_seen_entire_not_read_bottom)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
   apply(rule_tac
      n="m"
      and cn="c'"
      in PARSER_not_seen_entire_shifts_back)
         apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd we)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
  apply(clarsimp)
  apply(case_tac xb)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x xb wd a list)(*strict*)
  apply(thin_tac "xb=a#list")
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
  apply(subgoal_tac "\<exists>w'. wb @ butn wc (length wc - parser_fixed_input_length_recN d m) = rule_rpush e2 @ w'")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' w'a)(*strict*)
   apply(rule_tac
      x="w'a @ wd@MARK@[parser_bottom M]"
      in exI)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
  apply(rule_tac
      t="butn wc (length wc - parser_fixed_input_length_recN d m)"
      and s="take (parser_fixed_input_length_recN d m) wc"
      in ssubst)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
   apply(rule butn_take)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
  apply(subgoal_tac "prefix (rule_rpush e2) wb \<or> prefix wb (rule_rpush e2)")
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
   apply(erule disjE)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
    apply(simp add: prefix_def)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "wc=ca@w'")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    prefer 2
    apply(rule_tac
      w="wb"
      in append_linj)
    apply(rule_tac
      t="wb@wc"
      and s="rule_rpush e2 @ w'"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(rule_tac
      t="rule_rpush e2"
      and s="wb@ca"
      in ssubst)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(rule_tac
      t="rule_rpush e2"
      and s="wb@ca"
      in ssubst)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "\<exists>w'. take (parser_fixed_input_length_recN d m) wc = ca @ w'")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(erule exE)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca w'a)(*strict*)
    apply(rule_tac
      x="w'a"
      in exI)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d (Suc n) \<ge> length (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    prefer 2
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "length (parserS_conf_scheduler c2) - (parser_fixed_input_length_recN d (Suc n)) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d ((Suc n)+(m-Suc n)))")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    prefer 2
    apply(rule PARSER_UnseenPartStrictlyDecreases)
        apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d m \<ge> length ca")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
   apply(subgoal_tac "length (rule_rpop e2) \<ge> length (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
    apply(case_tac "(parser_fixed_input_length_recN d n) \<ge> (length (rule_rpop e2))")
     apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
     apply(subgoal_tac "max (parser_fixed_input_length_recN d n) (length (rule_rpop e2)) = (parser_fixed_input_length_recN d n)")
      apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      wb="wb"
      and wa="wa"
      and On="parser_fixed_input_length_recN d n"
      in help_lemma2)
          apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
         apply(force)
        apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
        apply(force)
       apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d n) (length (rule_rpop e2)) = (length (rule_rpop e2))")
  apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      wb="wb"
      in help_lemma3)
  apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb x wd w' ca)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
  apply(rule_tac
      t="rule_rpop e2"
      and s="wa@rule_rpush e2"
      in ssubst)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w' ca)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac n e1 e2 c1 c2 w wa wb wc x wd w')(*strict*)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_belongs_preserves: "
  valid_parser M
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead = parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast(parserS_conf_scheduler c)) (n - 1)@[parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.belongs M d'"
  apply(rule parserS.derivation_belongs)
  apply(force)
  apply(simp add: derivation_map_def)
  apply(subgoal_tac "c \<in> parserS_configurations M")
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="0"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac l wa)(*strict*)
  apply(rule conjI)
  apply(rename_tac l wa)(*strict*)
  apply(rule_tac
      B="set wa"
      in subset_trans)
  apply(rename_tac l wa)(*strict*)
  apply(rule set_butn_subset)
  apply(rename_tac l wa)(*strict*)
  apply(force)
  apply(rename_tac l wa)(*strict*)
  apply(rule_tac
      B="set wa"
      in contra_subsetD)
  apply(rename_tac l wa)(*strict*)
  apply(rule set_butn_subset)
  apply(rename_tac l wa)(*strict*)
  apply(force)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_derivation)
  apply(force)+
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_derivation_initial: "
  valid_parser M
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead = parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast (parserS_conf_scheduler c)) (n - 1) @ [parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d'
  \<Longrightarrow> parserS.derivation_initial M d
  \<Longrightarrow> parserS.derivation_initial M d'"
  apply(simp add: parserS.derivation_initial_def)
  apply(simp add: parserS_initial_configurations_def)
  apply(simp add: derivation_map_def)
  apply(clarsimp)
  apply(simp add: parserS_initial_configurations_def)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac wa)(*strict*)
  apply(subgoal_tac "set (butn wa (length (parserS_conf_scheduler c') - Suc (parser_fixed_input_length_recN d m))) \<subseteq> set wa")
  apply(rename_tac wa)(*strict*)
  apply(force)
  apply(rename_tac wa)(*strict*)
  apply(rule set_butn_subset)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_Overhead: "
  valid_parser M
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead = parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast (parserS_conf_scheduler c)) (n - 1) @ [parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d'
  \<Longrightarrow> parserS.derivation_initial M d
  \<Longrightarrow> parser_fixed_input_length_recN d x = parser_fixed_input_length_recN d' x"
  apply(induct x)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(case_tac "d (Suc x)")
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d x = Some (pair e1 c1) \<and> d (Suc x) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac x a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc x"
      in parserS.step_detail_before_some_position)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_Overhead_prime: "
  valid_parser M
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead \<ge> parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast (parserS_conf_scheduler c)) (n - 1) @ [parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d'
  \<Longrightarrow> parser_fixed_input_length_recN d x = parser_fixed_input_length_recN d' x"
  apply(induct x)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(case_tac "d (Suc x)")
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d x = Some (pair e1 c1) \<and> d (Suc x) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac x a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc x"
      in parserS.step_detail_before_some_position)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_Overhead_prime_prime: "
  valid_parser M
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> maximum_of_domain d m
  \<Longrightarrow> d 0 = Some (pair None c)
  \<Longrightarrow> d m = Some (pair e c')
  \<Longrightarrow> w @ (parserS_conf_scheduler c') = parserS_conf_scheduler c
  \<Longrightarrow> remaining=length (parserS_conf_scheduler c')
  \<Longrightarrow> additionalOverhead \<ge> parser_fixed_input_length_recN d m
  \<Longrightarrow> n = remaining - additionalOverhead
  \<Longrightarrow> d' = derivation_map d (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn (butlast (parserS_conf_scheduler c)) (n - 1) @ v @ [parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d'
  \<Longrightarrow> parser_fixed_input_length_recN d x = parser_fixed_input_length_recN d' x"
  apply(induct x)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(case_tac "d (Suc x)")
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_map_def)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d x = Some (pair e1 c1) \<and> d (Suc x) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac x a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc x"
      in parserS.step_detail_before_some_position)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(force)
  apply(rename_tac x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_map_def)
  done

lemma PARSER_derivation_map_preserves_parser_fixed_input_length_recN: "
  valid_parser P
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.derivation P d'
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> parserS.belongs P d'
  \<Longrightarrow> d' = derivation_map d C
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow> d n = Some (pair e2 c2)
  \<Longrightarrow> parser_fixed_input_length_recN d n =
          parser_fixed_input_length_recN (derivation_map d C) n"
  apply(induct n arbitrary: e2 c2)
  apply(rename_tac e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e2 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac n e2 c2)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n e2 c2)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(subgoal_tac "derivation_map d C (Suc n) = Some (pair (Some e2a) (C c2))")
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(clarsimp)
  done

lemma PARSER_derivation_map_preserves_String_of_Overhead: "
  valid_parser P
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.derivation P d'
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> parserS.belongs P d'
  \<Longrightarrow> d' = derivation_map d C
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow> d n = Some (pair e2 c2)
  \<Longrightarrow> take (parser_fixed_input_length_recN d n) (parserS_conf_scheduler c2) =
          take
           (parser_fixed_input_length_recN (derivation_map d C) n)
           (parserS_conf_scheduler (C c2))"
  apply(induct n arbitrary: e2 c2)
  apply(rename_tac e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e2 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac n e2 c2)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n e2 c2)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "derivation_map d C (Suc n) = Some (pair (Some e2a) (C c2))")
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parser_fixed_input_length_recN (derivation_map d C) n= parser_fixed_input_length_recN d n")
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  prefer 2
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map d C) n"
      and s="parser_fixed_input_length_recN d n"
      in subst)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(rule PARSER_derivation_map_preserves_parser_fixed_input_length_recN)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  prefer 4
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(subgoal_tac "parserS_step_relation P (C c1a) e2a (C c2)")
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  prefer 2
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_map d C) n = Some (pair e1 c1) \<and> (derivation_map d C) (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a e1a c1aa)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac n c2 e1 e2a c1a)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(subgoal_tac "length (rule_rpop e2a) \<ge> length (rule_rpush e2a) ")
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(clarsimp)
  apply(case_tac "parser_fixed_input_length_recN d n \<le> length (rule_rpop e2a)")
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN d n) (length (rule_rpop e2a))"
      and s="length (rule_rpop e2a)"
      in ssubst)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN d n) (length (rule_rpop e2a))"
      and s="(parser_fixed_input_length_recN d n)"
      in ssubst)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(subgoal_tac "take (parser_fixed_input_length_recN (derivation_map d C) n) (rule_rpop e2a) = rule_rpop e2a")
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  prefer 2
  apply(rule take_all)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(rule valid_parser_rules_rhs_gets_shorter)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a x xa xb xc)(*strict*)
  apply(simp add: parserS.belongs_def)
  done

lemma PARSER_derivation_map_preserves_read: "
  valid_parser P
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.derivation P d'
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> parserS.belongs P d'
  \<Longrightarrow> d' = derivation_map d C
  \<Longrightarrow> d 0 = Some (pair None c1)
  \<Longrightarrow> d n = Some (pair e2 c2)
  \<Longrightarrow> parserS_string_state c1 = w @ parserS_string_state c2
  \<Longrightarrow> parserS_string_state (C c1) = w @ parserS_string_state (C c2)"
  apply(induct n arbitrary: e2 c2 w)
  apply(rename_tac e2 c2 w)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(rename_tac n e2 c2 w)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac n e2 c2 w)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n e2 c2 w)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2 w)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2 w)(*strict*)
  apply(force)
  apply(rename_tac n e2 c2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c1a = w @ (parserS_string_state c2)")
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  prefer 2
  apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c1a)")
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  prefer 2
  apply(rule_tac
      j="n"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state (C c1a) = w @ (parserS_string_state (C c2))")
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  prefer 2
  apply(rule_tac
      i="n"
      and d="derivation_map d C"
      and j="Suc 0"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  apply(force)
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac n c2 w e1 e2a c1a wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1a"
      in meta_allE)
  apply(erule_tac
      x="wb"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. (derivation_map d C) n = Some (pair e1 c1) \<and> (derivation_map d C) (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac n c2 e1 e2a c1a wa wb wc)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc)(*strict*)
  apply(force)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc e1a e2 c1aa c2a)(*strict*)
  apply(subgoal_tac "derivation_map d C n = Some (pair e1 (C c1a))")
  apply(rename_tac n c2 e1 e2a c1a wa wb wc e1a e2 c1aa c2a)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc e1a e2 c1aa c2a)(*strict*)
  apply(subgoal_tac "derivation_map d C (Suc n) = Some (pair (Some e2a) (C c2))")
  apply(rename_tac n c2 e1 e2a c1a wa wb wc e1a e2 c1aa c2a)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac n c2 e1 e2a c1a wa wb wc e1a e2 c1aa c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c2 c1a wa wb wc e1a e2)(*strict*)
  apply(thin_tac "derivation_map d C n = Some (pair e1a (C c1a))")
  apply(thin_tac "derivation_map d C (Suc n) = Some (pair (Some e2) (C c2))")
  apply(rename_tac n c2 c1a wa wb wc e1a e2)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c2 c1a wa wb wc e1a e2 x xa xb xc)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n c2 c1a wa wb wc e1a e2 x xa xb xc rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  done

lemma PARSER0_parser_fixed_input_length_recN_replacement: "
  valid_bounded_parser M 0
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parser_fixed_input_length_recN d n = 0"
  apply(induct n)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc n)")
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac n a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  done

lemma parser_fixed_input_length_rec1_maximum: "
  valid_bounded_parser M k
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parser_fixed_input_length_rec1 d n \<le> k"
  apply(induct n)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc n)")
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac n a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "e2 \<in> parser_rules M")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(case_tac "rule_rpop e2")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 a list)(*strict*)
  apply(clarsimp)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac n e1 e2 c1 c2 a list)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 a list)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(rule_tac
      j="Suc(length list)"
      in le_trans)
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(rule_tac
      t="Suc(length list)"
      and s="length(a # list)"
      in ssubst)
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(simp (no_asm_use))
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(rule_tac
      t="a # list"
      and s="kPrefix ka (w @ [parser_bottom M])"
      in ssubst)
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(rule_tac
      t="kPrefix ka (w @ [parser_bottom M])"
      and s="xa @ rule_rpush e2"
      in ssubst)
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(simp (no_asm_simp))
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(simp (no_asm_use))
  apply(rename_tac n e1 e2 c1 c2 a list ka w xa)(*strict*)
  apply(force)
  done

lemma parser_fixed_input_length_recN_maximum: "
  valid_bounded_parser M k
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parser_fixed_input_length_recN d n \<le> k"
  apply(induct n)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc n)")
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac n a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "e2 \<in> parser_rules M")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma PARSER1_parser_fixed_input_length_recN_replacement: "
  valid_bounded_parser M k
  \<Longrightarrow> k\<le>Suc 0
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parser_fixed_input_length_recN d n = parser_fixed_input_length_rec1 d n"
  apply(case_tac "k=0")
  apply(clarsimp)
  apply(rule_tac
      t="parser_fixed_input_length_recN d n"
      and s="0"
      in ssubst)
  apply(rule PARSER0_parser_fixed_input_length_recN_replacement)
  apply(force)
  apply(force)
  apply(force)
  apply(induct n)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc n)")
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac n a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "e2 \<in> parser_rules M")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(subgoal_tac "k=Suc 0")
  prefer 2
  apply(force)
  apply(clarsimp)
  apply(induct n)
  apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc n)")
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac n a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "e2 \<in> parser_rules M")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_rec1 d n \<le> Suc 0")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(rule parser_fixed_input_length_rec1_maximum)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "length (rule_rpop e2) \<le> Suc 0")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "length (rule_rpush e2) \<le> length (rule_rpop e2)")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      and P="\<lambda>e2. valid_parser_step_label M e2"
      in ballE)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 k w xa)(*strict*)
  apply(rule_tac
      t="kPrefix k (w @ [parser_bottom M])"
      and s="xa @ rule_rpush e2"
      in ssubst)
  apply(rename_tac n e1 e2 c1 c2 k w xa)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 k w xa)(*strict*)
  apply(simp (no_asm_use))
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(case_tac "rule_rpop e2")
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 a)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_rec1 d n) (Suc 0)"
      and s="Suc 0"
      in ssubst)
  apply(rename_tac n e1 e2 c1 c2 a)(*strict*)
  apply(force)
  apply(rename_tac n e1 e2 c1 c2 a)(*strict*)
  apply(clarsimp)
  done

lemma valid_parser_implies_some_valid_bounded_parser: "
  valid_parser P
  \<Longrightarrow> \<exists>k. valid_bounded_parser P k"
  apply(simp add: valid_bounded_parser_def)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(rule finite_has_max)
  apply(force)
  done

lemma PARSER_always_bottom: "
  parserS.belongs P d
  \<Longrightarrow> d i = Some (pair e \<lparr>parserS_conf_stack=w, parserS_conf_scheduler=v\<rparr>)
  \<Longrightarrow> \<exists>v'. v=v'@[parser_bottom P] \<and> (parser_bottom P \<notin> set v')"
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(auto)
  apply(simp add: parserS_configurations_def)
  done

lemma eachLabelInRuleSet: "
  valid_parser P
  \<Longrightarrow> parserS.derivation P dP
  \<Longrightarrow> maximum_of_domain dP n
  \<Longrightarrow> \<pi>' = get_labels dP n
  \<Longrightarrow> option_to_setMap (set \<pi>') \<subseteq> parser_rules P"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: get_labels_def)
  apply(simp add: option_to_setMap_def)
  apply(auto)
  apply(rename_tac x i)(*strict*)
  apply(simp add: get_label_def)
  apply(case_tac x)
  apply(rename_tac x i rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
  apply(auto)
  apply(rename_tac i rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
  apply(case_tac "dP i")
  apply(rename_tac i rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
  apply(auto)
  apply(rename_tac i rule_lpop rule_rpop rule_lpush rule_rpush a)(*strict*)
  apply(case_tac a)
  apply(rename_tac i rule_lpop rule_rpop rule_lpush rule_rpush a option b)(*strict*)
  apply(auto)
  apply(rename_tac i rule_lpop rule_rpop rule_lpush rule_rpush b)(*strict*)
  apply(case_tac i)
  apply(rename_tac i rule_lpop rule_rpop rule_lpush rule_rpush b)(*strict*)
  apply(auto)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b)(*strict*)
  apply(rule parserS.initialNotEdgeSome_prime)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b)(*strict*)
  apply(blast)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b)(*strict*)
  apply(blast)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat)(*strict*)
  apply(case_tac "dP nat")
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat)(*strict*)
  apply(rule parserS.derivationNoFromNone)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat)(*strict*)
  apply(blast)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat)(*strict*)
  apply(blast)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat)(*strict*)
  apply(blast)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat a)(*strict*)
  apply(case_tac a)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat a option ba)(*strict*)
  apply(auto)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat option ba)(*strict*)
  apply(subgoal_tac "parserS_step_relation P ba \<lparr>rule_lpop = rule_lpop, rule_rpop = rule_rpop, rule_lpush = rule_lpush, rule_rpush = rule_rpush\<rparr> b")
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat option ba)(*strict*)
  prefer 2
  apply(rule parserS.position_change_due_to_step_relation)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat option ba)(*strict*)
  apply(blast)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat option ba)(*strict*)
  apply(blast)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat option ba)(*strict*)
  apply(blast)
  apply(rename_tac rule_lpop rule_rpop rule_lpush rule_rpush b nat option ba)(*strict*)
  apply(simp add: parserS_step_relation_def)
  done

lemma valid_parser_implies_valid_parser_step_label: "
  valid_parser P
  \<Longrightarrow> a \<in> parser_rules P
  \<Longrightarrow> valid_parser_step_label P a"
  apply(simp add: valid_parser_def)
  done

lemma PARSER_always_suffixing: "
  valid_parser P
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> d i = Some (pair e \<lparr>parserS_conf_stack=w, parserS_conf_scheduler=v\<rparr>)
  \<Longrightarrow> d (i+j) = Some (pair e' \<lparr>parserS_conf_stack=w', parserS_conf_scheduler=v'\<rparr>)
  \<Longrightarrow> \<exists>v''. v''@v'=v"
  apply(induct j arbitrary: e' w' v')
  apply(rename_tac e' w' v')(*strict*)
  apply(clarsimp)
  apply(rename_tac j e' w' v')(*strict*)
  apply(subgoal_tac "\<exists>e' w' v'. d (i+j) = Some (pair e' \<lparr>parserS_conf_stack=w', parserS_conf_scheduler=v'\<rparr>)")
  apply(rename_tac j e' w' v')(*strict*)
  apply(clarsimp)
  apply(rename_tac j e' w' v' e'a w'a v'a)(*strict*)
  apply(erule_tac
      x="e'a"
      in meta_allE)
  apply(erule_tac
      x="w'a"
      in meta_allE)
  apply(erule_tac
      x="v'a"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac j e' w' v' e'a w'a v'a v'')(*strict*)
  apply(case_tac e')
  apply(rename_tac j e' w' v' e'a w'a v'a v'')(*strict*)
  apply(rule parserS.derivation_Always_PreEdge_prime)
  apply(rename_tac j e' w' v' e'a w'a v'a v'')(*strict*)
  apply(force)
  apply(rename_tac j e' w' v' e'a w'a v'a v'')(*strict*)
  apply(force)
  apply(rename_tac j e' w' v' e'a w'a v'a v'' a)(*strict*)
  apply(clarsimp)
  apply(rename_tac j w' v' e'a w'a v'a v'' a)(*strict*)
  apply(subgoal_tac "parserS_step_relation P \<lparr>parserS_conf_stack = w'a, parserS_conf_scheduler = v'a\<rparr> a \<lparr>parserS_conf_stack = w', parserS_conf_scheduler = v'\<rparr>")
  apply(rename_tac j w' v' e'a w'a v'a v'' a)(*strict*)
  prefer 2
  apply(rule_tac
      n="i+j"
      in parserS.position_change_due_to_step_relation)
  apply(rename_tac j w' v' e'a w'a v'a v'' a)(*strict*)
  apply(blast)
  apply(rename_tac j w' v' e'a w'a v'a v'' a)(*strict*)
  apply(blast)
  apply(rename_tac j w' v' e'a w'a v'a v'' a)(*strict*)
  apply(blast)
  apply(rename_tac j w' v' e'a w'a v'a v'' a)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac j e'a v'' a x xa)(*strict*)
  apply(subgoal_tac "(\<exists>x. x@(rule_rpush a)=rule_rpop a)")
  apply(rename_tac j e'a v'' a x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e'a v'' a x xa xb)(*strict*)
  apply(case_tac xa)
  apply(rename_tac j e'a v'' a x xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e'a v'' a x xb)(*strict*)
  apply(case_tac a)
  apply(rename_tac j e'a v'' a x xb rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e'a v'' a x xa xb aa list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
  apply(rename_tac j e'a v'' a x xa xb aa list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac j e'a v'' a x xa xb aa list)(*strict*)
  apply(thin_tac "xa=aa#list")
  apply(clarsimp)
  apply(rename_tac j e'a v'' a x xb w' x')(*strict*)
  apply(rule_tac
      x="v''@xb"
      in exI)
  apply(force)
  apply(rename_tac j e'a v'' a x xa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P a")
  apply(rename_tac j e'a v'' a x xa)(*strict*)
  prefer 2
  apply(rule valid_parser_implies_valid_parser_step_label)
  apply(rename_tac j e'a v'' a x xa)(*strict*)
  apply(force)
  apply(rename_tac j e'a v'' a x xa)(*strict*)
  apply(force)
  apply(rename_tac j e'a v'' a x xa)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(rename_tac j e' w' v')(*strict*)
  apply(case_tac "d (i+j)")
  apply(rename_tac j e' w' v')(*strict*)
  apply(rule parserS.derivationNoFromNone)
  apply(rename_tac j e' w' v')(*strict*)
  apply(force)
  apply(rename_tac j e' w' v')(*strict*)
  apply(force)
  apply(rename_tac j e' w' v')(*strict*)
  apply(force)
  apply(rename_tac j e' w' v' a)(*strict*)
  apply(case_tac a)
  apply(rename_tac j e' w' v' a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac j e' w' v' option b)(*strict*)
  apply(case_tac b)
  apply(rename_tac j e' w' v' option b parserS_conf_stack parserS_conf_scheduler)(*strict*)
  apply(clarsimp)
  done

lemma parserS_inst_9: "
  (\<forall>M. valid_parser M \<longrightarrow> (\<forall>e. e \<in> parser_step_labels M \<longrightarrow> (\<forall>c1 c2. parserS_step_relation M c1 e c2 \<longrightarrow> (\<exists>w. parserS_string_state c1 = w @ parserS_string_state c2))))"
  apply(clarsimp)
  apply(rename_tac M e c1 c2)(*strict*)
  apply(simp add: parserS_string_state_def parserS_step_relation_def parser_step_labels_def)
  apply(clarsimp)
  apply(rename_tac M e c1 c2 x xa)(*strict*)
  apply(case_tac c1)
  apply(rename_tac M e c1 c2 x xa parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(case_tac c2)
  apply(rename_tac M e c1 c2 x xa parserS_conf_stacka parserS_conf_schedulera parserS_conf_stackaa parserS_conf_scheduleraa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e)(*strict*)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
  apply(rename_tac M e)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac M e)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac M e k w xa)(*strict*)
  apply(case_tac "(\<exists>x. x @ [parser_bottom M] = kPrefix k (w @ [parser_bottom M]))")
  apply(rename_tac M e k w xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e k w xa x xb)(*strict*)
  apply(case_tac e)
  apply(rename_tac M e k w xa x xb rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac M k w xa x xb rule_lpop rule_lpush)(*strict*)
  apply(rule_tac
      t="kPrefix k (w @ [parser_bottom M])"
      and s="xa @ x @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac M k w xa x xb rule_lpop rule_lpush)(*strict*)
  apply(force)
  apply(rename_tac M k w xa x xb rule_lpop rule_lpush)(*strict*)
  apply(rule_tac
      x="xa"
      in exI)
  apply(force)
  apply(rename_tac M e k w xa)(*strict*)
  apply(rule_tac
      x="xa"
      in exI)
  apply(force)
  done

lemma parserS_inst_10: "
  (\<forall>G d. parserS.derivation G d \<longrightarrow> parserS.belongs G d \<longrightarrow> parserS_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> parserS_marking_configurations G))"
  apply(simp add: parserS_marking_condition_def parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(rule order_antisym)
  apply(rename_tac G d)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d i e c f w)(*strict*)
  apply(case_tac "d 0")
  apply(rename_tac G d i e c f w)(*strict*)
  apply(rule parserS.initialNotNone_prime)
  apply(rename_tac G d i e c f w)(*strict*)
  apply(force)
  apply(rename_tac G d i e c f w)(*strict*)
  apply(force)
  apply(rename_tac G d i e c f w a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G d i e c f w a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d i e c f w option b)(*strict*)
  apply(case_tac option)
  apply(rename_tac G d i e c f w option b)(*strict*)
  prefer 2
  apply(rename_tac G d i e c f w option b a)(*strict*)
  apply(rule parserS.initialNotEdgeSome_prime)
  apply(rename_tac G d i e c f w option b a)(*strict*)
  apply(force)
  apply(rename_tac G d i e c f w option b a)(*strict*)
  apply(force)
  apply(rename_tac G d i e c f w option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d i e c f w b)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="0"
      in allE)
  apply(clarsimp)
  done

lemma PARSERl_Nonblockingness2: "
  valid_bounded_parser P k
  \<Longrightarrow> k\<le>Suc 0
  \<Longrightarrow> Nonblockingness2 (parserS.unmarked_language P) (parserS.marked_language P)"
  apply(subgoal_tac "valid_parser P")
  prefer 2
  apply(simp add: valid_bounded_parser_def)
  apply(simp add: Nonblockingness2_def)
  apply(simp add: parserS.marked_language_def parserS.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
  apply(rename_tac x d c)(*strict*)
  prefer 2
  apply(rule parserS.some_position_has_details_at_0)
  apply(force)
  apply(rename_tac x d c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca)(*strict*)
  apply(subgoal_tac "parserS.belongs P d")
  apply(rename_tac x d c ca)(*strict*)
  prefer 2
  apply(rule parserS.derivation_belongs)
  apply(rename_tac x d c ca)(*strict*)
  apply(force)
  apply(rename_tac x d c ca)(*strict*)
  apply(force)
  apply(rename_tac x d c ca)(*strict*)
  apply(simp add: parserS.derivation_initial_def parserS_initial_configurations_def)
  apply(rename_tac x d c ca)(*strict*)
  apply(force)
  apply(rename_tac x d c ca)(*strict*)
  apply(simp add: parserS_marked_effect_def parserS_unmarked_effect_def parserS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb)(*strict*)
  apply(simp add: parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state ca = w @ (parserS_string_state cb)")
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(subgoal_tac "\<exists>k\<le>i. (\<forall>i<k. \<not> (\<lambda>k. \<exists>c' e. d k = Some (pair e c') \<and> length(parserS_conf_scheduler c')\<le>(length (c@[parser_bottom P]))) i) \<and> (\<lambda>k. \<exists>c' e. d k = Some (pair e c') \<and> length(parserS_conf_scheduler c')\<le>(length (c@[parser_bottom P]))) k")
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  prefer 2
  apply(rule ex_least_nat_le_prime)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state ca = w @ (parserS_string_state c')")
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  prefer 2
  apply(rule_tac
      j="ka"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. parserS_string_state c' = w @ (parserS_string_state cb)")
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  prefer 2
  apply(rule_tac
      j="i-ka"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. c=w@wb")
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  prefer 2
  apply(case_tac "wa=x")
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  apply(subgoal_tac "prefix wa x \<or> prefix x wa")
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  apply(simp add: prefix_def)
  apply(erule disjE)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  apply(rule_tac
      b="wb"
      in mutual_prefix_prefix)
  apply(rule sym)
  apply(force)
  apply(rename_tac x d c ca i e cb f w ka c' ea wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(subgoal_tac "\<exists>k\<le>ka. (\<exists>c. d 0 = Some (pair None c) \<and> (\<exists>c'. (\<exists>e. d k = Some (pair e c')) \<and> (\<exists>v. v @ parserS_conf_scheduler c' = parserS_conf_scheduler c \<and> x = v @ take (parser_fixed_input_length_rec1 d k) (butlast (parserS_conf_scheduler c'))))) ")
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(erule exE)+
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      x="derivation_take d kaa"
      in exI)
  apply(subgoal_tac "parserS.derivation P (derivation_take d kaa)")
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule conjI)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(simp add: parserS.derivation_initial_def)
  apply(simp add: derivation_take_def)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule conjI)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(rule conjI)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule_tac
      x="c'a"
      in exI)
  apply(rule_tac
      x="kaa"
      in exI)
  apply(rule conjI)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(rule conjI)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule_tac
      t="(parser_fixed_input_length_recN (derivation_take d kaa) kaa)"
      and s="(parser_fixed_input_length_recN d kaa)"
      in ssubst)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule parser_fixed_input_length_recN_with_derivation_take)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN d kaa"
      and s="parser_fixed_input_length_rec1 d kaa"
      in ssubst)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule PARSER1_parser_fixed_input_length_recN_replacement)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc kaa c c'a eb v)(*strict*)
  apply(rule parserS.derivation_take_preserves_derivation)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_string_state ca = w @ (parserS_string_state cb)")
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(case_tac ka)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w ka c' ea wb wc wa nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' ea wb wc nat)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac x d ca i e cb f w c' ea wb wc nat)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
  apply(rename_tac x d ca i e cb f w c' ea wb wc nat)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' ea wb wc nat)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' ea wb wc nat)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' ea wb wc nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "e2 \<in> parser_rules P")
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc nat"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "length (rule_rpop e2) \<le> Suc 0")
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  prefer 2
  apply(simp add: valid_bounded_parser_def)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "length (rule_rpush e2) \<le> length (rule_rpop e2)")
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  prefer 2
  apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      and P="\<lambda>e2. valid_parser_step_label P e2"
      in ballE)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 ka wa xb)(*strict*)
  apply(rule_tac
      t="kPrefix ka (wa @ [parser_bottom P])"
      and s="xb @ rule_rpush e2"
      in ssubst)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 ka wa xb)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 ka wa xb)(*strict*)
  apply(simp (no_asm_use))
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state ca = w @ (parserS_string_state c1)")
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  prefer 2
  apply(rule_tac
      j="nat"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c')")
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  prefer 2
  apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. w\<noteq>[] \<and> wa@w=x")
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  prefer 2
  apply(subgoal_tac "prefix x wa \<or> prefix wa x")
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  apply(case_tac "x=wa")
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  apply(erule disjE)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  apply(rule mutual_prefix_prefix)
  apply(force)
  apply(rename_tac x d ca i e cb f w c' wb wc nat e1 e2 c1 wa wd)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we)(*strict*)
  apply(subgoal_tac "wc=[]")
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we)(*strict*)
  prefer 2
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we x xa)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we x xa)(*strict*)
  apply(case_tac "rule_rpop e2")
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we x xa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we x xa a)(*strict*)
  apply(case_tac we)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we x xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we x xa a aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we x xa)(*strict*)
  apply(force)
  apply(rename_tac d ca i e cb f w c' wb wc nat e1 e2 c1 wa we)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb nat e1 e2 c1 wa we)(*strict*)
  apply(rule_tac
      x="Suc nat"
      in exI)
  apply(clarsimp)
  apply(case_tac "rule_rpop e2")
  apply(rename_tac d ca i e cb f w c' wb nat e1 e2 c1 wa we)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(rename_tac d ca i e cb f w c' wb nat e1 e2 c1 wa we a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb nat e1 e2 c1 wa we a)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb nat e1 e2 c1 wa we a x xa)(*strict*)
  apply(case_tac we)
  apply(rename_tac d ca i e cb f w c' wb nat e1 e2 c1 wa we a x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d ca i e cb f w c' wb nat e1 e2 c1 wa we a x xa aa list)(*strict*)
  apply(clarsimp)
  done

lemma PARSERl_unmarked_closed: "
  valid_bounded_parser P k
  \<Longrightarrow> k\<le>Suc 0
  \<Longrightarrow> Nonblockingness2 (parserHF.unmarked_language P) (parserHF.unmarked_language P)"
  apply(subgoal_tac "valid_parser P")
  prefer 2
  apply(simp add: valid_bounded_parser_def)
  apply(simp add: Nonblockingness2_def)
  apply(simp add: parserS.marked_language_def parserHF.unmarked_language_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
  apply(rename_tac x d c)(*strict*)
  prefer 2
  apply(rule parserHF.some_position_has_details_at_0)
  apply(force)
  apply(rename_tac x d c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c ca)(*strict*)
  apply(subgoal_tac "ca \<in> parserHF_initial_configurations P")
  apply(rename_tac x d c ca)(*strict*)
  prefer 2
  apply(simp add: parserHF.derivation_initial_def)
  apply(rename_tac x d c ca)(*strict*)
  apply(simp add: parserHF_initial_configurations_def)
  apply(clarsimp)
  apply(case_tac ca)
  apply(rename_tac x d c ca parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c)(*strict*)
  apply(simp add: parserHF_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x d c i e ca)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>k\<le>i. (\<forall>i<k. \<not> (\<lambda>k. \<exists>c' e. d k = Some (pair e c') \<and> length(parserHF_conf_history c')\<ge>(length x)) i) \<and> (\<lambda>k. \<exists>c' e. d k = Some (pair e c') \<and> length(parserHF_conf_history c')\<ge>(length x)) k")
  apply(rename_tac x d c i e ca)(*strict*)
  prefer 2
  apply(rule ex_least_nat_le_prime)
  apply(clarsimp)
  apply(rename_tac x d c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca ka c' ea)(*strict*)
  apply(case_tac ka)
  apply(rename_tac x d c i e ca ka c' ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac d i e ca)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(clarsimp)
  apply(rename_tac x d c i e ca ka c' ea nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' ea nat)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d c i e ca c' ea nat)(*strict*)
  prefer 2
  apply(rule_tac
      d="d"
      and n="nat"
      and m="i"
      in parserHF.step_detail_before_some_position)
  apply(rename_tac x d c i e ca c' ea nat)(*strict*)
  apply(simp add: parserHF.derivation_initial_def)
  apply(rename_tac x d c i e ca c' ea nat)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' ea nat)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' ea nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHF_conf_history ca = (parserHF_conf_history c1)@w")
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  prefer 2
  apply(rule_tac
      n="nat"
      and m="i-nat"
      in parserHF.steps_extend_history_derivation)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  prefer 2
  apply(simp add: get_configuration_def)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(rule parserHF.belongs_configurations)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(rule parserHF.derivation_initial_belongs)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHF_conf_history c' = (parserHF_conf_history c1)@w")
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  prefer 2
  apply(rule_tac
      n="nat"
      and m="Suc 0"
      in parserHF.steps_extend_history_derivation)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  prefer 2
  apply(simp add: get_configuration_def)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(rule parserHF.belongs_configurations)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(rule parserHF.derivation_initial_belongs)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHF_conf_history ca = (parserHF_conf_history c')@w")
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  prefer 2
  apply(subgoal_tac "X" for X)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  prefer 2
  apply(rule_tac
      n="Suc nat"
      and m="i-Suc nat"
      in parserHF.steps_extend_history_derivation)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  prefer 2
  apply(simp add: get_configuration_def)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(rule parserHF.belongs_configurations)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(rule parserHF.derivation_initial_belongs)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w wa)(*strict*)
  apply(simp add: get_configuration_def)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wa wb)(*strict*)
  apply(rule_tac
      x="Suc nat"
      in exI)
  apply(clarsimp)
  apply(simp add: parserHF_step_relation_def valid_bounded_parser_def)
  apply(clarsimp)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa)(*strict*)
  apply(case_tac ca)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f h l)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa f h l)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa f h l parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f1 h1 l1)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa f h l f1 h1 l1)(*strict*)
  apply(case_tac c')
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa f h l f1 h1 l1 parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(rename_tac f2 h2 l2)
  apply(rename_tac x d c i e ca c' nat e1 e2 c1 wb xa f h l f1 h1 l1 f2 h2 l2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1)(*strict*)
  apply(erule disjE)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l h1 ca)(*strict*)
  apply(subgoal_tac "drop (length (rule_rpop e2) + length ca) (butlast_if_match (rule_rpop e2) (parser_bottom P)) = []")
  apply(rename_tac x d c i e nat e1 e2 wb xa f l h1 ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l h1 ca)(*strict*)
  apply(rule drop_entire_butlast_if_match)
  apply(force)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1 ca)(*strict*)
  apply(rule_tac
      xs="rule_rpop e2"
      in rev_cases)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1 ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l h1)(*strict*)
  apply(subgoal_tac "butlast_if_match [] (parser_bottom P) = []")
  apply(rename_tac x d c i e nat e1 e2 wb xa f l h1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l h1)(*strict*)
  apply (metis butlast_if_match_direct2_prime empty_iff list.set(1))
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1 ca ys y)(*strict*)
  apply(subgoal_tac "prefix h1 x \<or> prefix x h1")
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1 ca ys y)(*strict*)
  prefer 2
  apply(rule mutual_prefix_prefix)
  apply(rule sym)
  apply(force)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1 ca ys y)(*strict*)
  apply(erule disjE)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1 ca ys y)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x d c i e nat e1 e2 wb xa f l f1 h1 ca ys y)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 ca ys y cb)(*strict*)
  apply(rule_tac
      xs="ca"
      in rev_cases)
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 ca ys y cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 ys y cb)(*strict*)
  apply(subgoal_tac "drop (Suc (length ys)) (butlast_if_match (ys @ [y]) (parser_bottom P)) = []")
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 ys y cb)(*strict*)
  prefer 2
  apply(rule drop_entire_butlast_if_match)
  apply(force)
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 ys y cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 ca ys y cb ysa ya)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 y cb ysa)(*strict*)
  apply(case_tac "f1")
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 y cb ysa)(*strict*)
  prefer 2
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 y cb ysa a list)(*strict*)
  apply(force)
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 y cb ysa)(*strict*)
  apply(case_tac "ysa")
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 y cb ysa)(*strict*)
  prefer 2
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 y cb ysa a list)(*strict*)
  apply(force)
  apply(rename_tac d c i e nat e1 e2 wb xa f l f1 h1 y cb ysa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb)(*strict*)
  apply(case_tac "y=parser_bottom P")
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb)(*strict*)
  apply(subgoal_tac "butlast_if_match [y] (parser_bottom P) = []")
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb)(*strict*)
  prefer 2
  apply (metis append_Nil butlast_if_match_direct)
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb)(*strict*)
  apply(subgoal_tac "butlast_if_match [y] (parser_bottom P) = [y]")
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb)(*strict*)
  prefer 2
  apply (metis append_Nil butlast_if_match_direct2)
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      xs="cb"
      in rev_cases)
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c i e nat e1 e2 wb xa f l h1 y cb ys ya)(*strict*)
  apply(clarsimp)
  done

lemma parser_fixed_input_length_recN_derivation_take_ignore_for_smaller: "
  k \<le> n1
  \<Longrightarrow> k \<le> n2
  \<Longrightarrow> parser_fixed_input_length_recN (derivation_take d n1) k = parser_fixed_input_length_recN (derivation_take d n2) k"
  apply(induct k)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(case_tac "derivation_take d n1 (Suc k)")
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(case_tac "derivation_take d n2 (Suc k)")
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k a)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac k a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac k a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac k option b)(*strict*)
  apply(case_tac "derivation_take d n2 (Suc k)")
  apply(rename_tac k option b)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(rename_tac k option b a)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(rename_tac k option b)(*strict*)
  apply(case_tac option)
  apply(rename_tac k option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac k b)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac k option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac k b a)(*strict*)
  apply(simp add: derivation_take_def)
  done

lemma parser_fixed_input_length_recN_Crop_one: "
  valid_parser P
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parser_fixed_input_length_recN (derivation_take d k) k = parser_fixed_input_length_recN d k"
  apply(induct k)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(case_tac "d (Suc k)")
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(fold derivation_take_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d (Suc k)) k"
      and s="parser_fixed_input_length_recN (derivation_take d k) k"
      in ssubst)
  apply(rename_tac k)(*strict*)
  apply(rule parser_fixed_input_length_recN_derivation_take_ignore_for_smaller)
  apply(rename_tac k)(*strict*)
  apply(force)
  apply(rename_tac k)(*strict*)
  apply(force)
  apply(rename_tac k)(*strict*)
  apply(force)
  apply(rename_tac k a)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(subgoal_tac "\<exists>e c. d(Suc k)=Some (pair (Some e) c)")
  apply(rename_tac k a)(*strict*)
  prefer 2
  apply(rule parserS.pre_some_position_is_some_position_prime)
  apply(rename_tac k a)(*strict*)
  apply(force)
  apply(rename_tac k a)(*strict*)
  apply(force)
  apply(rename_tac k a)(*strict*)
  apply(force)
  apply(rename_tac k a)(*strict*)
  apply(force)
  apply(rename_tac k a)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e c)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d (Suc k)) k"
      and s="parser_fixed_input_length_recN (derivation_take d k) k"
      in ssubst)
  apply(rename_tac k e c)(*strict*)
  apply(fold derivation_take_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d (Suc k)) k"
      and s="parser_fixed_input_length_recN (derivation_take d k) k"
      in ssubst)
  apply(rename_tac k e c)(*strict*)
  apply(rule parser_fixed_input_length_recN_derivation_take_ignore_for_smaller)
  apply(rename_tac k e c)(*strict*)
  apply(force)
  apply(rename_tac k e c)(*strict*)
  apply(force)
  apply(rename_tac k e c)(*strict*)
  apply(force)
  apply(rename_tac k e c)(*strict*)
  apply(clarsimp)
  done

lemma PARSER_AnyEffect_Crop_Decompose: "
  valid_parser P
  \<Longrightarrow> d 0 = Some (pair None c0)
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d (Suc i) = Some (pair ei' ci')
  \<Longrightarrow> parserS_conf_scheduler c0 = read @ (parserS_conf_scheduler ci)
  \<Longrightarrow> parserS_conf_scheduler ci = read' @ (parserS_conf_scheduler ci')
  \<Longrightarrow> seen'=take (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci'))
  \<Longrightarrow> parserS_unmarked_effect M (derivation_take d (Suc i)) = parserS_unmarked_effect M (derivation_take d i) \<union> {read@read'@seen'}"
  apply(rule order_antisym)
  apply(rule subsetI)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>c c' ia e v. derivation_take d (Suc i) 0 = Some (pair None c) \<and> derivation_take d (Suc i) ia = Some (pair e c') \<and> v @ parserS_conf_scheduler c' = parserS_conf_scheduler c \<and> x = v @ take (parser_fixed_input_length_recN (derivation_take d (Suc i)) ia) (butlast (parserS_conf_scheduler c'))")
  apply(rename_tac x)(*strict*)
  prefer 2
  apply(simp only: parserS_unmarked_effect_def)
  apply(force)
  apply(rename_tac x)(*strict*)
  apply(thin_tac "x \<in> parserS_unmarked_effect M (derivation_take d (Suc i))")
  apply(erule exE)+
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(erule conjE)+
  apply(case_tac "ia\<le>i")
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule UnI1)
  apply(simp add: parserS_unmarked_effect_def)
  apply(rule_tac
      x="c0"
      in exI)
  apply(clarsimp)
  apply(rename_tac c c' ia e v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rule_tac
      x="c'"
      in exI)
  apply(clarsimp)
  apply(rename_tac c' ia e v)(*strict*)
  apply(rule_tac
      x="ia"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="v"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="parser_fixed_input_length_recN (\<lambda>n. if n \<le> Suc i then d n else None) ia"
      and s="parser_fixed_input_length_recN (\<lambda>n. if n \<le> i then d n else None) ia"
      in ssubst)
  apply(rename_tac c' ia e v)(*strict*)
  apply(fold derivation_take_def)
  apply(rule parser_fixed_input_length_recN_derivation_take_ignore_for_smaller)
  apply(rename_tac c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule UnI2)
  apply(case_tac "ia > Suc i")
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(subgoal_tac "Suc i=ia")
  apply(rename_tac x c c' ia e v)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(subgoal_tac "v @ take (parser_fixed_input_length_recN (derivation_take d (Suc i)) ia) (butlast (parserS_conf_scheduler c')) = read @ read' @ seen'")
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="ia"
      and s="Suc i"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(thin_tac "\<not> ia\<le>i")
  apply(thin_tac "\<not> Suc i<ia")
  apply(thin_tac "x = v @ take (parser_fixed_input_length_recN (derivation_take d (Suc i)) ia) (butlast (parserS_conf_scheduler c'))")
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(subgoal_tac "d (Suc i) = Some (pair e c')")
  apply(rename_tac x c c' ia e v)(*strict*)
  prefer 2
  apply(simp add: derivation_take_def)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(thin_tac "derivation_take d (Suc i) ia = Some (pair e c')")
  apply(subgoal_tac "d 0 = Some (pair None c)")
  apply(rename_tac x c c' ia e v)(*strict*)
  prefer 2
  apply(simp add: derivation_take_def)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(thin_tac "derivation_take d (Suc i) 0 = Some (pair None c)")
  apply(rule_tac
      t="c'"
      and s="ci'"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(subgoal_tac "v @ parserS_conf_scheduler ci' = parserS_conf_scheduler c0")
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(thin_tac "v @ parserS_conf_scheduler c' = parserS_conf_scheduler c")
  apply(thin_tac "d (Suc i) = Some (pair e c')")
  apply(thin_tac "d 0 = Some (pair None c)")
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d (Suc i)) (Suc i)"
      and s="parser_fixed_input_length_recN d (Suc i)"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  prefer 2
  apply(thin_tac "Suc i=ia")
  apply(rule_tac
      v="drop (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci')) @ [last(parserS_conf_scheduler ci')]"
      in append_injr)
  apply(rule_tac
      t="(v @ take (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci'))) @ drop (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci')) @ [last (parserS_conf_scheduler ci')]"
      and s="v @ (take (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci')) @ drop (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci'))) @ [last (parserS_conf_scheduler ci')]"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="(take (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci')) @ drop (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci')))"
      and s="butlast (parserS_conf_scheduler ci')"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="v @ butlast (parserS_conf_scheduler ci') @ [last (parserS_conf_scheduler ci')]"
      and s="v @ (butlast (parserS_conf_scheduler ci') @ [last (parserS_conf_scheduler ci')])"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="butlast (parserS_conf_scheduler ci') @ [last (parserS_conf_scheduler ci')]"
      and s="parserS_conf_scheduler ci'"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule butlast_last)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ci' = w @ [parser_bottom P]")
  apply(rename_tac x c c' ia e v)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac v)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="v @ parserS_conf_scheduler ci'"
      and s="parserS_conf_scheduler c0"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler c0"
      and s="read @ parserS_conf_scheduler ci"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler ci"
      and s="read' @ parserS_conf_scheduler ci'"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="seen'"
      and s="take (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci'))"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="(read @ read' @ take (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci'))) @ drop (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci')) @ [last (parserS_conf_scheduler ci')]"
      and s="read @ read' @ (take (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci')) @ drop (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci'))) @ [last (parserS_conf_scheduler ci')]"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule_tac
      t="take (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci')) @ drop (parser_fixed_input_length_recN d (Suc i)) (butlast (parserS_conf_scheduler ci'))"
      and s="butlast(parserS_conf_scheduler ci')"
      in ssubst)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ci' = w@[parser_bottom P]")
  apply(rename_tac x c c' ia e v)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac v)(*strict*)
  apply(erule_tac
      x="Suc i"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(rule parser_fixed_input_length_recN_Crop_one)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac x c c' ia e v)(*strict*)
  apply(force)
  apply(rule Un_least)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac c c' ia e v)(*strict*)
  apply(rule_tac
      x="c0"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac c c' ia e v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac c c' ia e v)(*strict*)
  apply(rule_tac
      x="c'"
      in exI)
  apply(rule_tac
      x="ia"
      in exI)
  apply(rule conjI)
  apply(rename_tac c c' ia e v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(case_tac "ia\<le>i")
  apply(rename_tac c c' ia e v)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' ia e v)(*strict*)
  apply(clarsimp)
  apply(rename_tac c c' ia e v)(*strict*)
  apply(subgoal_tac "c=c0")
  apply(rename_tac c c' ia e v)(*strict*)
  prefer 2
  apply(simp add: derivation_take_def)
  apply(rename_tac c c' ia e v)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(clarsimp)
  apply(rename_tac c' ia e v)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d i) ia"
      and s="parser_fixed_input_length_recN (derivation_take d (Suc i)) ia"
      in ssubst)
  apply(rename_tac c' ia e v)(*strict*)
  apply(rule parser_fixed_input_length_recN_derivation_take_ignore_for_smaller)
  apply(rename_tac c' ia e v)(*strict*)
  apply(case_tac "ia\<le>i")
  apply(rename_tac c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac c' ia e v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac c' ia e v)(*strict*)
  apply(case_tac "ia\<le>Suc i")
  apply(rename_tac c' ia e v)(*strict*)
  apply(force)
  apply(rename_tac c' ia e v)(*strict*)
  apply(simp add: derivation_take_def)
  apply(rename_tac c' ia e v)(*strict*)
  apply(force)
  apply(simp add: parserS_unmarked_effect_def)
  apply(rule_tac
      x="c0"
      in exI)
  apply(rule conjI)
  apply(simp add: derivation_take_def)
  apply(rule_tac
      x="ci'"
      in exI)
  apply(rule_tac
      x="Suc i"
      in exI)
  apply(rule conjI)
  apply(simp add: derivation_take_def)
  apply(rule_tac
      x="read@read'"
      in exI)
  apply(rule conjI)
  apply(force)
  apply(rule_tac
      t="read @ read' @ take (case ei' of None \<Rightarrow> parser_fixed_input_length_recN d i | Some e \<Rightarrow> max (parser_fixed_input_length_recN d i) (length (rule_rpop e)) - (length (rule_rpop e) - length (rule_rpush e))) (butlast (parserS_conf_scheduler ci')) = (read @ read') @ take (parser_fixed_input_length_recN (derivation_take d (Suc i)) (Suc i)) (butlast (parserS_conf_scheduler ci'))"
      and s=" take (case ei' of None \<Rightarrow> parser_fixed_input_length_recN d i | Some e \<Rightarrow> max (parser_fixed_input_length_recN d i) (length (rule_rpop e)) - (length (rule_rpop e) - length (rule_rpush e))) (butlast (parserS_conf_scheduler ci')) = take (parser_fixed_input_length_recN (derivation_take d (Suc i)) (Suc i)) (butlast (parserS_conf_scheduler ci'))"
      in ssubst)
  apply(force)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d (Suc i)) (Suc i)"
      and s="parser_fixed_input_length_recN d (Suc i)"
      in ssubst)
  apply(rule parser_fixed_input_length_recN_Crop_one)
  apply(force)
  apply(force)
  apply(force)
  done

lemma PARSER_maximal_context_preserves_effect_prime: "
  valid_parser M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> c \<in> parserS_initial_configurations M
  \<Longrightarrow> parserS.belongs M dh
  \<Longrightarrow> parserS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> k= parser_fixed_input_length_recN dh n
  \<Longrightarrow> parserS_conf_scheduler c = w @ parserS_conf_scheduler ca
  \<Longrightarrow> parserS_unmarked_effect M (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast(parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@[parser_bottom M]\<rparr>)) = parserS_unmarked_effect M dh"
  apply(rule_tac
      t="k"
      and s="parser_fixed_input_length_recN dh n"
      in ssubst)
  apply(force)
  apply(thin_tac "k=parser_fixed_input_length_recN dh n")
  apply(rule order_antisym)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(subgoal_tac "i\<le>n")
  apply(rename_tac cb c' i ea v)(*strict*)
  prefer 2
  apply(case_tac "i\<le>n")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(rule_tac
      m="i"
      in parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(subgoal_tac "cb=(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n))@[parser_bottom M]\<rparr>)c")
  apply(rename_tac cb c' i ea v)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(thin_tac "derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n))@[parser_bottom M]\<rparr>) 0 = Some (pair None cb)")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(case_tac a)
  apply(rename_tac c' i ea v a option b)(*strict*)
  apply(rename_tac ei ci)
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(subgoal_tac "Some (pair ei ((\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n))@[parser_bottom M]\<rparr>)ci)) = Some (pair ea c')")
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(thin_tac "derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n))@[parser_bottom M]\<rparr>) i = Some (pair ea c')")
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea v ci)(*strict*)
  apply(rule_tac
      x="ci"
      in exI)
  apply(rule_tac
      x="i"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state ci")
  apply(rename_tac i ea v ci)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state ci = w @ parserS_string_state ca")
  apply(rename_tac i ea v ci)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ci=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  prefer 2
  apply(simp only: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac wd)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wd @ [parser_bottom M])"
      and s="wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="wa @ wd @ [parser_bottom M]"
      and s="(wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length wd - parser_fixed_input_length_recN dh n) @ [parser_bottom M]\<rparr>)) i"
      and s="parser_fixed_input_length_recN dh i"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  defer
  apply(subgoal_tac "v=w")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  prefer 2
  apply(case_tac "v=w")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "v @ butn (butlast (wa @ wd @ [parser_bottom M])) (length wd - parser_fixed_input_length_recN dh n) \<noteq> butn (butlast (w @ wa @ wd @ [parser_bottom M])) (length wd - parser_fixed_input_length_recN dh n)")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (w @ wa @ wd @ [parser_bottom M])"
      and s="w@wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="w @ wa @ wd @ [parser_bottom M]"
      and s="(w @ wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wd @ [parser_bottom M])"
      and s="wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="wa @ wd @ [parser_bottom M]"
      and s="(wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (wa @ wd) (length wd - parser_fixed_input_length_recN dh n)"
      and s="wa@butn wd (length wd - parser_fixed_input_length_recN dh n)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (w @ wa @ wd) (length wd - parser_fixed_input_length_recN dh n)"
      and s="(w@wa)@butn wd (length wd - parser_fixed_input_length_recN dh n)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="w @ wa @ wd"
      and s="(w @ wa) @ wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(thin_tac "v @ butn (butlast (wa @ wd @ [parser_bottom M])) (length wd - parser_fixed_input_length_recN dh n) = butn (butlast (w @ wa @ wd @ [parser_bottom M])) (length wd - parser_fixed_input_length_recN dh n)")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="v"
      and s="w"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(simp add: butn_def)
  apply(case_tac "(parser_fixed_input_length_recN dh i - length wa) \<le> (length wd - (length wd - parser_fixed_input_length_recN dh n))")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) (length wd - (length wd - parser_fixed_input_length_recN dh n))"
      and s="parser_fixed_input_length_recN dh i - length wa"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) (length wd - (length wd - parser_fixed_input_length_recN dh n))"
      and s="(length wd - (length wd - parser_fixed_input_length_recN dh n))"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler ci) - (parser_fixed_input_length_recN dh i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN dh (i+(n-i)))")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  prefer 2
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule sym)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_Overhead)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_derivation)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(simp add: parserS.derivation_initial_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n)) @ [parser_bottom M]\<rparr>) c"
      in exI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n)) @ [parser_bottom M]\<rparr>) c'"
      in exI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule conjI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler (c'\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c')) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n)) @ [parser_bottom M]\<rparr>)"
      and s="butn (butlast (parserS_conf_scheduler c')) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n)) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc (parser_fixed_input_length_recN dh n)) @ [parser_bottom M]\<rparr>)) i"
      and s="parser_fixed_input_length_recN dh i"
      in ssubst)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule sym)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_Overhead)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_derivation)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: parserS.derivation_initial_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "i\<le>n")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(case_tac "i\<le>n")
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(rule_tac
      m="i"
      in parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state c'")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c' = w @ parserS_string_state ca")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c'=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(simp only: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="wa @ wb @ [parser_bottom M]"
      and s="(wa @ wb) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((wa @ wb) @ [parser_bottom M])"
      and s="wa@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="w @ (wa @ wb) @ [parser_bottom M]"
      and s="(w@wa @ wb) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((w@ wa @ wb) @ [parser_bottom M])"
      and s="w@wa@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb) (length wb - parser_fixed_input_length_recN dh n)"
      and s="wa@butn wb (length wb - parser_fixed_input_length_recN dh n)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (w @ wa @ wb) (length wb - parser_fixed_input_length_recN dh n)"
      and s="(w@wa)@butn wb (length wb - parser_fixed_input_length_recN dh n)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="w@wa@wb"
      and s="(w@wa)@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(rule conjI)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN dh i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN dh (i+(n-i)))")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(case_tac "length wb \<ge> parser_fixed_input_length_recN dh n")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn wb (length wb - parser_fixed_input_length_recN dh n)"
      and s="take (parser_fixed_input_length_recN dh n) wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_take)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(case_tac "(parser_fixed_input_length_recN dh i - length wa) \<le> (parser_fixed_input_length_recN dh n)")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) (parser_fixed_input_length_recN dh n)"
      and s="parser_fixed_input_length_recN dh i - length wa"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) (parser_fixed_input_length_recN dh n)"
      and s="parser_fixed_input_length_recN dh n"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn wb (length wb - parser_fixed_input_length_recN dh n)"
      and s="wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(simp add: butn_def)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  done

lemma PARSER_maximal_context_preserves_effect_prime_prime: "
  valid_parser M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> c \<in> parserS_configurations M
  \<Longrightarrow> parserS.belongs M dh
  \<Longrightarrow> parserS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> k\<ge>parser_fixed_input_length_recN dh n
  \<Longrightarrow> parserS_conf_scheduler c = w @ parserS_conf_scheduler ca
  \<Longrightarrow> parserS_unmarked_effect M (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast(parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@[parser_bottom M]\<rparr>)) = parserS_unmarked_effect M dh"
  apply(rule order_antisym)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(subgoal_tac "i\<le>n")
  apply(rename_tac cb c' i ea v)(*strict*)
  prefer 2
  apply(case_tac "i\<le>n")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(rule_tac
      m="i"
      in parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(subgoal_tac "cb=(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@[parser_bottom M]\<rparr>)c")
  apply(rename_tac cb c' i ea v)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(thin_tac "derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@[parser_bottom M]\<rparr>) 0 = Some (pair None cb)")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(case_tac a)
  apply(rename_tac c' i ea v a option b)(*strict*)
  apply(rename_tac ei ci)
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(subgoal_tac "Some (pair ei ((\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@[parser_bottom M]\<rparr>)ci)) = Some (pair ea c')")
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(thin_tac "derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@[parser_bottom M]\<rparr>) i = Some (pair ea c')")
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea v ci)(*strict*)
  apply(rule_tac
      x="ci"
      in exI)
  apply(rule_tac
      x="i"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state ci")
  apply(rename_tac i ea v ci)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state ci = w @ parserS_string_state ca")
  apply(rename_tac i ea v ci)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ci=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  prefer 2
  apply(simp only: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac wd)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wd @ [parser_bottom M])"
      and s="wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="wa @ wd @ [parser_bottom M]"
      and s="(wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length wd - k) @ [parser_bottom M]\<rparr>)) i"
      and s="parser_fixed_input_length_recN dh i"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  defer
  apply(subgoal_tac "v=w")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  prefer 2
  apply(case_tac "v=w")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "v @ butn (butlast (wa @ wd @ [parser_bottom M])) (length wd - k) \<noteq> butn (butlast (w @ wa @ wd @ [parser_bottom M])) (length wd - k)")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (w @ wa @ wd @ [parser_bottom M])"
      and s="w@wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="w @ wa @ wd @ [parser_bottom M]"
      and s="(w @ wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wd @ [parser_bottom M])"
      and s="wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="wa @ wd @ [parser_bottom M]"
      and s="(wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (wa @ wd) (length wd - k)"
      and s="wa@butn wd (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (w @ wa @ wd) (length wd - k)"
      and s="(w@wa)@butn wd (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="w @ wa @ wd"
      and s="(w @ wa) @ wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(thin_tac "v @ butn (butlast (wa @ wd @ [parser_bottom M])) (length wd - k) = butn (butlast (w @ wa @ wd @ [parser_bottom M])) (length wd - k)")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="v"
      and s="w"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(simp add: butn_def)
  apply(case_tac "(parser_fixed_input_length_recN dh i - length wa) \<le> (length wd - (length wd - k))")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) (length wd - (length wd - k))"
      and s="parser_fixed_input_length_recN dh i - length wa"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) (length wd - (length wd - k))"
      and s="(length wd - (length wd - k))"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler ci) - (parser_fixed_input_length_recN dh i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN dh (i+(n-i)))")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  prefer 2
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule sym)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_Overhead_prime)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_derivation_prime)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ [parser_bottom M]\<rparr>) c"
      in exI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ [parser_bottom M]\<rparr>) c'"
      in exI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule conjI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler (c'\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c')) (length (parserS_conf_scheduler ca) - Suc k) @ [parser_bottom M]\<rparr>)"
      and s="butn (butlast (parserS_conf_scheduler c')) (length (parserS_conf_scheduler ca) - Suc k) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ [parser_bottom M]\<rparr>)) i"
      and s="parser_fixed_input_length_recN dh i"
      in ssubst)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule sym)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_Overhead_prime)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_derivation_prime)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: parserS.derivation_initial_def)
  apply(subgoal_tac "i\<le>n")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(case_tac "i\<le>n")
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(rule_tac
      m="i"
      in parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state c'")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c' = w @ parserS_string_state ca")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c'=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(simp only: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="wa @ wb @ [parser_bottom M]"
      and s="(wa @ wb) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((wa @ wb) @ [parser_bottom M])"
      and s="wa@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="w @ (wa @ wb) @ [parser_bottom M]"
      and s="(w@wa @ wb) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((w@ wa @ wb) @ [parser_bottom M])"
      and s="w@wa@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb) (length wb - parser_fixed_input_length_recN dh n)"
      and s="wa@butn wb (length wb - parser_fixed_input_length_recN dh n)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (w @ wa @ wb) (length wb - parser_fixed_input_length_recN dh n)"
      and s="(w@wa)@butn wb (length wb - parser_fixed_input_length_recN dh n)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="w@wa@wb"
      and s="(w@wa)@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb) (length wb - k)"
      and s="wa@butn wb (length wb - k)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (w@wa @ wb) (length wb - k)"
      and s="w@butn (wa@wb) (length wb - k)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb) (length wb - k)"
      and s="wa@butn wb (length wb - k)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(rule conjI)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN dh i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN dh (i+(n-i)))")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(rule take_complex)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  done

lemma PARSER_not_DetectsEnd_never_see_bottom: "
  valid_parser P
  \<Longrightarrow> parserS.belongs P dh
  \<Longrightarrow> parserS.derivation P dh
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> \<not> parser_observes_input_terminator P
  \<Longrightarrow> parser_fixed_input_length_recN dh n < length (parserS_conf_scheduler ca)"
  apply(subgoal_tac "ca \<in> parserS_configurations P")
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(induct n arbitrary: e ca)
  apply(rename_tac e ca)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac n e ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh n = Some (pair e1 c1) \<and> dh (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac n e ca)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n e ca)(*strict*)
  apply(force)
  apply(rename_tac n e ca)(*strict*)
  apply(force)
  apply(rename_tac n e ca)(*strict*)
  apply(force)
  apply(rename_tac n e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(subgoal_tac "length (rule_rpop e2) \<ge> length (rule_rpush e2)")
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(rule prop_max)
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n ca e1 e2 c1 x xa)(*strict*)
  apply(force)
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n ca e1 e2 c1 x)(*strict*)
  apply(simp add: parser_observes_input_terminator_def)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac n ca e1 e2 c1 x)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c1 = w @ [parser_bottom P]")
  apply(rename_tac n ca e1 e2 c1 x)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x=" n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 x w wa)(*strict*)
  apply(rule_tac
      x="wa"
      in exI)
  apply(force)
  apply(rename_tac n ca e1 e2 c1 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ca e1 e2 c1 x)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca = w @ [parser_bottom P]")
  apply(rename_tac n ca e1 e2 c1 x)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac n ca e1 e2 c1 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(rule valid_parser_rules_rhs_gets_shorter)
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac n ca e1 e2 c1)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc n"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  done

lemma help_lemma1: "
  wa+wd\<ge>Oi
  \<Longrightarrow> On \<le> k
  \<Longrightarrow> Suc wd - On \<le> Suc (wa + wd) - Oi
  \<Longrightarrow> Oi - wa \<le> wd - (wd - k)"
  apply(force)
  done

lemma PARSER_maximal_context_preserves_effect_prime_prime_prime: "
  valid_parser M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> c \<in> parserS_configurations M
  \<Longrightarrow> parserS.belongs M dh
  \<Longrightarrow> parserS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> \<not> parser_observes_input_terminator M
  \<Longrightarrow> k\<ge>parser_fixed_input_length_recN dh n
  \<Longrightarrow> parserS_conf_scheduler c = w @ parserS_conf_scheduler ca
  \<Longrightarrow> parserS_unmarked_effect M (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast(parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>)) = parserS_unmarked_effect M dh"
  apply(rule order_antisym)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(subgoal_tac "i\<le>n")
  apply(rename_tac cb c' i ea v)(*strict*)
  prefer 2
  apply(case_tac "i\<le>n")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(rule_tac
      m="i"
      in parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(subgoal_tac "cb=(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>)c")
  apply(rename_tac cb c' i ea v)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(thin_tac "derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>) 0 = Some (pair None cb)")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(case_tac a)
  apply(rename_tac c' i ea v a option b)(*strict*)
  apply(rename_tac ei ci)
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(subgoal_tac "Some (pair ei ((\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>)ci)) = Some (pair ea c')")
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(thin_tac "derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>) i = Some (pair ea c')")
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea v ci)(*strict*)
  apply(rule_tac
      x="ci"
      in exI)
  apply(rule_tac
      x="i"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state ci")
  apply(rename_tac i ea v ci)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state ci = w @ parserS_string_state ca")
  apply(rename_tac i ea v ci)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ci=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  prefer 2
  apply(simp only: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac wd)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wd @ [parser_bottom M])"
      and s="wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="wa @ wd @ [parser_bottom M]"
      and s="(wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length wd - k) @ MARK@ [parser_bottom M]\<rparr>)) i"
      and s="parser_fixed_input_length_recN dh i"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  defer
  apply(subgoal_tac "v=w")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  prefer 2
  apply(case_tac "v=w")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "v @ butn (butlast (wa @ wd @ [parser_bottom M])) (length wd - k) \<noteq> butn (butlast (w @ wa @ wd @ [parser_bottom M])) (length wd - k)")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (w @ wa @ wd @ [parser_bottom M])"
      and s="w@wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="w @ wa @ wd @ [parser_bottom M]"
      and s="(w @ wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wd @ [parser_bottom M])"
      and s="wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="wa @ wd @ [parser_bottom M]"
      and s="(wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (wa @ wd) (length wd - k)"
      and s="wa@butn wd (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (w @ wa @ wd) (length wd - k)"
      and s="(w@wa)@butn wd (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="w @ wa @ wd"
      and s="(w @ wa) @ wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(thin_tac "v @ butn (butlast (wa @ wd @ [parser_bottom M])) (length wd - k) = butn (butlast (w @ wa @ wd @ [parser_bottom M])) (length wd - k)")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="v"
      and s="w"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (butn (wa @ wd) (length wd - k) @ MARK @ [parser_bottom M])"
      and s="butlast ((butn (wa @ wd) (length wd - k) @ MARK) @ [parser_bottom M])"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="(butlast ((butn (wa @ wd) (length wd - k) @ MARK) @ [parser_bottom M]))"
      and s="butn (wa @ wd) (length wd - k) @ MARK"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (wa @ wd) (length wd - k)"
      and s="wa@butn wd (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="(wa @ butn wd (length wd - k)) @ MARK"
      and s="wa @ butn wd (length wd - k) @ MARK"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler ci) - (parser_fixed_input_length_recN dh i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN dh (i+(n-i)))")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh i - length wa \<le> length (butn wd (length wd - k))")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(case_tac "length wd - k")
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="butn wd 0"
      and s="wd"
      in ssubst)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(simp add: butn_def)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd nat)(*strict*)
  apply(clarsimp)
  apply(simp add: butn_def)
  apply(clarsimp)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) (length wd - Suc nat)"
      and s="parser_fixed_input_length_recN dh i - length wa"
      in ssubst)
  apply(rename_tac i ea ci w wa wd nat)(*strict*)
  apply(rule Orderings.min_absorb1)
  apply(force)
  apply(rename_tac i ea ci w wa wd nat)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="length (butn wd (length wd - k))"
      and s="length wd - (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_length)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(rule_tac
      On="parser_fixed_input_length_recN dh n"
      in help_lemma1)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  prefer 4
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule sym)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_Overhead_prime_prime)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      d="dh"
      and MARK="MARK"
      in PARSER_possibility_of_restriction_EffectOverhead_derivation_prime_prime_prime)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule PARSER_not_DetectsEnd_never_see_bottom)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh i < length (parserS_conf_scheduler ci)")
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(rule PARSER_not_DetectsEnd_never_see_bottom)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]\<rparr>) c"
      in exI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]\<rparr>) c'"
      in exI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule conjI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler (c'\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c')) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]\<rparr>)"
      and s="butn (butlast (parserS_conf_scheduler c')) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]\<rparr>)) i"
      and s="parser_fixed_input_length_recN dh i"
      in ssubst)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule sym)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_Overhead_prime_prime)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_derivation_prime_prime_prime)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule PARSER_not_DetectsEnd_never_see_bottom)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "i\<le>n")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(case_tac "i\<le>n")
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(rule_tac
      m="i"
      in parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state c'")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c' = w @ parserS_string_state ca")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c'=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(simp only: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="wa @ wb @ [parser_bottom M]"
      and s="(wa @ wb) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((wa @ wb) @ [parser_bottom M])"
      and s="wa@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="w @ (wa @ wb) @ [parser_bottom M]"
      and s="(w@wa @ wb) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((w@ wa @ wb) @ [parser_bottom M])"
      and s="w@wa@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb) (length wb - k)"
      and s="wa@butn wb (length wb - k)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (w @ wa @ wb) (length wb - k)"
      and s="(w@wa)@butn wb (length wb - k)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="w@wa@wb"
      and s="(w@wa)@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(rule conjI)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((wa @ butn wb (length wb - k)) @ MARK @ [parser_bottom M])"
      and s="(wa @ butn wb (length wb - k)) @ MARK"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc_2)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN dh i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN dh (i+(n-i)))")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "length (butn wb (length wb - k)) = length wb - (length wb - k)")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "(parser_fixed_input_length_recN dh i) - length wa - (length wb - (length wb - k)) = 0")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(case_tac "length wb-k")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(simp add: butn_def)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(rule_tac
      t="butn wb (length wb - k)"
      and s="take k wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(rule butn_take)
  apply(force)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parser_fixed_input_length_recN dh i - length wa \<le> k")
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) k"
      and s="parser_fixed_input_length_recN dh i - length wa"
      in ssubst)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parser_fixed_input_length_recN dh i < length (parserS_conf_scheduler c')")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(rule PARSER_not_DetectsEnd_never_see_bottom)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_length)
  done

lemma PARSER_maximal_context_preserves_effect_prime_prime_prime_prime: "
  valid_parser M
  \<Longrightarrow> dh 0 = Some (pair None c)
  \<Longrightarrow> c \<in> parserS_configurations M
  \<Longrightarrow> parserS.belongs M dh
  \<Longrightarrow> parserS.derivation M dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> dh n = Some (pair e ca)
  \<Longrightarrow> parser_fixed_input_length_recN dh n < length(parserS_conf_scheduler ca)
  \<Longrightarrow> k\<ge>parser_fixed_input_length_recN dh n
  \<Longrightarrow> parserS_conf_scheduler c = w @ parserS_conf_scheduler ca
  \<Longrightarrow> parserS_unmarked_effect M (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast(parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>)) = parserS_unmarked_effect M dh"
  apply(rule order_antisym)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(subgoal_tac "i\<le>n")
  apply(rename_tac cb c' i ea v)(*strict*)
  prefer 2
  apply(case_tac "i\<le>n")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(rule_tac
      m="i"
      in parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(subgoal_tac "cb=(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>)c")
  apply(rename_tac cb c' i ea v)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(thin_tac "derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>) 0 = Some (pair None cb)")
  apply(rename_tac cb c' i ea v)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(case_tac a)
  apply(rename_tac c' i ea v a option b)(*strict*)
  apply(rename_tac ei ci)
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(subgoal_tac "Some (pair ei ((\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>)ci)) = Some (pair ea c')")
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  prefer 2
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(thin_tac "derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k)@MARK@[parser_bottom M]\<rparr>) i = Some (pair ea c')")
  apply(rename_tac c' i ea v a ei ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea v ci)(*strict*)
  apply(rule_tac
      x="ci"
      in exI)
  apply(rule_tac
      x="i"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state ci")
  apply(rename_tac i ea v ci)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state ci = w @ parserS_string_state ca")
  apply(rename_tac i ea v ci)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ci=w@[parser_bottom M]")
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  prefer 2
  apply(simp only: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac i ea v ci w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac wd)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wd @ [parser_bottom M])"
      and s="wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="wa @ wd @ [parser_bottom M]"
      and s="(wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length wd - k) @ MARK@ [parser_bottom M]\<rparr>)) i"
      and s="parser_fixed_input_length_recN dh i"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  defer
  apply(subgoal_tac "v=w")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  prefer 2
  apply(case_tac "v=w")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "v @ butn (butlast (wa @ wd @ [parser_bottom M])) (length wd - k) \<noteq> butn (butlast (w @ wa @ wd @ [parser_bottom M])) (length wd - k)")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (w @ wa @ wd @ [parser_bottom M])"
      and s="w@wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="w @ wa @ wd @ [parser_bottom M]"
      and s="(w @ wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (wa @ wd @ [parser_bottom M])"
      and s="wa@wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="wa @ wd @ [parser_bottom M]"
      and s="(wa @ wd) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (wa @ wd) (length wd - k)"
      and s="wa@butn wd (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (w @ wa @ wd) (length wd - k)"
      and s="(w@wa)@butn wd (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="w @ wa @ wd"
      and s="(w @ wa) @ wd"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(thin_tac "v @ butn (butlast (wa @ wd @ [parser_bottom M])) (length wd - k) = butn (butlast (w @ wa @ wd @ [parser_bottom M])) (length wd - k)")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="v"
      and s="w"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butlast (butn (wa @ wd) (length wd - k) @ MARK @ [parser_bottom M])"
      and s="butlast ((butn (wa @ wd) (length wd - k) @ MARK) @ [parser_bottom M])"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="(butlast ((butn (wa @ wd) (length wd - k) @ MARK) @ [parser_bottom M]))"
      and s="butn (wa @ wd) (length wd - k) @ MARK"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="butn (wa @ wd) (length wd - k)"
      and s="wa@butn wd (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="(wa @ butn wd (length wd - k)) @ MARK"
      and s="wa @ butn wd (length wd - k) @ MARK"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler ci) - (parser_fixed_input_length_recN dh i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN dh (i+(n-i)))")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh i - length wa \<le> length (butn wd (length wd - k))")
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(case_tac "length wd - k")
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="butn wd 0"
      and s="wd"
      in ssubst)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(simp add: butn_def)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd nat)(*strict*)
  apply(clarsimp)
  apply(simp add: butn_def)
  apply(clarsimp)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) (length wd - Suc nat)"
      and s="parser_fixed_input_length_recN dh i - length wa"
      in ssubst)
  apply(rename_tac i ea ci w wa wd nat)(*strict*)
  apply(rule Orderings.min_absorb1)
  apply(force)
  apply(rename_tac i ea ci w wa wd nat)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      t="length (butn wd (length wd - k))"
      and s="length wd - (length wd - k)"
      in ssubst)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule butn_length)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(clarsimp)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(rule_tac
      On="parser_fixed_input_length_recN dh n"
      in help_lemma1)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  prefer 4
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule sym)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_Overhead_prime_prime)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(rule_tac
      c'="ca"
      and d="dh"
      and MARK="MARK"
      in PARSER_possibility_of_restriction_EffectOverhead_derivation_prime_prime_prime_prime)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea v ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(rename_tac i ea ci w wa wd)(*strict*)
  apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]\<rparr>) c"
      in exI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="(\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]\<rparr>) c'"
      in exI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule conjI)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler (c'\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c')) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]\<rparr>)"
      and s="butn (butlast (parserS_conf_scheduler c')) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length (parserS_conf_scheduler ca) - Suc k) @ MARK@ [parser_bottom M]\<rparr>)) i"
      and s="parser_fixed_input_length_recN dh i"
      in ssubst)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule sym)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_Overhead_prime_prime)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_derivation_prime_prime_prime_prime)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "i\<le>n")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(case_tac "i\<le>n")
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(case_tac "dh i")
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(rule_tac
      m="i"
      in parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v a)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state c'")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(rule_tac
      j="i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c' = w @ parserS_string_state ca")
  apply(rename_tac c' i ea v)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(force)
  apply(rename_tac c' i ea v)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler ca=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c'=w@[parser_bottom M]")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(simp only: parserS.belongs_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="wa @ wb @ [parser_bottom M]"
      and s="(wa @ wb) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((wa @ wb) @ [parser_bottom M])"
      and s="wa@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="w @ (wa @ wb) @ [parser_bottom M]"
      and s="(w@wa @ wb) @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((w@ wa @ wb) @ [parser_bottom M])"
      and s="w@wa@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (wa @ wb) (length wb - k)"
      and s="wa@butn wb (length wb - k)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butn (w @ wa @ wb) (length wb - k)"
      and s="(w@wa)@butn wb (length wb - k)"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="w@wa@wb"
      and s="(w@wa)@wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_shift)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(rule conjI)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule_tac
      t="butlast ((wa @ butn wb (length wb - k)) @ MARK @ [parser_bottom M])"
      and s="(wa @ butn wb (length wb - k)) @ MARK"
      in ssubst)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butlast_snoc_2)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN dh i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN dh (i+(n-i)))")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "length (butn wb (length wb - k)) = length wb - (length wb - k)")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "(parser_fixed_input_length_recN dh i) - length wa - (length wb - (length wb - k)) = 0")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(case_tac "length wb-k")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(simp add: butn_def)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(rule_tac
      t="butn wb (length wb - k)"
      and s="take k wb"
      in ssubst)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(rule butn_take)
  apply(force)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parser_fixed_input_length_recN dh i - length wa \<le> k")
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(rule_tac
      t="min (parser_fixed_input_length_recN dh i - length wa) k"
      and s="parser_fixed_input_length_recN dh i - length wa"
      in ssubst)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb nat)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh i < length (parserS_conf_scheduler c')")
  apply(rename_tac c' i ea w wa wb)(*strict*)
  prefer 2
  apply(rule_tac
      cn="ca"
      in PARSER_not_seen_entire_shifts_back)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(force)
  apply(rename_tac c' i ea w wa wb)(*strict*)
  apply(rule butn_length)
  done

lemma PARSER_derivation_drop_parser_fixed_input_length_recN: "
  parser_fixed_input_length_recN (derivation_drop dh na) m \<le> parser_fixed_input_length_recN dh (na + m)"
  apply(induct m)
  apply(clarsimp)
  apply(rename_tac m)(*strict*)
  apply(clarsimp)
  apply(case_tac "dh (Suc (na + m))")
  apply(rename_tac m)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_drop_def)
  apply(rule_tac
      t="m+na"
      and s="na+m"
      in ssubst)
  apply(rename_tac m)(*strict*)
  apply(force)
  apply(rename_tac m)(*strict*)
  apply(clarsimp)
  apply(fold derivation_drop_def)
  apply(force)
  apply(rename_tac m a)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_drop_def)
  apply(rule_tac
      t="m+na"
      and s="na+m"
      in ssubst)
  apply(rename_tac m a)(*strict*)
  apply(force)
  apply(rename_tac m a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac m a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac m option b)(*strict*)
  apply(case_tac option)
  apply(rename_tac m option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac m b)(*strict*)
  apply(fold derivation_drop_def)
  apply(force)
  apply(rename_tac m option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac m b a)(*strict*)
  apply(case_tac "(parser_fixed_input_length_recN (derivation_drop dh na) m) \<ge> (length (rule_rpop a))")
  apply(rename_tac m b a)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN (derivation_drop dh na) m) (length (rule_rpop a))"
      and s="(parser_fixed_input_length_recN (derivation_drop dh na) m)"
      in ssubst)
  apply(rename_tac m b a)(*strict*)
  apply(force)
  apply(rename_tac m b a)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN dh (na + m)) (length (rule_rpop a))"
      and s="(parser_fixed_input_length_recN dh (na + m))"
      in ssubst)
  apply(rename_tac m b a)(*strict*)
  apply(force)
  apply(rename_tac m b a)(*strict*)
  apply(force)
  apply(rename_tac m b a)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN (derivation_drop dh na) m) (length (rule_rpop a))"
      and s="(length (rule_rpop a))"
      in ssubst)
  apply(rename_tac m b a)(*strict*)
  apply(force)
  apply(rename_tac m b a)(*strict*)
  apply(case_tac "(parser_fixed_input_length_recN dh (na + m)) \<le> (length (rule_rpop a))")
  apply(rename_tac m b a)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN dh (na + m)) (length (rule_rpop a))"
      and s="(length (rule_rpop a))"
      in ssubst)
  apply(rename_tac m b a)(*strict*)
  apply(force)
  apply(rename_tac m b a)(*strict*)
  apply(force)
  apply(rename_tac m b a)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN dh (na + m)) (length (rule_rpop a))"
      and s="(parser_fixed_input_length_recN dh (na + m))"
      in ssubst)
  apply(rename_tac m b a)(*strict*)
  apply(force)
  apply(rename_tac m b a)(*strict*)
  apply(force)
  done

lemma PARSER_indistinguishable_entirely_read_input_implies_certain_close_state_relationship: "
  valid_parser M
  \<Longrightarrow> \<not> parser_observes_input_terminator M
  \<Longrightarrow> \<not> parserS_marking_condition M (derivation_map dh Cnv)
  \<Longrightarrow> Cnv = (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn(butlast(parserS_conf_scheduler c))((length(parserS_conf_scheduler dhcn)) - Suc(parser_fixed_input_length_recN dh n))@[parser_bottom M]\<rparr>)
  \<Longrightarrow> parserS.is_forward_deterministic M
  \<Longrightarrow> parserS_conf_stack dic = dic_stack @ [f]
  \<Longrightarrow> f \<in> parser_marking M
  \<Longrightarrow> dh 0 = Some (pair None dhc0)
  \<Longrightarrow> parserS.derivation M dh
  \<Longrightarrow> d i = Some (pair die dic)
  \<Longrightarrow> parserS_conf_scheduler dic = [parser_bottom M]
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.belongs M dh
  \<Longrightarrow> dh n = Some (pair e dhcn)
  \<Longrightarrow> parserS_conf_scheduler dhc0 = w @ parserS_conf_scheduler dhcn
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> d 0 = Some (pair None dc0)
  \<Longrightarrow> C = (\<lambda>c. c\<lparr>parserS_conf_scheduler:=butn(butlast(parserS_conf_scheduler c))((length(parserS_conf_scheduler dhcn)) - Suc(parser_fixed_input_length_recN dh n))@v@[parser_bottom M]\<rparr>)
  \<Longrightarrow> dc0 = C dhc0
  \<Longrightarrow> x\<le>n
  \<Longrightarrow> dh x = Some (pair e' dhcx)
  \<Longrightarrow> Cdhcx=(C dhcx)
  \<Longrightarrow> d x = Some (pair e' Cdhcx)"
  (*
  dh
    0: dhc0=w.dhcn
    x: dhcx
    n: dhcn
  d
    0: dc0 = dc0(w.v.$)
    x: dhcx(dhcx-dhcn.v)
*)
  apply(induct x arbitrary: e' Cdhcx dhcx rule: nat_less_induct)
  apply(rename_tac na e' Cdhcx dhcx)(*strict*)
  apply(clarsimp)
  apply(rename_tac na e' dhcx)(*strict*)
  apply(case_tac na)
  apply(rename_tac na e' dhcx)(*strict*)
  apply(clarsimp)
  apply(rename_tac na e' dhcx nat)(*strict*)
  apply(rename_tac x)
  apply(rename_tac na e' dhcx x)(*strict*)
  apply(case_tac "dhc0")
  apply(rename_tac na e' dhcx x parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac e' dhcx x parserS_conf_stacka)(*strict*)
  apply(rule sym)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh x = Some (pair e1 c1) \<and> dh (Suc x) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac e' dhcx x parserS_conf_stacka)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc x"
      in parserS.step_detail_before_some_position)
  apply(rename_tac e' dhcx x parserS_conf_stacka)(*strict*)
  apply(force)
  apply(rename_tac e' dhcx x parserS_conf_stacka)(*strict*)
  apply(force)
  apply(rename_tac e' dhcx x parserS_conf_stacka)(*strict*)
  apply(force)
  apply(rename_tac e' dhcx x parserS_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>w''. parserS_string_state \<lparr>parserS_conf_stack = parserS_conf_stacka, parserS_conf_scheduler = w @ parserS_conf_scheduler dhcn\<rparr> = w'' @ (parserS_string_state c1)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  prefer 2
  apply(rule_tac
      d="dh"
      and j="x"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  apply(subgoal_tac "\<exists>w''. parserS_string_state c1 = w'' @ (parserS_string_state dhcx)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  prefer 2
  apply(rule_tac
      d="dh"
      and j="Suc 0"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'')(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  apply(subgoal_tac "\<exists>w''. parserS_string_state dhcx = w'' @ (parserS_string_state dhcn)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  prefer 2
  apply(rule_tac
      d="dh"
      and j="n-(Suc x)"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler dhcn = w @ [parser_bottom M]")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="n"
      and P="\<lambda>n. case dh n of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> parser_step_labels M) \<and> c \<in> parserS_configurations M"
      in allE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(case_tac "d (Suc x)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "i\<le>x")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  prefer 2
  apply(case_tac "i\<le>x")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(subgoal_tac "i>x")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(clarsimp)
  apply(case_tac "Suc x=i")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(rule_tac
      i="Suc x"
      and d="d"
      and n="i"
      in parserS.derivationNoFromNone2)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state dic = w @ parserS_string_state (c1\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c1)) (length wa - parser_fixed_input_length_recN dh n) @ v @ [parser_bottom M]\<rparr>)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  prefer 2
  apply(rule_tac
      j="x-i"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa waa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c1= w @ parserS_string_state dhcn")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  prefer 2
  apply(rule_tac
      j="n-x"
      and d="dh"
      in parserS.derivation_monotonically_dec)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler dhcn=w@[parser_bottom M]")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh i = Some (pair e c)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  prefer 2
  apply(rule_tac
      m="x"
      in parserS.pre_some_position_is_some_position)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w)(*strict*)
  apply(erule exE)+
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(erule disjE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack = parserS_conf_stacka, parserS_conf_scheduler = w'' @ w''a @ w''b @ w @ [parser_bottom M]\<rparr>\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler \<lparr>parserS_conf_stack = parserS_conf_stacka, parserS_conf_scheduler = w'' @ w''a @ w''b @ w @ [parser_bottom M]\<rparr>)) (length w - parser_fixed_input_length_recN dh n) @ [parser_bottom M]\<rparr>"
      in allE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(erule impE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="0"
      and P="\<lambda>x. case d x of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> parser_step_labels M) \<and> c \<in> parserS_configurations M"
      in allE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(erule_tac
      x="i"
      and P="\<lambda>i. \<forall>e c. derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length w - parser_fixed_input_length_recN dh n) @ [parser_bottom M]\<rparr>) i = Some (pair e c) \<longrightarrow> c \<notin> parserS_marking_configurations M"
      in allE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(erule_tac
      x="ea"
      in allE)
  apply(erule_tac
      x="c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length w - parser_fixed_input_length_recN dh n) @ [parser_bottom M]\<rparr>"
      in allE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(erule impE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(simp add: derivation_map_def)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w ea c)(*strict*)
  apply(simp add: parserS_marking_configurations_def)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w c)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="i"
      and P="\<lambda>i. case d i of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> parser_step_labels M) \<and> c \<in> parserS_configurations M"
      in allE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w c)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w wa)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d x = Some (pair e1 c1) \<and> d (Suc x) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa a)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc x"
      in parserS.step_detail_before_some_position)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa a)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(case_tac "i<Suc x")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh i = Some (pair e c)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  prefer 2
  apply(rule parserS.some_position_has_details_before_max_dom)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(blast)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(blast)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(arith)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(erule disjE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(simp add: derivation_map_def)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="0"
      and P="\<lambda>i. case dh i of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> parser_step_labels M) \<and> c \<in> parserS_configurations M"
      in allE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(subgoal_tac "butlast (w'' @ w''a @ w''b @ wa @ [parser_bottom M]) = w'' @ w''a @ w''b @ wa")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(erule impE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(rule_tac
      B="set (w'' @ w''a @ w''b @ wa)"
      in subset_trans)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply (metis set_butn_subset)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(subgoal_tac "parser_bottom M \<notin> set (butn (w'' @ w''a @ w''b @ wa) (length wa - parser_fixed_input_length_recN dh n))")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2 c)(*strict*)
  apply(rule_tac
      B="set (w'' @ w''a @ w''b @ wa)"
      in nset_mp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 c)(*strict*)
  apply(rule set_butn_subset)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 c)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 c)(*strict*)
  apply(simp add: butlast_append)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 c)(*strict*)
  apply(erule_tac
      x="i"
      and P="\<lambda>i. \<forall>e c. derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length w - parser_fixed_input_length_recN dh n) @ [parser_bottom M]\<rparr>) i = Some (pair e c) \<longrightarrow> c \<notin> parserS_marking_configurations M"
      in allE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 c)(*strict*)
  apply(simp add: derivation_map_def)
  apply(simp add: parserS_marking_configurations_def)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 c)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="i"
      and P="\<lambda>i. case dh i of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> parser_step_labels M) \<and> c \<in> parserS_configurations M"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def valid_parser_def)
  apply(clarsimp)
  apply (metis bot_least insert_subset list.set(1) list.set(2))
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(subgoal_tac "i\<ge>Suc x")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(thin_tac "\<not> i < Suc x")
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(subgoal_tac "\<forall>xy xa. dh x = Some (pair xy xa) \<longrightarrow> d x = Some (pair xy (xa\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler xa)) (length w - parser_fixed_input_length_recN dh n) @ v @ [parser_bottom M]\<rparr>))")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  prefer 2
  apply(erule_tac
      x="x"
      in allE)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b wa e2a c2)(*strict*)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(simp add: butlast_append)
  apply(simp add: butn_shift)
  apply(subgoal_tac "rule_rpop e2 = w''a @ rule_rpush e2")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  prefer 2
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(subgoal_tac "e2=e2a")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh n < length (parserS_conf_scheduler dhcn)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  prefer 2
  apply(rule PARSER_not_DetectsEnd_never_see_bottom)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "butn w (length w - parser_fixed_input_length_recN dh n) = take (parser_fixed_input_length_recN dh n) w")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  prefer 2
  apply(rule butn_take)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(clarsimp)
  apply(thin_tac "\<not> parserS_marking_condition M (derivation_map dh (\<lambda>c. c\<lparr>parserS_conf_scheduler := butn (butlast (parserS_conf_scheduler c)) (length w - parser_fixed_input_length_recN dh n) @ [parser_bottom M]\<rparr>))")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(erule_tac
      x="x"
      in allE)
  apply(clarsimp)
  apply(case_tac "\<exists>X. rule_rpop e2 @ X = w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  prefer 2
  apply(subgoal_tac "prefix (w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w) (rule_rpop e2) \<or> prefix (rule_rpop e2) (w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  prefer 2
  apply(simp add: parserS_step_relation_def)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 xa xb xc xd)(*strict*)
  apply(erule conjE)+
  apply(rule_tac
      d="xb"
      and b="drop (parser_fixed_input_length_recN dh n) w @ [parser_bottom M]"
      in mutual_prefix_prefix)
  apply(clarsimp)
  apply(rule_tac
      t="rule_rpush e2 @ xb"
      and s="w''b @ w @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 xa xb xc xd)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 xa xb xc xd)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(erule disjE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 c)(*strict*)
  apply(case_tac c1)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 c parserS_conf_stackaa parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa)(*strict*)
  apply(simp add: butlast_append)
  apply(case_tac c)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(subgoal_tac "length (rule_rpush e2) > length w''b + parser_fixed_input_length_recN dh n")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  prefer 2
  apply(rule_tac
      y="length(w''b @ take (parser_fixed_input_length_recN dh n) w @ (a#list))"
      in less_le_trans)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler dhcx) - (parser_fixed_input_length_recN dh (Suc x)) \<ge> length (parserS_conf_scheduler dhcn) - (parser_fixed_input_length_recN dh ((Suc x)+(n-Suc x)))")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  prefer 2
  apply(rule PARSER_UnseenPartStrictlyDecreases)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh (Suc x) \<ge> length (rule_rpush e2)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  prefer 2
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_minimum)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 w'' w''a w''b w e2a c2 c parserS_conf_stackaa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  apply(subgoal_tac "(\<forall>c c1 c2 e1 e2. parserS_step_relation M c e1 c1 \<and> parserS_step_relation M c e2 c2 \<longrightarrow> e1 = e2)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  prefer 2
  apply(simp add: parserS.is_forward_deterministic_def parserS.is_forward_edge_deterministic_def)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  apply(subgoal_tac "\<And>c c1 e1 e2. parserS_step_relation M c e1 c1 \<Longrightarrow> \<exists>c2. parserS_step_relation M c e2 c2 \<Longrightarrow> e1 = e2")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  prefer 2
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X c c1a e1a e2b)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  apply(thin_tac "\<forall>c c1 c2 e1 e2. parserS_step_relation M c e1 c1 \<and> parserS_step_relation M c e2 c2 \<longrightarrow> e1 = e2")
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule_tac
      x="dhcx"
      in meta_allE)
  apply(erule_tac
      x="e2"
      in meta_allE)
  apply(erule_tac
      x="e2a"
      in meta_allE)
  apply(erule meta_impE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(subgoal_tac "(\<exists>xb. xa @ rule_lpop e2 = xb @ rule_lpop e2a) \<and> (\<exists>xa. w''a @ rule_rpush e2 @ xb = rule_rpop e2a @ xa)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xd xba xaa)(*strict*)
  apply(rule_tac
      x="\<lparr>parserS_conf_stack=xba @ rule_lpush e2a, parserS_conf_scheduler=rule_rpush e2a @ xaa\<rparr>"
      in exI)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(rule conjI)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(rule_tac
      t="xa @ rule_lpop e2"
      and s="xc @ rule_lpop e2a"
      in ssubst)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(rule_tac
      x="xc"
      in exI)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(rule_tac
      t="rule_rpush e2 @ xb"
      and s="w''b @ w @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(case_tac "xb")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(simp add: parser_observes_input_terminator_def)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd)(*strict*)
  apply(subgoal_tac "parser_bottom M \<in> set (rule_rpush e2)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd)(*strict*)
  apply(rule_tac
      t="rule_rpush e2"
      and s="w''b @ w @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xb xc xd a list)(*strict*)
  apply(thin_tac "xb=a#list")
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(rule_tac
      t="w''a @ rule_rpush e2 @ w' @ [parser_bottom M]"
      and s="w''a @ w''b @ w @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(subgoal_tac "prefix (rule_rpop e2a) (w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w) \<or> (prefix (w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w) (rule_rpop e2a) \<and> ((w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w) \<noteq>(rule_rpop e2a)))")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  prefer 2
  apply(subgoal_tac "prefix (rule_rpop e2a) (w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w) \<or> (prefix (w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w) (rule_rpop e2a))")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  prefer 2
  apply(rule_tac
      b="xd"
      and d="v @ [parser_bottom M]"
      in mutual_prefix_prefix)
  apply(rule sym)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(erule disjE)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(simp add: prefix_def)
  apply(rule_tac
      t="w"
      and s="take (parser_fixed_input_length_recN dh n) w @ (drop (parser_fixed_input_length_recN dh n) w)"
      in ssubst)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(erule exE)+
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c)(*strict*)
  apply(rule_tac
      t="w''a @ w''b @ (take (parser_fixed_input_length_recN dh n) w @ drop (parser_fixed_input_length_recN dh n) w) @ [parser_bottom M]"
      and s="(w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w) @ drop (parser_fixed_input_length_recN dh n) w @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c)(*strict*)
  apply(rule_tac
      t="w''a @ w''b @ take (parser_fixed_input_length_recN dh n) w"
      and s="rule_rpop e2a @ c"
      in ssubst)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c)(*strict*)
  apply(rule_tac
      x="c @ drop (parser_fixed_input_length_recN dh n) w @ [parser_bottom M]"
      in exI)
  apply(simp (no_asm))
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w')(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c)(*strict*)
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c a list)(*strict*)
  apply(subgoal_tac "c\<noteq>[]")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c a list)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c a list)(*strict*)
  apply(thin_tac "c=a#list")
  apply(thin_tac "parserS_conf_stack dic = dic_stack @ [f]")
  apply(thin_tac "f \<in> parser_marking M")
  apply(thin_tac "dh 0 = Some (pair None \<lparr>parserS_conf_stack = parserS_conf_stacka, parserS_conf_scheduler = w'' @ w''a @ rule_rpush e2 @ w' @ [parser_bottom M]\<rparr>)")
  apply(rename_tac dhcx x parserS_conf_stacka e1 e2 c1 w'' w''a w''b w e2a c2 X xa xc xd w' c a list)(*strict*)
  apply(thin_tac "d i = Some (pair die dic)")
  apply(thin_tac "parserS_conf_scheduler dic = [parser_bottom M]")
  apply(thin_tac "Suc x \<le> i")
  apply(clarsimp)
  apply(rename_tac dhcx x e1 e2 c1 w''a w''b w e2a c2 X xa xc xd w' c)(*strict*)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w7 w8 w9)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w7 w8 w9)(*strict*)
  apply(case_tac w7)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w7 w8 w9)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(case_tac dhcx)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(force)
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(simp add: parser_observes_input_terminator_def)
  apply(erule_tac
      x="de'"
      in ballE)
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(subgoal_tac "parser_bottom M \<in> set (rule_rpop de')")
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(force)
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(rule_tac
      t="rule_rpop de'"
      and s="w1 @ w2 @ take (parser_fixed_input_length_recN dh n) w3 @ v @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(force)
  apply(rename_tac dhcx' x dhe dhe' w1 w2 w3 de' dcx' w4 w5 w6 w8 w9)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w7 w8 w9 a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w7 = w' @ [x']")
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w7 w8 w9 a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w7 w8 w9 a list)(*strict*)
  apply(thin_tac "w7=a#list")
  apply(clarsimp)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w')(*strict*)
  apply(rename_tac w7)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(simp add: butlast_append)
  apply(rule_tac
      t="rule_rpop de'"
      and s="w1 @ w2 @ take (parser_fixed_input_length_recN dh n) w3 @ w9"
      in ssubst)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(force)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(simp (no_asm))
  apply(subgoal_tac "de'=dhe'")
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(case_tac de')
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7 rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(case_tac dhe')
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7 rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(subgoal_tac "(\<forall>c c1 c2 e1 e2. parserS_step_relation M c e1 c1 \<and> parserS_step_relation M c e2 c2 \<longrightarrow> e1 = e2)")
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  prefer 2
  apply(simp add: parserS.is_forward_deterministic_def parserS.is_forward_edge_deterministic_def)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack=w6@rule_lpop de', parserS_conf_scheduler=w1 @ w2 @ take (parser_fixed_input_length_recN dh n) w3 @ w9\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack=w6@rule_lpush de', parserS_conf_scheduler=rule_rpush de'\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack=w5@rule_lpush dhe', parserS_conf_scheduler=w2 @ take (parser_fixed_input_length_recN dh n) w3 @ w9\<rparr>"
      in allE)
  apply(erule_tac
      x="de'"
      in allE)
  apply(erule_tac
      x="dhe'"
      in allE)
  apply(erule impE)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(rule conjI)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(rule_tac
      t="rule_rpop de'"
      and s="w1 @ w2 @ take (parser_fixed_input_length_recN dh n) w3 @ w9"
      in ssubst)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(force)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(simp (no_asm))
  apply(subgoal_tac "\<exists>x. w2 @ take (parser_fixed_input_length_recN dh n) w3 = rule_rpush dhe' @ x")
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(clarsimp)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w5 w6 w8 w9 w7 xa)(*strict*)
  apply(rule_tac
      x="xa@w9"
      in exI)
  apply(clarsimp)
  apply(rename_tac dhcx' x dhe dhe' dhcx w1 w2 w3 de' dcx' w4 w5 w6 w8 w9 w7)(*strict*)
  apply(rule_tac
      x="w4"
      in exI)
  apply(force)
  done

corollary weakening_of_fake_correspond_assumption: "
  valid_parser M
  \<Longrightarrow> \<not> parser_observes_input_terminator M
  \<Longrightarrow> Collect (parserS_entire_input_observed M) \<subseteq> Collect (parserS.Nonblockingness_configuration M)"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: parserS_entire_input_observed_def)
  apply(clarsimp)
  apply(rename_tac x d e n)(*strict*)
  apply(subgoal_tac "False")
  apply(rename_tac x d e n)(*strict*)
  apply(force)
  apply(rename_tac x d e n)(*strict*)
  apply(subgoal_tac " \<exists>k\<le>n. (\<forall>i<k. \<not> (\<lambda>n. case d n of Some (pair e c) \<Rightarrow> parser_fixed_input_length_recN d n = length (parserS_conf_scheduler c) | _ \<Rightarrow> True) i) \<and> (\<lambda>n. case d n of Some (pair e c) \<Rightarrow> parser_fixed_input_length_recN d n = length (parserS_conf_scheduler c) | _ \<Rightarrow> True) k ")
  apply(rename_tac x d e n)(*strict*)
  prefer 2
  apply(rule ex_least_nat_le_prime)
  apply(clarsimp)
  apply(rename_tac x d e n)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n k)(*strict*)
  apply(subgoal_tac "\<exists>e c. d k = Some (pair e c)")
  apply(rename_tac x d e n k)(*strict*)
  prefer 2
  apply(rule parserS.some_position_has_details_before_max_dom)
  apply(rename_tac x d e n k)(*strict*)
  apply(blast)
  apply(rename_tac x d e n k)(*strict*)
  apply(blast)
  apply(rename_tac x d e n k)(*strict*)
  apply(arith)
  apply(rename_tac x d e n k)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n k ea c)(*strict*)
  apply(subgoal_tac "c \<in> parserS_configurations M ")
  apply(rename_tac x d e n k ea c)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="k"
      and P="\<lambda>k. case d k of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> parser_step_labels M) \<and> c \<in> parserS_configurations M"
      in allE)
  apply(rename_tac x d e n k ea c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n k ea c)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d e n k ea l w)(*strict*)
  apply(case_tac k)
  apply(rename_tac x d e n k ea l w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n k ea l w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n ea l w nat)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
  apply(rename_tac x d e n ea l w nat)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
  apply(rename_tac x d e n ea l w nat)(*strict*)
  apply(force)
  apply(rename_tac x d e n ea l w nat)(*strict*)
  apply(force)
  apply(rename_tac x d e n ea l w nat)(*strict*)
  apply(force)
  apply(rename_tac x d e n ea l w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n l w nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "c1 \<in> parserS_configurations M ")
  apply(rename_tac x d e n l w nat e1 e2 c1)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(rename_tac x d e n l w nat e1 e2 c1)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d e n l w nat e1 e2 la wa)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb)(*strict*)
  apply(subgoal_tac "valid_parser_step_label M e2")
  apply(rename_tac x d e n w nat e1 e2 wa xa xb)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc nat"
      in allE)
  apply(clarsimp)
  apply(simp add: valid_parser_def)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd)(*strict*)
  apply(case_tac "(\<exists>x. x @ [parser_bottom M] = kPrefix k (wb @ [parser_bottom M]))")
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length wb")
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parser_bottom M \<in> set wb")
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(force)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(rule_tac
      A="set (take k wb)"
      in set_mp)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(rule set_take_subset2)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(rule_tac
      t="take k wb"
      and s="xe@[parser_bottom M]"
      in ssubst)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(force)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(simp (no_asm_use) only: set_append set_Cons)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(rule_tac
      t="take k wb"
      and s="xe @ [parser_bottom M]"
      in ssubst)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(force)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe)(*strict*)
  apply(simp (no_asm))
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc xe nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc nata)(*strict*)
  apply(simp add: parser_observes_input_terminator_def)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd xc nata)(*strict*)
  apply(force)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd)(*strict*)
  apply(clarsimp)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length wb")
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd)(*strict*)
  prefer 2
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd nata)(*strict*)
  apply(force)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd)(*strict*)
  apply(clarsimp)
  apply(case_tac xb)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd)(*strict*)
  apply(force)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac x d e n w nat e1 e2 wa xa xb k wb xd a list)(*strict*)
  apply(thin_tac "xb=a#list")
  apply(clarsimp)
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  apply(subgoal_tac "min (length wb) k = k")
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (rule_rpush e2) \<le> k")
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  prefer 2
  apply(rule_tac
      j="length (xd @ rule_rpush e2)"
      in le_trans)
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  apply(simp (no_asm))
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  apply(rule_tac
      j="length (take k wb)"
      in le_trans)
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  apply(force)
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  apply(force)
  apply(rename_tac x d e n nat e1 e2 xa k wb xd w')(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e n nat e1 e2 xa k xd w')(*strict*)
  apply(case_tac "(parser_fixed_input_length_recN d nat) \<ge> k")
  apply(rename_tac x d e n nat e1 e2 xa k xd w')(*strict*)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) k = (parser_fixed_input_length_recN d nat)")
  apply(rename_tac x d e n nat e1 e2 xa k xd w')(*strict*)
  apply(force)
  apply(rename_tac x d e n nat e1 e2 xa k xd w')(*strict*)
  apply(force)
  apply(rename_tac x d e n nat e1 e2 xa k xd w')(*strict*)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) k = k")
  apply(rename_tac x d e n nat e1 e2 xa k xd w')(*strict*)
  apply(force)
  apply(rename_tac x d e n nat e1 e2 xa k xd w')(*strict*)
  apply(force)
  done

lemma conflicts_translate_step_enabledness: "
  valid_parser P
  \<Longrightarrow> r1 \<in> parser_rules P
  \<Longrightarrow> r2 \<in> parser_rules P
  \<Longrightarrow> suffix (rule_lpop r2) (rule_lpop r1)
  \<Longrightarrow> prefix (rule_rpop r1) (rule_rpop r2)
  \<Longrightarrow> parserS_step_relation P c r2 c'
  \<Longrightarrow> \<exists>c'. parserS_step_relation P c r1 c'"
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x xa ca caa)(*strict*)
  apply(rule_tac
      x="\<lparr>parserS_conf_stack=x @ ca @ rule_lpush r1, parserS_conf_scheduler=SSr\<rparr>" for SSr
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="caa@xa"
      in exI)
  apply(clarsimp)
  apply(force)
  done

definition parser_no_empty_steps_from_marking_states :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> bool"
  where
    "parser_no_empty_steps_from_marking_states G \<equiv>
  \<forall>e. e \<in> parser_rules G
  \<longrightarrow> last (rule_lpop e) \<in> parser_marking G
  \<longrightarrow> rule_rpop e \<noteq> []"

theorem parserHF_dependency_between_determinism_properties: "
  valid_parser G
  \<Longrightarrow>
  parserHF.is_forward_target_deterministic_accessible G
  \<and> (parserHF.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> parserHF.is_forward_target_deterministicHist_SB G)
  \<and> (parserHF.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> parserHF.is_forward_target_deterministicHist_DB G)
  \<and> (parserHF.is_forward_target_deterministicHist_SB G
  \<longleftrightarrow> parserHF.is_forward_target_deterministicHist_DB G)
  \<and> (parserHF.is_forward_edge_deterministic_accessible G
  \<longrightarrow> parserHF.is_forward_edge_deterministicHist_SB G)
  \<and> (parserHF.is_forward_edge_deterministic_accessible G
  \<longrightarrow> parserHF.is_forward_edge_deterministicHist_DB G)
  \<and> (parserHF.is_forward_edge_deterministicHist_SB G
  \<longleftrightarrow> parserHF.is_forward_edge_deterministicHist_DB G)"
  apply(rule conjI)
  apply (metis parserHF_inst_AX_is_forward_target_deterministic_correspond_DB parserHF_is_forward_target_deterministicHist_DB_long)
  apply(rule conjI)
  apply (metis parserHF.AX_is_forward_target_deterministic_correspond_SB parserHF.is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long)
  apply(rule conjI)
  apply (metis parserHF.AX_is_forward_target_deterministic_correspond_DB parserHF.is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long)
  apply(rule conjI)
  apply (metis parserHF.is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long parserHF.is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long parserHF_inst_AX_is_forward_target_deterministic_correspond_DB parserHF_inst_AX_is_forward_target_deterministic_correspond_SB)
  apply(rule conjI)
  apply (metis parserHF.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_SB)
  apply(rule conjI)
  apply (metis parserHF.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long parserHF.is_forward_edge_deterministic_accessible_implies_is_forward_edge_deterministicHist_DB_long)
  apply (metis parserHF.AX_is_forward_edge_deterministic_correspond_DB_SB parserHF.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long parserHF.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long)
  done

corollary parserHF_operational_Nonblockingness_SB_DB_Restriction: "
  valid_parser G
  \<Longrightarrow> (parserHF.Nonblockingness_branching G \<longrightarrow> parserHF.Nonblockingness_branching_restricted G)
  \<and> (parserHF.Nonblockingness_branching G \<longrightarrow> parserHF.Nonblockingness_branching_restricted_DB G)
  \<and> (parserHF.Nonblockingness_branching_restricted G \<longleftrightarrow> parserHF.Nonblockingness_branching_restricted_DB G)"
  apply(rule conjI)
  apply(simp add: parserHF.Nonblockingness_branching_restricted_def parserHF.Nonblockingness_branching_def)
  apply(rule conjI)
  apply(simp add: parserHF.Nonblockingness_branching_restricted_DB_def parserHF.Nonblockingness_branching_def)
  apply (metis parserHF.Nonblockingness_branching_SB_DB_restricted)
  done

corollary parserHF_operational_Nonblockingness_from_language_Nonblockingness: "
  valid_parser G
  \<Longrightarrow> parserHF.is_forward_edge_deterministicHist_DB G
  \<or> parserHF.is_forward_edge_deterministicHist_SB G
  \<Longrightarrow> nonblockingness_language (parserHF.unmarked_language G) (parserHF.marked_language G)
  \<Longrightarrow> parserHF.Nonblockingness_branching_restricted_DB G
  \<and> parserHF.Nonblockingness_branching_restricted G"
  apply(subgoal_tac "parserHF.is_forward_deterministicHist_DB G \<or> parserHF.is_forward_deterministicHist_SB G")
  apply(metis parserHF.AX_BF_BraSBRest_DetHDB_LaOp parserHF.AX_BF_BraSBRest_DetHSB_LaOp parserHF.AX_BF_BraDBRest_DetHDB_LaOp parserHF.AX_BF_BraDBRest_DetHSB_LaOp)
  apply(thin_tac "nonblockingness_language (parserHF.unmarked_language G) (parserHF.marked_language G)")
  apply(erule disjE)
  apply(rule disjI1)
  apply(simp add: parserHF.is_forward_deterministicHist_DB_def)
  apply(rule conjI)
  apply (metis parserHF_is_forward_target_deterministicHist_DB_long)
  apply (metis parserHF.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long)
  apply(rule disjI2)
  apply(simp add: parserHF.is_forward_deterministicHist_SB_def)
  apply(rule conjI)
  apply (metis parserHF.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long parserHF_dependency_between_determinism_properties)
  apply (metis parserHF.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long)
  done

corollary parserHF_language_Nonblockingness_from_operational_Nonblockingness: "
  valid_parser G
  \<Longrightarrow> parserHF.Nonblockingness_branching G
  \<Longrightarrow> nonblockingness_language (parserHF.unmarked_language G) (parserHF.marked_language G)"
  apply(metis parserHF.AX_BF_Bra_OpLa)
  done

theorem parserHFS_dependency_between_determinism_properties: "
  valid_parser G
  \<Longrightarrow>
  parserHFS.is_forward_target_deterministic_accessible G
  \<and> (parserHFS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> parserHFS.is_forward_target_deterministicHist_SB G)
  \<and> (parserHFS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> parserHFS.is_forward_target_deterministicHist_DB G)
  \<and> (parserHFS.is_forward_target_deterministicHist_SB G
  \<longleftrightarrow> parserHFS.is_forward_target_deterministicHist_DB G)
  \<and> (parserHFS.is_forward_edge_deterministic_accessible G
  \<longleftrightarrow> parserHFS.is_forward_edge_deterministicHist_SB G)
  \<and> (parserHFS.is_forward_edge_deterministic_accessible G
  \<longleftrightarrow> parserHFS.is_forward_edge_deterministicHist_DB G)
  \<and> (parserHFS.is_forward_edge_deterministicHist_SB G
  \<longleftrightarrow> parserHFS.is_forward_edge_deterministicHist_DB G)"
  apply(rule conjI)
  apply(rule parserHFS_is_forward_target_deterministic_accessible)
  apply(force)
  apply(rule conjI)
  apply (metis parserHFS.is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long parserHFS.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long parserHFS_is_forward_target_deterministic_accessible)
  apply(rule conjI)
  apply (metis parserHFS.is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long parserHFS.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_DB_long parserHFS_is_forward_target_deterministic_accessible)
  apply(rule conjI)
  apply (metis parserHFS.is_forward_target_deterministicHist_DB_vs_is_forward_target_deterministicHist_DB_long parserHFS.is_forward_target_deterministicHist_SB_vs_is_forward_target_deterministicHist_SB_long parserHFS_inst_AX_is_forward_target_deterministic_correspond_DB parserHFS_inst_AX_is_forward_target_deterministic_correspond_SB)
  apply(rule conjI)
  apply (metis parserHFS.AX_is_forward_edge_deterministic_correspond_SB parserHFS.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long)
  apply(rule conjI)
  apply (metis parserHFS.AX_is_forward_edge_deterministic_correspond_DB parserHFS.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long)
  apply (metis parserHFS.AX_is_forward_edge_deterministic_correspond_DB_SB parserHFS.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long parserHFS.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long)
  done

corollary parserHFS_operational_Nonblockingness_SB_DB_Restriction: "
  valid_parser G
  \<Longrightarrow> (parserHFS.Nonblockingness_linear G \<longrightarrow> parserHFS.Nonblockingness_linear_restricted G)
  \<and> (parserHFS.Nonblockingness_linear_DB G \<longrightarrow> parserHFS.Nonblockingness_linear_restricted_DB G)
  \<and> (parserHFS.Nonblockingness_linear G \<longleftrightarrow> parserHFS.Nonblockingness_linear_DB G)
  \<and> (parserHFS.Nonblockingness_linear_restricted G \<longleftrightarrow> parserHFS.Nonblockingness_linear_restricted_DB G)"
  apply(rule conjI)
  apply(simp add: parserHFS.Nonblockingness_linear_restricted_DB_def parserHFS.Nonblockingness_linear_restricted_def parserHFS.Nonblockingness_linear_def parserHFS.Nonblockingness_linear_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rule conjI)
  apply(simp add: parserHFS.Nonblockingness_linear_restricted_DB_def parserHFS.Nonblockingness_linear_restricted_def parserHFS.Nonblockingness_linear_def parserHFS.Nonblockingness_linear_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rule conjI)
  apply (metis parserHFS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  apply(metis parserHFS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_1 parserHFS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_2)
  done

corollary parserHFS_language_Nonblockingness_from_operational_Nonblockingness: "
  valid_parser G
  \<Longrightarrow> parserHFS.Nonblockingness_linear G
      \<or> parserHFS.Nonblockingness_linear_DB G
  \<Longrightarrow> nonblockingness_language (parserHFS.unmarked_language G) (parserHFS.marked_language G)"
  apply(metis parserHFS.AX_BF_LinSB_OpLa parserHFS.AX_BF_LinDB_OpLa)
  done

corollary parserHFS_operational_Nonblockingness_from_language_Nonblockingness: "
  valid_parser G
  \<Longrightarrow> parserHFS.is_forward_edge_deterministic_accessible G
      \<or> parserHFS.is_forward_edge_deterministicHist_DB G
      \<or> parserHFS.is_forward_edge_deterministicHist_SB G
  \<Longrightarrow> nonblockingness_language (parserHFS.unmarked_language G) (parserHFS.marked_language G)
  \<Longrightarrow> parserHFS.Nonblockingness_linear_restricted G
      \<and> parserHFS.Nonblockingness_linear_restricted_DB G"
  apply(subgoal_tac "parserHFS.is_forward_deterministic_accessible G \<or> parserHFS.is_forward_deterministicHist_DB G \<or> parserHFS.is_forward_deterministicHist_SB G")
  apply(thin_tac "parserHFS.is_forward_edge_deterministic_accessible G \<or> parserHFS.is_forward_edge_deterministicHist_DB G \<or> parserHFS.is_forward_edge_deterministicHist_SB G")
  apply(metis parserHFS.AX_BF_LinSBRest_DetR_LaOp parserHFS.AX_BF_LinDBRest_DetR_LaOp parserHFS.AX_BF_LinSBRest_DetHDB_LaOp parserHFS.AX_BF_LinSBRest_DetHSB_LaOp parserHFS.AX_BF_LinDBRest_DetHDB_LaOp parserHFS.AX_BF_LinDBRest_DetHSB_LaOp)
  apply(erule disjE)
  apply(rule disjI1)
  apply (metis parserHFS.is_forward_deterministic_accessible_def parserHFS_is_forward_target_deterministic_accessible)
  apply(erule disjE)
  apply(rule disjI2)
  apply(rule disjI1)
  apply (metis parserHFS.is_forward_deterministicHist_DB_def parserHFS.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long parserHFS.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_DB_long parserHFS_is_forward_target_deterministic_accessible)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(metis parserHFS.is_forward_deterministicHist_SB_def parserHFS.is_forward_edge_deterministicHist_SB_vs_is_forward_edge_deterministicHist_SB_long parserHFS.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long parserHFS_is_forward_target_deterministic_accessible)
  done

theorem parserS_dependency_between_determinism_properties: "
  valid_parser G
  \<Longrightarrow>
  parserS.is_forward_target_deterministic_accessible G"
  apply(rule parserS_dependency_between_determinism_properties_main)
  apply(force)
  done

corollary parserS_operational_Nonblockingness_SB_DB_Restriction: "
  valid_parser G
  \<Longrightarrow> parserS.Nonblockingness_linear_DB G
  \<Longrightarrow> parserS.Nonblockingness_linear_restricted_DB G"
  apply(simp add: parserS.Nonblockingness_linear_restricted_DB_def parserS.Nonblockingness_linear_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  done

corollary parserS_language_Nonblockingness_from_operational_Nonblockingness: "
  valid_parser G
  \<Longrightarrow> parserS.Nonblockingness_linear_DB G
  \<Longrightarrow> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)"
  apply(metis parserS.AX_BF_LinDB_OpLa)
  done

corollary parserS_operational_Nonblockingness_from_language_Nonblockingness: "
  valid_parser G
  \<Longrightarrow> parserS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> nonblockingness_language (parserS.unmarked_language G) (parserS.marked_language G)
  \<Longrightarrow> parserS.Nonblockingness_linear_restricted_DB G"
  apply(subgoal_tac "parserS.is_forward_deterministic_accessible G")
  apply(thin_tac "parserS.is_forward_edge_deterministic_accessible G")
  apply(metis parserS.AX_BF_LinDBRest_DetR_LaOp)
  apply(metis parserS_dependency_between_determinism_properties parserS.is_forward_deterministic_accessible_def)
  done

theorem parserFS_dependency_between_determinism_properties: "
  valid_parser G
  \<Longrightarrow> parserFS.is_forward_target_deterministic_accessible G"
  apply(rule parserFS_dependency_between_determinism_properties_main)
  apply(force)
  done

corollary parserFS_operational_Nonblockingness_SB_DB_Restriction: "
  valid_parser G
  \<Longrightarrow> (parserFS.Nonblockingness_linear G \<longrightarrow> parserFS.Nonblockingness_linear_restricted G)
  \<and> (parserFS.Nonblockingness_linear_DB G \<longrightarrow> parserFS.Nonblockingness_linear_restricted_DB G)
  \<and> (parserFS.Nonblockingness_linear G \<longleftrightarrow> parserFS.Nonblockingness_linear_DB G)
  \<and> (parserFS.Nonblockingness_linear_restricted G \<longleftrightarrow> parserFS.Nonblockingness_linear_restricted_DB G)"
  apply(rule conjI)
  apply(simp add: parserFS.Nonblockingness_linear_restricted_DB_def parserFS.Nonblockingness_linear_restricted_def parserFS.Nonblockingness_linear_def parserFS.Nonblockingness_linear_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rule conjI)
  apply(simp add: parserFS.Nonblockingness_linear_restricted_DB_def parserFS.Nonblockingness_linear_restricted_def parserFS.Nonblockingness_linear_def parserFS.Nonblockingness_linear_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rule conjI)
  apply (metis parserFS.Nonblockingness_linear_vs_Nonblockingness_linear_DB)
  apply(metis parserFS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_1 parserFS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_2)
  done

corollary parserFS_language_Nonblockingness_from_operational_Nonblockingness: "
  valid_parser G
  \<Longrightarrow> parserFS.Nonblockingness_linear G
      \<or> parserFS.Nonblockingness_linear_DB G
  \<Longrightarrow> nonblockingness_language (parserFS.unmarked_language G) (parserFS.marked_language G)"
  apply(erule disjE)
  apply (metis parserFS_operational_Nonblockingness_SB_DB_Restriction parserS.AX_BF_LinDB_OpLa parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
  apply (metis parserS.AX_BF_LinDB_OpLa parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
  done

corollary parserFS_operational_Nonblockingness_from_language_Nonblockingness: "
  valid_parser G
  \<Longrightarrow> parserFS.is_forward_edge_deterministic_accessible G
  \<Longrightarrow> nonblockingness_language (parserFS.unmarked_language G) (parserFS.marked_language G)
  \<Longrightarrow> parserFS.Nonblockingness_linear_restricted G
      \<and> parserFS.Nonblockingness_linear_restricted_DB G"
  apply(subgoal_tac "parserFS.is_forward_deterministic_accessible G")
  apply(thin_tac "parserFS.is_forward_edge_deterministic_accessible G")
  apply(rule conjI)
  apply (metis parserFS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_2 parserFS.is_forward_deterministic_accessible_def parserS_operational_Nonblockingness_from_language_Nonblockingness parserS_vs_parserFS.Nonblockingness_translation_rest1 parserS_vs_parserFS.preservation_of_determinism parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
  apply (metis parserFS.Nonblockingness_linear_restricted_SB_vs_Nonblockingness_linear_restricted_DB_2 parserFS.is_forward_deterministic_accessible_def parserS_operational_Nonblockingness_from_language_Nonblockingness parserS_vs_parserFS.Nonblockingness_translation_rest1 parserS_vs_parserFS.preservation_of_determinism parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
  apply (metis parserFS.is_forward_deterministic_accessible_def parserFS_dependency_between_determinism_properties)
  done

corollary parser_inter_semantics_determinsim_relationship: "
  valid_parser G
  \<Longrightarrow>
  (parserS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> parserHFS.is_forward_target_deterministic_accessible G)
  \<and> (parserS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> parserHF.is_forward_target_deterministic_accessible G)
  \<and> (parserS.is_forward_target_deterministic_accessible G
  \<longleftrightarrow> parserFS.is_forward_target_deterministic_accessible G)
  \<and> (parserS.is_forward_edge_deterministic_accessible G
  \<longleftrightarrow> parserHFS.is_forward_edge_deterministic_accessible G)
  \<and> (parserS.is_forward_edge_deterministic_accessible G
  \<longleftrightarrow> parserFS.is_forward_edge_deterministic_accessible G)
  \<and> (parserHF.is_forward_edge_deterministicHist_SB G
  \<longleftrightarrow> parserHFS.is_forward_edge_deterministicHist_SB G)"
  apply(rule_tac
      t="parserS.is_forward_target_deterministic_accessible G"
      and s="True"
      in ssubst)
  apply (metis parserS_dependency_between_determinism_properties)
  apply(rule_tac
      t="parserFS.is_forward_target_deterministic_accessible G"
      and s="True"
      in ssubst)
  apply (metis parserFS_dependency_between_determinism_properties)
  apply(rule_tac
      t="parserHFS.is_forward_target_deterministic_accessible G"
      and s="True"
      in ssubst)
  apply (metis parserHFS_is_forward_target_deterministic_accessible)
  apply(rule_tac
      t="parserHF.is_forward_target_deterministic_accessible G"
      and s="True"
      in ssubst)
  apply (metis parserHF_dependency_between_determinism_properties)
  apply(rule conjI)
  apply(force)
  apply(rule conjI)
  apply(force)
  apply(rule conjI)
  apply(force)
  apply(rule conjI)
  apply (metis parserS_vs_parserHFS.preservation_of_determinism)
  apply(rule conjI)
  apply (metis parserS_vs_parserFS.preservation_of_determinism)
  apply (metis parserHF.is_forward_edge_deterministicHist_DB_vs_is_forward_edge_deterministicHist_DB_long parserHFS2HF_DEdetermR_FEdetermHist_DB parserHFS_dependency_between_determinism_properties parserHF_dependency_between_determinism_properties parserHF_parserHFS_preserve_determ)
  done

corollary parser_inter_semantics_language_relationship: "
  valid_parser G
  \<Longrightarrow>
  (parserHF.marked_language G \<subseteq> parserHF.unmarked_language G)
  \<and> (parserS.marked_language G = parserFS.marked_language G)
  \<and> (parserS.marked_language G = parserHFS.marked_language G)
  \<and> (parserHFS.marked_language G = parserHF.marked_language G)
  \<and> (parserS.unmarked_language G = parserFS.unmarked_language G)
  \<and> (parserS.unmarked_language G = parserHFS.unmarked_language G)
  \<and> (parserHFS.unmarked_language G = parserHF.unmarked_language G)
  \<and> (valid_bounded_parser G (Suc 0) \<longrightarrow> parserHF.unmarked_language G = prefix_closure (parserHF.unmarked_language G))"
  apply(rule context_conjI)
  apply (metis parserHF.lang_inclusion)
  apply(rule context_conjI)
  apply (metis antisym parserFS.AX_marked_language_finite parserS.AX_marked_language_finite parserS_vs_parserFS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation1 parserS_vs_parserFS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation2 subsetI_basic)
  apply(rule context_conjI)
  apply (metis antisym parserHFS_inst_lang_finite parserS.AX_marked_language_finite parserS_vs_parserHFS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation1 parserS_vs_parserHFS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation2 subsetI)
  apply(rule context_conjI)
  apply (metis antisym parserHF.AX_marked_language_finite parserHFS_inst_lang_finite parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_marked_language_translation2 parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_marked_language_translation1)
  apply(rule context_conjI)
  apply (metis parserFS.AX_unmarked_language_finite parserS.AX_unmarked_language_finite parserS_vs_parserFS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation1 parserS_vs_parserFS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation2 set_eq_from_double_subseteq subsetI)
  apply(rule context_conjI)
  apply (metis parserHFS.AX_unmarked_language_finite parserS.AX_unmarked_language_finite parserS_vs_parserHFS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation1 parserS_vs_parserHFS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation2 set_eq_from_double_subseteq subsetI)
  apply(rule context_conjI)
  apply (metis antisym parserHF.AX_unmarked_language_finite parserHFS.AX_unmarked_language_finite parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_unmarked_language_translation1 parserHF_vs_parserHFS.ATS_Branching_Versus_Linear2_unmarked_language_translation2)
  apply(rule impI)
  apply(subgoal_tac "X" for X)
  prefer 2
  apply(rule PARSERl_unmarked_closed)
  apply(force)
  apply(force)
  apply(simp add: Nonblockingness2_def)
  apply(rule antisym)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(force)
  apply(force)
  done

corollary parser_inter_semantics_Nonblockingnessness_relationship: "
  valid_parser G
  \<Longrightarrow> (parserHFS.Nonblockingness_linear G \<longleftrightarrow> parserHF.Nonblockingness_branching G)
  \<and> (parserFS.Nonblockingness_linear G \<longleftrightarrow> parserS.Nonblockingness_linear_DB G)
  \<and> (parserHFS.Nonblockingness_linear G \<longleftrightarrow> parserFS.Nonblockingness_linear G)
  \<and> (parserHF.Nonblockingness_branching G \<longleftrightarrow> parserS.Nonblockingness_linear_DB G)"
  apply(rule context_conjI)
  apply (metis parserHF_vs_parserHFS.bfbra_to_bflin parserHF_vs_parserHFS.bflin_to_bfbra)
  apply(rule context_conjI)
  apply (metis parserFS_operational_Nonblockingness_SB_DB_Restriction parserS_vs_parserFS_Nonblockingness_and_lang_transfer)
  apply(subgoal_tac "(parserHFS.Nonblockingness_linear G \<longleftrightarrow> parserS.Nonblockingness_linear_DB G)")
  prefer 2
  apply(subgoal_tac "(parserHFS.Nonblockingness_linear_DB G \<longleftrightarrow> parserS.Nonblockingness_linear_DB G) \<and> parserHFS.unmarked_language G = parserS.unmarked_language G \<and> parserHFS.marked_language G = parserS.marked_language G")
  prefer 2
  apply(rule parserS_vs_parserHFS_Nonblockingness_and_lang_transfer)
  apply(force)
  apply(rule_tac
      t="parserHFS.Nonblockingness_linear G"
      and s="parserHFS.Nonblockingness_linear_DB G"
      in ssubst)
  prefer 2
  apply(force)
  apply (metis parserHFS_operational_Nonblockingness_SB_DB_Restriction)
  apply(rule context_conjI)
  apply(rule_tac
      t="parserHFS.Nonblockingness_linear G"
      and s="parserS.Nonblockingness_linear_DB G"
      in ssubst)
  apply(force)
  apply(metis)
  apply(metis)
  done

lemma PARSER1_latest_point_where_input_bottom_not_seen: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> parserS_conf_scheduler c = [parser_bottom P]
  \<Longrightarrow> parser_fixed_input_length_rec1 d n = Suc 0
  \<Longrightarrow> \<forall>r \<in> parser_rules P. rule_rpop r \<noteq> []
  \<Longrightarrow> \<exists>k e c. d k = Some (pair e c) \<and> parserS_conf_scheduler c = [parser_bottom P] \<and> parser_fixed_input_length_rec1 d k = 0 \<and> parser_fixed_input_length_rec1 d (Suc k) = Suc 0"
  apply(subgoal_tac "\<forall>PR. (PR = (\<lambda>e c. parserS_conf_scheduler c = [parser_bottom P] \<and> (case e of None \<Rightarrow> True | Some e \<Rightarrow> length(rule_rpush e)>0))) \<longrightarrow> (\<exists>k\<le>n. (\<forall>i<k. \<not>(\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> PR e c)) i) & ((\<lambda>n. (case d n of None \<Rightarrow> False| Some (pair e c) \<Rightarrow> PR e c)))k)")
  prefer 2
  apply(rule allI)
  apply(rename_tac PR)(*strict*)
  apply(rule impI)
  apply(rule parserS.existence_of_earliest_satisfaction_point_prime)
  apply(rename_tac PR)(*strict*)
  apply(force)
  apply(rename_tac PR)(*strict*)
  apply(force)
  apply(rename_tac PR)(*strict*)
  apply(clarsimp)
  apply(case_tac e)
  apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(case_tac n)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a nat)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="a"
      in ballE)
  apply(rename_tac a nat)(*strict*)
  apply(case_tac "rule_rpop a")
  apply(rename_tac a nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a nat aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a nat)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="(Suc nat)"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  apply(erule_tac
      x="(\<lambda>e c. parserS_conf_scheduler c = [parser_bottom P] \<and> (case e of None \<Rightarrow> True | Some e \<Rightarrow> 0 < length (rule_rpush e)))"
      in allE)
  apply(erule impE)
  apply(force)
  apply(erule exE)
  apply(rename_tac k)(*strict*)
  apply(case_tac k)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
  prefer 2
  apply(rule parserS.some_position_has_details_at_0)
  apply(force)
  apply(clarsimp)
  apply(rename_tac ca)(*strict*)
  apply(rule_tac
      x="0"
      in exI)
  apply(rule_tac
      x="None"
      in exI)
  apply(rule_tac
      x="ca"
      in exI)
  apply(clarsimp)
  apply(case_tac n)
  apply(rename_tac ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> d (Suc 0) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac ca nat)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
  apply(rename_tac ca nat)(*strict*)
  apply(force)
  apply(rename_tac ca nat)(*strict*)
  apply(force)
  apply(rename_tac ca nat)(*strict*)
  apply(force)
  apply(rename_tac ca nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca nat e2 c2)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac ca nat e2 c2)(*strict*)
  apply(case_tac "rule_rpop e2")
  apply(rename_tac ca nat e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca nat e2 c2 a list)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ca nat e2 c2 x)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c2 = w @ [parser_bottom P]")
  apply(rename_tac ca nat e2 c2 x)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc 0"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac ca nat e2 x w)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(force)
  apply(rename_tac ca nat e2 c2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca nat e2 c2 x w)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P e2")
  apply(rename_tac ca nat e2 c2 x w)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(rename_tac ca nat e2 c2 x w)(*strict*)
  apply(rule valid_parser_implies_valid_parser_step_label)
  apply(rename_tac ca nat e2 c2 x w)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac ca nat e2 c2 x w)(*strict*)
  apply(force)
  apply(rename_tac ca nat e2 c2)(*strict*)
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc 0"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac k nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
  apply(rename_tac k nat)(*strict*)
  prefer 2
  apply(rule_tac
      m="n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac k nat)(*strict*)
  apply(force)
  apply(rename_tac k nat)(*strict*)
  apply(force)
  apply(rename_tac k nat)(*strict*)
  apply(force)
  apply(rename_tac k nat)(*strict*)
  apply(erule exE)+
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "e2 \<in> parser_rules P")
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc nat"
      in allE)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P e2")
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(rule valid_parser_implies_valid_parser_step_label)
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "rule_rpop e2 \<noteq> []")
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(case_tac "rule_rpop e2")
  apply(rename_tac k nat e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac k nat e1 e2 c1 c2 a list)(*strict*)
  apply(rule_tac
      x="nat"
      in exI)
  apply(rule_tac
      x="e1"
      in exI)
  apply(rule_tac
      x="c1"
      in exI)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 a list)(*strict*)
  apply(subgoal_tac "parserS_conf_scheduler c1=[parser_bottom P]")
  apply(rename_tac nat e1 e2 c1 c2 a list)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x)(*strict*)
  apply(case_tac e1)
  apply(rename_tac nat e1 e2 c1 c2 x)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e2 c1 c2 x a)(*strict*)
  apply(rule conjI)
  apply(rename_tac nat e2 c1 c2 x a)(*strict*)
  apply(case_tac nat)
  apply(rename_tac nat e2 c1 c2 x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e2 c1 c2 x a nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2 c1 c2 x a nata)(*strict*)
  apply(subgoal_tac "a \<in> parser_rules P")
  apply(rename_tac e2 c1 c2 x a nata)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="Suc nata"
      in allE)
  apply(clarsimp)
  apply(simp add: parser_step_labels_def)
  apply(rename_tac e2 c1 c2 x a nata)(*strict*)
  apply(subgoal_tac "rule_rpop a \<noteq> []")
  apply(rename_tac e2 c1 c2 x a nata)(*strict*)
  prefer 2
  apply(erule_tac
      x="a"
      in ballE)
  apply(rename_tac e2 c1 c2 x a nata)(*strict*)
  apply(force)
  apply(rename_tac e2 c1 c2 x a nata)(*strict*)
  apply(force)
  apply(rename_tac e2 c1 c2 x a nata)(*strict*)
  apply(case_tac "rule_rpop a")
  apply(rename_tac e2 c1 c2 x a nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac e2 c1 c2 x a nata aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e2 c1 c2 x a)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      and P="\<lambda>e2. rule_rpop e2 \<noteq> []"
      in ballE)
  apply(rename_tac nat e2 c1 c2 x a)(*strict*)
  apply(case_tac "rule_rpush e2")
  apply(rename_tac nat e2 c1 c2 x a)(*strict*)
  apply(force)
  apply(rename_tac nat e2 c1 c2 x a aa list)(*strict*)
  apply(force)
  apply(rename_tac nat e2 c1 c2 x a)(*strict*)
  apply(force)
  apply(rename_tac nat e1 e2 c1 c2 a list)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      A="parser_rules P"
      and x="e2"
      and P="\<lambda>e2. rule_rpop e2 \<noteq> []"
      in ballE)
  apply(rename_tac nat e1 e2 c1 c2 a list)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac nat e1 e2 c1 c2 a list)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 a list x xa)(*strict*)
  apply(case_tac "rule_rpush e2")
  apply(rename_tac nat e1 e2 c1 c2 a list x xa)(*strict*)
  apply(force)
  apply(rename_tac nat e1 e2 c1 c2 a list x xa aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 a list x)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_conf_scheduler c1 = w @ [parser_bottom P]")
  apply(rename_tac nat e1 e2 c1 c2 a list x)(*strict*)
  prefer 2
  apply(simp add: parserS.belongs_def)
  apply(erule_tac
      x="nat"
      and P="\<lambda>nat. case d nat of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> (case e of None \<Rightarrow> True | Some e' \<Rightarrow> e' \<in> parser_step_labels P) \<and> c \<in> parserS_configurations P"
      in allE)
  apply(rename_tac nat e1 e2 c1 c2 a list x)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c2 a list x w)(*strict*)
  apply(force)
  apply(rename_tac nat e1 e2 c1 c2 a list x)(*strict*)
  apply(force)
  done

lemma parser_fixed_input_length_rec1_with_derivation_take: "
  i\<le>n
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> parser_fixed_input_length_rec1 (derivation_take d n) i = parser_fixed_input_length_rec1 d i"
  apply(induct i)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: derivation_take_def)
  apply(case_tac "d (Suc i)")
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
  apply(rename_tac i a)(*strict*)
  prefer 2
  apply(rule parserS.pre_some_position_is_some_position_prime)
  apply(rename_tac i a)(*strict*)
  apply(force)
  apply(rename_tac i a)(*strict*)
  apply(force)
  apply(rename_tac i a)(*strict*)
  apply(force)
  apply(rename_tac i a)(*strict*)
  apply(force)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e c)(*strict*)
  apply(case_tac "rule_rpop e")
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_take_def)
  apply(rename_tac i e c a list)(*strict*)
  apply(clarsimp)
  done

lemma parser_fixed_input_length_recN_maximum2: "
  valid_parser G
  \<Longrightarrow> parserS.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> parser_fixed_input_length_recN d n \<le> length (parserS_conf_scheduler c)"
  apply(induct n arbitrary: e c)
  apply(rename_tac e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
  apply(rename_tac n e c)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserS.step_detail_before_some_position)
  apply(rename_tac n e c)(*strict*)
  apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(subgoal_tac "length (rule_rpop e2) \<ge> length (rule_rpush e2)")
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "(parser_fixed_input_length_recN d n) \<le> (length (rule_rpop e2))")
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN d n) (length (rule_rpop e2))"
      and s="length (rule_rpop e2)"
      in ssubst)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(force)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(force)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN d n) (length (rule_rpop e2))"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(force)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(force)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 x xa k w xc)(*strict*)
  apply (metis valid_parser_rules_rhs_gets_shorter)
  apply(rename_tac n c e1 e2 c1 x xa)(*strict*)
  apply(simp add: valid_parser_def)
  done

theorem parser_Nonblockingness_linear_restricted_DB_to_Nonblockingness_linear_DB_with_not_parserS_entire_input_observed: "
  valid_parser G
  \<Longrightarrow> \<forall>c. \<not> parserS_entire_input_observed G c
  \<Longrightarrow> parserS.Nonblockingness_linear_restricted_DB G
  \<Longrightarrow> parserS.Nonblockingness_linear_DB G"
  apply(simp add: parserS.Nonblockingness_linear_DB_def parserS.Nonblockingness_linear_restricted_DB_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
  apply(rename_tac dh n)(*strict*)
  prefer 2
  apply(rule_tac
      M="G"
      in parserS.some_position_has_details_before_max_dom)
  apply(rename_tac dh n)(*strict*)
  apply(rule parserS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e c)(*strict*)
  apply(subgoal_tac "c \<in> parserS_configurations G")
  apply(rename_tac dh n e c)(*strict*)
  prefer 2
  apply(rule parserS.belongs_configurations)
  apply(rename_tac dh n e c)(*strict*)
  apply(rule parserS.derivation_initial_belongs)
  apply(rename_tac dh n e c)(*strict*)
  apply(force)
  apply(rename_tac dh n e c)(*strict*)
  apply(force)
  apply(rename_tac dh n e c)(*strict*)
  apply(force)
  apply(rename_tac dh n e c)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh n \<le> length (parserS_conf_scheduler c)")
  apply(rename_tac dh n e c)(*strict*)
  prefer 2
  apply(rule parser_fixed_input_length_recN_maximum2)
  apply(rename_tac dh n e c)(*strict*)
  apply(force)+
  apply(rename_tac dh n e c)(*strict*)
  apply(rule parserS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac dh n e c)(*strict*)
  apply(force)
  apply(rename_tac dh n e c)(*strict*)
  apply(subgoal_tac "parserS_get_unfixed_scheduler_DB G dh n \<sqsupseteq> [parser_bottom G]")
  apply(rename_tac dh n e c)(*strict*)
  prefer 2
  apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(erule_tac
      x="c"
      in allE)
  apply(simp add: parserS_entire_input_observed_def)
  apply(erule_tac
      x="dh"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      P="parserS.belongs G dh"
      in impE)
  apply(rename_tac dh n e c)(*strict*)
  apply (metis parserS.derivation_initial_belongs)
  apply(rename_tac dh n e c)(*strict*)
  apply(erule_tac
      P="parserS.derivation G dh"
      in impE)
  apply(rename_tac dh n e c)(*strict*)
  apply (metis parserS.derivation_initial_is_derivation)
  apply(rename_tac dh n e c)(*strict*)
  apply(erule_tac
      x="e"
      in allE)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac dh n e l w)(*strict*)
  apply(simp add: parserS_get_scheduler_def)
  apply(rename_tac dh n e c)(*strict*)
  apply(clarsimp)
  done

lemma parser_is_forward_edge_deterministic_accessible_implies_is_forward_deterministic_accessible: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_edge_deterministic_accessible P
  \<Longrightarrow> parserS.is_forward_deterministic_accessible P"
  apply(simp add: parserS.is_forward_deterministic_accessible_def)
  apply(simp add: parserS.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  done

theorem valid_bounded_parser_preserves_only_pop_or_top: "
  valid_bounded_parser G (Suc 0)
  \<Longrightarrow> (\<forall>r\<in> parser_rules G. rule_rpush r = [] \<or> rule_rpush r = rule_rpop r)"
  apply(clarsimp)
  apply(rename_tac r)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G r")
  apply(rename_tac r)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac r k w xa)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="r"
      in ballE)
  apply(rename_tac r k w xa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac r k w xa)(*strict*)
  apply(clarsimp)
  apply(case_tac xa)
  apply(rename_tac r k w xa)(*strict*)
  apply(force)
  apply(rename_tac r k w xa a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac r k w a list)(*strict*)
  apply(case_tac list)
  apply(rename_tac r k w a list)(*strict*)
  prefer 2
  apply(rename_tac r k w a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac r k w a aa lista)(*strict*)
  apply (metis append_Cons append_Nil drop_length_append le_antisym length_append_singleton length_shorter_append2 list.size(3))
  apply(rename_tac r k w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac r k w a)(*strict*)
  apply(case_tac "rule_rpush r")
  apply(rename_tac r k w a)(*strict*)
  apply(force)
  apply(rename_tac r k w a aa list)(*strict*)
  apply(clarsimp)
  apply (metis append_Cons append_Nil drop_length_append le_antisym length_append_singleton length_shorter_append2 list.size(3))
  apply(rename_tac r)(*strict*)
  apply(simp add: valid_bounded_parser_def valid_parser_def)
  done

lemma PARSER_use_FEdeterm: "
  parserS.is_forward_edge_deterministic P
  \<Longrightarrow> r1 \<in> parser_rules P
  \<Longrightarrow> r2 \<in> parser_rules P
  \<Longrightarrow> \<exists>a b. a@rule_lpop r1 = b@rule_lpop r2
  \<Longrightarrow> \<exists>a b. rule_rpop r1 @ a = rule_rpop r2 @ b
  \<Longrightarrow> r1=r2"
  apply(simp add: parserS.is_forward_edge_deterministic_def)
  apply(clarsimp)
  apply(rename_tac a aa b ba)(*strict*)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack=(a@(rule_lpop r1)),parserS_conf_scheduler=rule_rpop r1 @ aa\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack=(a@(rule_lpush r1)),parserS_conf_scheduler=rule_rpush r1 @ aa\<rparr>"
      in allE)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack=(b@(rule_lpush r2)),parserS_conf_scheduler=rule_rpush r2 @ ba\<rparr>"
      in allE)
  apply(erule_tac
      x="r1"
      in allE)
  apply(erule_tac
      x="r2"
      in allE)
  apply(erule impE)
  apply(rename_tac a aa b ba)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(rename_tac a aa b ba)(*strict*)
  apply(force)
  done

lemma PARSER_minimal_step_prefix_closureondition: "
  e \<in> parser_rules P
  \<Longrightarrow> \<exists>x. parserS_conf_stack c1 = x@rule_lpop e
  \<Longrightarrow> \<exists>x. parserS_conf_scheduler c1 = rule_rpop e@x
  \<Longrightarrow> \<exists>c2. parserS_step_relation P c1 e c2"
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(rule_tac
      x="\<lparr>parserS_conf_stack=x @ rule_lpush e, parserS_conf_scheduler=rule_rpush e @ xa\<rparr>"
      in exI)
  apply(force)
  done

lemma parserS_is_forward_target_deterministic: "
  valid_parser P
  \<Longrightarrow> parserS.is_forward_target_deterministic P"
  apply(simp add: parserS.is_forward_target_deterministic_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  done

lemma parser_existence_of_removing_rule: "
  valid_parser G
  \<Longrightarrow> parserS.derivation_initial G d
  \<Longrightarrow> d m \<noteq> None
  \<Longrightarrow> \<not> parserS_get_unfixed_scheduler_DB G d m \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<exists>e \<in> parser_rules G. parser_bottom G \<in> set (rule_rpop e)"
  apply(subgoal_tac "\<exists>k\<le>m. (\<forall>i<k. \<not> SSP i) \<and> SSP k" for SSP)
  prefer 2
  apply(rule_tac
      P="\<lambda>i. \<not> parserS_get_unfixed_scheduler_DB G d i \<sqsupseteq> [parser_bottom G]"
      in ex_least_nat_le_prime)
  apply(force)
  apply(clarsimp)
  apply(rename_tac y k)(*strict*)
  apply(case_tac k)
  apply(rename_tac y k)(*strict*)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(simp add: parserS.derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
  apply(rename_tac y)(*strict*)
  apply(force)
  apply(rename_tac y a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac y a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac y b)(*strict*)
  apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: parserS_initial_configurations_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def parserS_get_scheduler_def parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac y w)(*strict*)
  apply(simp add: suffix_def)
  apply(rename_tac y k nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat)(*strict*)
  apply(erule_tac
      x="nat"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
  apply(rename_tac y nat)(*strict*)
  prefer 2
  apply(rule_tac
      m="m"
      in parserS.step_detail_before_some_position)
  apply(rename_tac y nat)(*strict*)
  apply(rule parserS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac y nat)(*strict*)
  apply(force)
  apply(rename_tac y nat)(*strict*)
  apply(force)
  apply(rename_tac y nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
  apply(rule_tac
      x="e2"
      in bexI)
  apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(simp add: parserS_step_relation_def)
  apply(rename_tac y nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_step_relation_def parserS_get_unfixed_scheduler_DB_def get_configuration_def)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>w. rule_rpop e2=w@(rule_rpush e2)")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  prefer 2
  apply(subgoal_tac "valid_parser_step_label G e2")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  prefer 2
  apply(simp add: valid_parser_def)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 x xa k w xc)(*strict*)
  apply(rule_tac
      x="xc"
      in exI)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_get_scheduler c2 = w@[parser_bottom G]")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  prefer 2
  apply(subgoal_tac "c2 \<in> parserS_configurations G")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(simp add: parserS_configurations_def parserS_get_scheduler_def)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 x xa w wa)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 x xa w wa c)(*strict*)
  apply(case_tac xa)
  apply(rename_tac y nat e1 e2 c1 x xa w wa c)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 x w wa c)(*strict*)
  apply(case_tac "rule_rpush e2")
  apply(rename_tac y nat e1 e2 c1 x w wa c)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 x w wa c a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. rule_rpush e2 = w' @ [x']")
  apply(rename_tac y nat e1 e2 c1 x w wa c a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 x w wa c a list)(*strict*)
  apply(thin_tac "rule_rpush e2=a#list")
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 x xa w wa c a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
  apply(rename_tac y nat e1 e2 c1 x xa w wa c a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 x xa w wa c a list)(*strict*)
  apply(thin_tac "xa=a#list")
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(rule parserS.belongs_configurations)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(rule parserS.derivation_initial_belongs)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_get_scheduler c1 = w@[parser_bottom G]")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  prefer 2
  apply(subgoal_tac "c1 \<in> parserS_configurations G")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(simp add: parserS_configurations_def parserS_get_scheduler_def)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(rule parserS.belongs_configurations)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(rule parserS.derivation_initial_belongs)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(case_tac "(parser_fixed_input_length_recN d nat) \<le> (length (rule_rpop e2))")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) (length (rule_rpop e2)) = length (rule_rpop e2)")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb)(*strict*)
  apply(case_tac "length (rule_rpush e2) - length wa")
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb)(*strict*)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb nata)(*strict*)
  apply(clarsimp)
  apply(case_tac "parser_fixed_input_length_recN d nat - length wb")
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb nata)(*strict*)
  prefer 2
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb nata natb)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb nata)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_get_scheduler_def)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa nata)(*strict*)
  apply(case_tac "xa")
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa nata)(*strict*)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa nata a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa nata a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa nata a list)(*strict*)
  apply(thin_tac "xa=a#list")
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) (length (rule_rpop e2)) = parser_fixed_input_length_recN d nat")
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac y nat e1 e2 c1 c2 x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb)(*strict*)
  apply(thin_tac "max (parser_fixed_input_length_recN d nat) (length w + length (rule_rpush e2)) = parser_fixed_input_length_recN d nat")
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb)(*strict*)
  apply(case_tac "parser_fixed_input_length_recN d nat - length wb")
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb)(*strict*)
  prefer 2
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb nata)(*strict*)
  apply(simp add: suffix_def)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb)(*strict*)
  apply(clarsimp)
  apply(thin_tac "(drop (parser_fixed_input_length_recN d nat) wb @ [parser_bottom G]) \<sqsupseteq> [parser_bottom G]")
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb)(*strict*)
  apply(case_tac "parser_fixed_input_length_recN d nat - (length w + length wa)")
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb)(*strict*)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(rename_tac y nat e1 e2 c1 c2 x xa w wa wb nata)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_get_scheduler_def)
  apply(clarsimp)
  done

lemma PARSER_apply_FEdeterm: "
  valid_parser G
  \<Longrightarrow> e1 \<in> parser_rules G
  \<Longrightarrow> e2 \<in> parser_rules G
  \<Longrightarrow> parserS.is_forward_edge_deterministic G
  \<Longrightarrow> (suffix (rule_lpop e1) (rule_lpop e2)) \<or> (suffix (rule_lpop e2) (rule_lpop e1))
  \<Longrightarrow> (prefix (rule_rpop e1) (rule_rpop e2)) \<or> (prefix (rule_rpop e2) (rule_rpop e1))
  \<Longrightarrow> e1=e2"
  apply(subgoal_tac "\<exists>x. suffix x (rule_lpop e1) \<and> suffix x (rule_lpop e2)")
  apply(subgoal_tac "\<exists>x. prefix (rule_rpop e1) x \<and> prefix (rule_rpop e2) x")
  apply(thin_tac "rule_lpop e1 \<sqsupseteq> rule_lpop e2 \<or> rule_lpop e2 \<sqsupseteq> rule_lpop e1")
  apply(thin_tac "rule_rpop e1 \<sqsubseteq> rule_rpop e2 \<or> rule_rpop e2 \<sqsubseteq> rule_rpop e1")
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: parserS.is_forward_edge_deterministic_def)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack=x,parserS_conf_scheduler=xa\<rparr>"
      in allE)
  apply(simp add: suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack = ca @ rule_lpush e2, parserS_conf_scheduler = rule_rpush e2 @ cc\<rparr>"
      in allE)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(erule_tac
      x="\<lparr>parserS_conf_stack = c @ rule_lpush e1, parserS_conf_scheduler = rule_rpush e1 @ cb\<rparr>"
      in allE)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule impE)
  apply(rename_tac c ca cb cc)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(rule conjI)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(rename_tac c ca cb cc)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(erule_tac
      P="rule_rpop e1 \<sqsubseteq> rule_rpop e2"
      in disjE)
  apply(simp add: prefix_def)
  apply(force)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x c)(*strict*)
  apply(rule_tac
      x="rule_rpop e1"
      in exI)
  apply(force)
  apply(erule_tac
      P="rule_lpop e1 \<sqsupseteq> rule_lpop e2"
      in disjE)
  apply(simp add: suffix_def)
  apply(force)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(rule_tac
      x="rule_lpop e2"
      in exI)
  apply(force)
  done

lemma parserFS_parser_bottom_is_never_read: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> d j = Some (pair e' c')
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> parserFS_conf_fixed c @ parserFS_conf_scheduler c = w @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'
  \<Longrightarrow> parser_bottom G \<notin> set w"
  apply(induct "j-i" arbitrary: i e c w)
  apply(rename_tac i e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c w)(*strict*)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
  apply(rename_tac x i e c w)(*strict*)
  prefer 2
  apply(rule_tac
      m="j"
      in parserFS.step_detail_before_some_position)
  apply(rename_tac x i e c w)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac x i e c w)(*strict*)
  apply(force)
  apply(rename_tac x i e c w)(*strict*)
  apply(force)
  apply(rename_tac x i e c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(erule_tac
      x="Some e2"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2 = w @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'")
  apply(rename_tac x i e c w e2 c2)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      in parserFS_input_with_fixed_decreases)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(erule_tac
      x="wa"
      in meta_allE)
  apply(erule meta_impE)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(erule meta_impE)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c @ parserFS_conf_scheduler c = w @ parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2")
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  prefer 2
  apply(rule_tac
      G="G"
      in parserFS_input_with_fixed_decreases)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(simp add:  valid_bounded_parser_def)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(simp add:  valid_bounded_parser_def)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(force)
  apply(rename_tac x i e c w e2 c2 wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 wa wb)(*strict*)
  apply(subgoal_tac "parserFS_conf_fixed c @ parserFS_conf_scheduler c = wb @ parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2")
  apply(rename_tac x i e c e2 c2 wa wb)(*strict*)
  prefer 2
  apply(force)
  apply(rename_tac x i e c e2 c2 wa wb)(*strict*)
  apply(thin_tac "parserFS_conf_fixed c @ parserFS_conf_scheduler c = wb @ wa @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'")
  apply(thin_tac "parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2 = wa @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'")
  apply(thin_tac "parser_bottom G \<notin> set wa")
  apply(simp add: parserFS_step_relation_def)
  apply(rename_tac x i e c e2 c2 wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 wb xa v)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
  apply(rename_tac x i e c e2 c2 wb xa v)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 wb xa v k w)(*strict*)
  apply(erule disjE)
  apply(rename_tac x i e c e2 c2 wb xa v k w)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 wb xa k w remainder)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
  apply(rename_tac x i e c e2 c2 wb xa k w remainder)(*strict*)
  apply(clarsimp)
  apply (metis in_set_takeD kPrefix_def nset_diff set_append_contra1)
  apply(rename_tac x i e c e2 c2 wb xa k w remainder nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 wb xa k w remainder nat xb)(*strict*)
  apply (metis butlast_snoc_2 insert_Nil not_in_diff set_append_contra1 snoc_eq_iff_butlast)
  apply(rename_tac x i e c e2 c2 wb xa v k w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 wb xa k w popnew)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
  apply(rename_tac x i e c e2 c2 wb xa k w popnew)(*strict*)
  apply(clarsimp)
  apply (metis in_set_takeD kPrefix_def nset_diff set_append_contra1)
  apply(rename_tac x i e c e2 c2 wb xa k w popnew nat)(*strict*)
  apply(clarsimp)
  apply (metis butlast_snoc_2 insert_Nil not_in_diff set_append_contra1 snoc_eq_iff_butlast)
  apply(rename_tac x i e c e2 c2 wb xa v)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma parserFS_fixed_limited: "
  valid_bounded_parser G k
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> length (parserFS_conf_fixed c) \<le> k"
  apply(induct i arbitrary: e c)
  apply(rename_tac e c)(*strict*)
  apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
  apply(rename_tac i e c)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc i"
      in parserFS.step_detail_before_some_position)
  apply(rename_tac i e c)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(force)
  apply(rename_tac i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 x v)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
  apply(rename_tac i c e1 e2 c1 x v)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 x v ka w)(*strict*)
  apply(erule disjE)
  apply(rename_tac i c e1 e2 c1 x v ka w)(*strict*)
  prefer 2
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 x v ka w remainder)(*strict*)
  apply(rule_tac
      j="length (parserFS_conf_fixed c1)"
      in le_trans)
  apply(rename_tac i c e1 e2 c1 x v ka w remainder)(*strict*)
  apply (metis append_Nil butn_empty butn_prefix_closureise le_refl length_append nat_le_linear)
  apply(rename_tac i c e1 e2 c1 x v ka w remainder)(*strict*)
  apply(force)
  apply(rename_tac i c e1 e2 c1 x v ka w)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c e1 e2 c1 x v ka w popnew)(*strict*)
  apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      and A="parser_rules G"
      and P="\<lambda>e. length (rule_rpop e) \<le> k"
      in ballE)
  apply(rename_tac i c e1 e2 c1 x v ka w popnew)(*strict*)
  apply(clarsimp)
  apply (metis append_Nil kPrefix_def le_trans length_shorter_append2 nat_le_linear)
  apply(rename_tac i c e1 e2 c1 x v ka w popnew)(*strict*)
  apply(force)
  apply(rename_tac i c e1 e2 c1 x v)(*strict*)
  apply(simp add: valid_bounded_parser_def valid_parser_def)
  done

lemma parserFS_unmarked_effect_prefix_closed: "
  valid_bounded_parser P (Suc 0)
  \<Longrightarrow> parserFS.derivation_initial P d
  \<Longrightarrow> prefix_closure (parserFS_unmarked_effect P d) = parserFS_unmarked_effect P d"
  apply(rule order_antisym)
  prefer 2
  apply(simp add: prefix_closure_def prefix_def)
  apply(force)
  apply(simp add: prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x c)(*strict*)
  apply(simp add: parserFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(subgoal_tac "c' \<in> parserFS_configurations P")
  apply(rename_tac x c ca c' i v e)(*strict*)
  prefer 2
  apply(rule parserFS.belongs_configurations)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(subgoal_tac "ca \<in> parserFS_initial_configurations P")
  apply(rename_tac x c ca c' i v e)(*strict*)
  prefer 2
  apply(simp add: parserFS.derivation_initial_def)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(subgoal_tac "\<exists>k\<le>SSn. (\<forall>i<k. \<not> SSP i) \<and> SSP k" for SSn SSP)
  apply(rename_tac x c ca c' i v e)(*strict*)
  prefer 2
  apply(rule_tac
      n="i"
      and P="\<lambda>i. length x + length(parserFS_conf_scheduler(the(get_configuration(d i)))) \<le> length (parserFS_conf_scheduler ca)"
      in ex_least_nat_le_prime)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac "parserFS_conf_scheduler c'")
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>x. parserFS_conf_scheduler ca=x@[parser_bottom P]")
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e xa)(*strict*)
  apply(subgoal_tac "butlast_if_match (xa @ [parser_bottom P]) (parser_bottom P) = xa")
  apply(rename_tac x c ca c' i v e xa)(*strict*)
  prefer 2
  apply (metis butlast_if_match_direct insert_Nil rotate_simps)
  apply(rename_tac x c ca c' i v e xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(simp add: parserFS_initial_configurations_def parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x c i v e f l)(*strict*)
  apply(simp add: dom_abbreviation)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e a list)(*strict*)
  apply(subgoal_tac "\<exists>x. parserFS_conf_scheduler c'=x@[parser_bottom P]")
  apply(rename_tac x c ca c' i v e a list)(*strict*)
  apply(thin_tac "parserFS_conf_scheduler c' = a # list")
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e xa)(*strict*)
  apply(subgoal_tac "butlast_if_match (v @ parserFS_conf_fixed c') (parser_bottom P) = v @ parserFS_conf_fixed c'")
  apply(rename_tac x c ca c' i v e xa)(*strict*)
  apply(clarsimp)
  apply(thin_tac "butlast_if_match (v @ parserFS_conf_fixed c') (parser_bottom P) = v @ parserFS_conf_fixed c'")
  apply(case_tac ca)
  apply(rename_tac x c ca c' i v e xa parserFS_conf_fixeda parserFS_conf_stack parserFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c c' i v e xa parserFS_conf_fixeda parserFS_conf_stack)(*strict*)
  apply(case_tac c')
  apply(rename_tac x c c' i v e xa parserFS_conf_fixeda parserFS_conf_stack parserFS_conf_fixedaa parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c i v e xa parserFS_conf_fixed parserFS_conf_stack parserFS_conf_fixeda parserFS_conf_stacka)(*strict*)
  apply (metis lengthSmallerUnderDecomp length_append length_splice)
  apply(rename_tac x c ca c' i v e xa)(*strict*)
  apply(subgoal_tac "parser_bottom P \<notin> set(v @ parserFS_conf_fixed c')")
  apply(rename_tac x c ca c' i v e xa)(*strict*)
  apply (metis butlast_if_match_direct2_prime)
  apply(rename_tac x c ca c' i v e xa)(*strict*)
  apply(simp add: parserFS_initial_configurations_def parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x c i v e xa f l)(*strict*)
  apply(simp add: dom_abbreviation)
  apply(rename_tac x c ca c' i v e a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. parserFS_conf_scheduler c' = w' @ [x']")
  apply(rename_tac x c ca c' i v e a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac x c ca c' i v e a list)(*strict*)
  apply(thin_tac "parserFS_conf_scheduler c'=a#list")
  apply(simp add: parserFS_initial_configurations_def parserFS_configurations_def)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c i v e f w' l x')(*strict*)
  apply(simp add: dom_abbreviation)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k)(*strict*)
  apply(case_tac k)
  apply(rename_tac x c ca c' i v e k)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac ca c' i v e)(*strict*)
  apply(rule_tac
      x="ca"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac ca c' i v e)(*strict*)
  apply(force)
  apply(rename_tac ca c' i v e)(*strict*)
  apply(simp add: parserFS_initial_configurations_def)
  apply(clarsimp)
  apply(simp add: butlast_if_match_def)
  apply(rename_tac x c ca c' i v e k nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e nat)(*strict*)
  apply(rename_tac k)
  apply(rename_tac x c ca c' i v e k)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d k = Some (pair e1 c1) \<and> d (Suc k) = Some (pair (Some e2) c2) \<and> parserFS_step_relation P c1 e2 c2")
  apply(rename_tac x c ca c' i v e k)(*strict*)
  prefer 2
  apply(rule_tac
      m="i"
      in parserFS.step_detail_before_some_position)
  apply(rename_tac x c ca c' i v e k)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac x c ca c' i v e k)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(erule_tac
      x="k"
      in allE)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      x="c2"
      in exI)
  apply(rule conjI)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "length x + length (parserFS_conf_scheduler c2) = length (parserFS_conf_scheduler ca)")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c1 @ parserFS_conf_scheduler c1 = w @ parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(rule_tac
      G="P"
      in parserFS_input_with_fixed_decreases)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va)(*strict*)
  apply(case_tac "rule_rpop e2")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa)(*strict*)
  apply(erule disjE)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list)(*strict*)
  apply(subgoal_tac "\<exists>x. rule_rpop e2=[x]")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list)(*strict*)
  apply(erule disjE)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa a list xb popnew)(*strict*)
  apply(case_tac "popnew")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa a list xb popnew)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa a list xb popnew aa lista)(*strict*)
  apply(subgoal_tac "lista=[]")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa a list xb popnew aa lista)(*strict*)
  prefer 2
  apply (metis Cons_eq_appendI append_Nil length_1_context_empty)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa a list xb popnew aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e2"
      in ballE)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list)(*strict*)
  apply(rule_tac
      x="a"
      in exI)
  apply(clarsimp)
  apply(case_tac list)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list aa lista)(*strict*)
  apply (metis add_Suc_right length_append length_shorter_1 list.inject list.size(4) add.commute plus_nat.add_0)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w xa va a list)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed ca @ parserFS_conf_scheduler ca = w @ parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  prefer 2
  apply(rule_tac
      G="P"
      in parserFS_input_with_fixed_decreases)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(simp add:  valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(subgoal_tac "parserFS_conf_fixed ca=[]")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  prefer 2
  apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parser_bottom P \<notin> set (w @ parserFS_conf_fixed c2)")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="butlast_if_match (w @ parserFS_conf_fixed c2) (parser_bottom P)"
      and s="w @ parserFS_conf_fixed c2"
      in ssubst)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply (metis append_Nil2 butlast_if_match_direct2_prime butlast_if_match_pull_out)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(rule_tac
      z="parserFS_conf_scheduler ca"
      in prefix_length_eq)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  prefer 2
  apply(simp add: prefix_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(simp add: prefix_def)
  apply(case_tac "v @ parserFS_conf_fixed c'")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w)(*strict*)
  apply(simp add: butlast_if_match_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. v @ parserFS_conf_fixed c' = w' @ [x']")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w a list)(*strict*)
  apply(thin_tac "v @ parserFS_conf_fixed c'=a#list")
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w w' x')(*strict*)
  apply(case_tac "x'=parser_bottom P")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w w' x')(*strict*)
  apply(subgoal_tac "butlast_if_match (w' @ [x']) (parser_bottom P)=w'")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(rule_tac
      x="c @ [parser_bottom P] @ parserFS_conf_scheduler c'"
      in exI)
  apply (metis ConsApp concat_asso)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w w' x')(*strict*)
  apply (metis butlast_if_match_direct insert_Nil)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w w' x')(*strict*)
  apply(subgoal_tac "butlast_if_match (w' @ [x']) (parser_bottom P) = w'@[x']")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w w' x')(*strict*)
  prefer 2
  apply (metis butlast_if_match_direct2 insert_Nil)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w w' x')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="c@ parserFS_conf_scheduler c'"
      in exI)
  apply (metis append_eq_appendI)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(rule_tac
      d="d"
      and i="0"
      and j="Suc k"
      in parserFS_parser_bottom_is_never_read)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(subgoal_tac "c2 \<in> parserFS_configurations P")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  prefer 2
  apply(rule parserFS.belongs_configurations)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(case_tac "parser_bottom P \<notin> set (parserFS_conf_fixed c2)")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(subgoal_tac "parserFS_conf_scheduler c2=[]")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  prefer 2
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x c ca i v e k e1 e2 c1 w f fa l la r ra)(*strict*)
  apply(simp add: dom_abbreviation)
  apply(clarsimp)
  apply(rename_tac x c ca i v e k e1 e2 c1 w f fa l la r ra vd vf vg cb vh cc vi "cd" vj ce)(*strict*)
  apply(case_tac ra)
  apply(rename_tac x c ca i v e k e1 e2 c1 w f fa l la r ra vd vf vg cb vh cc vi "cd" vj ce)(*strict*)
  apply(force)
  apply(rename_tac x c ca i v e k e1 e2 c1 w f fa l la r ra vd vf vg cb vh cc vi "cd" vj ce a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ra = w' @ [x']")
  apply(rename_tac x c ca i v e k e1 e2 c1 w f fa l la r ra vd vf vg cb vh cc vi "cd" vj ce a list)(*strict*)
  prefer 2
  apply(rule NonEmptyListHasTailElem)
  apply(force)
  apply(rename_tac x c ca i v e k e1 e2 c1 w f fa l la r ra vd vf vg cb vh cc vi "cd" vj ce a list)(*strict*)
  apply(thin_tac "ra=a#list")
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c2 = w @ [parser_bottom P]")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  prefer 2
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x c ca i v e k e1 e2 c1 w f fa l la r)(*strict*)
  apply(simp add: dom_abbreviation)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w wa)(*strict*)
  apply(subgoal_tac "wa=[]")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w wa)(*strict*)
  prefer 2
  apply(subgoal_tac "length (parserFS_conf_fixed c2) \<le> Suc 0")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w wa)(*strict*)
  prefer 2
  apply(rule parserFS_fixed_limited)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w wa)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w wa)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w wa)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w wa)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2 = w @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'")
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  prefer 2
  apply(rule_tac
      G="P"
      in parserFS_input_with_fixed_decreases)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(simp add:  valid_bounded_parser_def)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i v e k e1 e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler c2 = w @ parserFS_conf_scheduler c'")
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  prefer 2
  apply(rule_tac
      G="P"
      in parserFS_input_decreases)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(simp add: valid_bounded_parser_def)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(rule parserFS.derivation_initial_belongs)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(simp add:  valid_bounded_parser_def)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(force)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "wa=[]")
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  prefer 2
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x c ca i e k e1 e2 c1 w wa f l la)(*strict*)
  apply(simp add: dom_abbreviation)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w)(*strict*)
  apply(subgoal_tac "butlast_if_match (w @ parserFS_conf_fixed c') (parser_bottom P) = w")
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w)(*strict*)
  prefer 2
  apply (metis append_Nil2 butlast_if_match_direct insert_Nil parserFS_get_scheduler_def)
  apply(rename_tac x c ca c' i e k e1 e2 c1 c2 w)(*strict*)
  apply(clarsimp)
  done

lemma valid_parser_lhs_never_empty: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> parserFS_conf_stack c \<noteq> []"
  apply(induct n arbitrary: e c)
  apply(rename_tac e c)(*strict*)
  apply(clarsimp)
  apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
  apply(rename_tac n e c)(*strict*)
  prefer 2
  apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
  apply(rename_tac n e c)(*strict*)
  apply(rule parserFS.derivation_initial_is_derivation)
  apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 v)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
  apply(rename_tac n c e1 e2 c1 v)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(rename_tac n c e1 e2 c1 v)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma PARSER_is_forward_deterministic_accessible_implies_is_forward_edge_deterministic_accessible: "
  parserFS.is_forward_deterministic_accessible P
  \<Longrightarrow> parserFS.is_forward_edge_deterministic_accessible P"
  apply(simp add: parserFS.is_forward_deterministic_accessible_def)
  done

end
