section {*I\_cfgLM\_trans\_der*}
theory
  I_cfgLM_trans_der

imports
  I_cfgLM

begin

abbreviation cfgLMTD :: "('a,'b) cfg \<Rightarrow> (nat \<Rightarrow> (('a, 'b) cfg_step_label, ('a, 'b) cfg_configuration) derivation_configuration option) \<Rightarrow> ('a, 'b) cfg_configuration \<Rightarrow> ('a, 'b) cfg_step_label list \<Rightarrow> ('a, 'b) cfg_configuration \<Rightarrow> bool" where
  "cfgLMTD G d c \<pi> c' \<equiv> (cfgLM.trans_der G d c \<pi> c')"

lemma cfgLM_trans_der_context2: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=w1'\<rparr>
  \<Longrightarrow> \<lparr>cfg_conf=w2\<rparr>\<in> cfg_configurations G
  \<Longrightarrow> cfgLM.trans_der G (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@w2\<rparr>)) \<lparr>cfg_conf=w1@w2\<rparr> (\<pi>1) \<lparr>cfg_conf=w1'@w2\<rparr>"
  apply(simp add: cfgLM.trans_der_def)
  apply(rule context_conjI)
   apply(rule cfgLM.derivation_map_preserves_derivation2)
    apply(force)
   apply(clarsimp)
   apply(rename_tac a e b ea)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac a e b ea l r)(*strict*)
   apply(rule_tac
      x="l"
      in exI)
   apply(clarsimp)
  apply(rule conjI)
   apply(rule cfgLM.derivation_map_preserves_belongs)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(clarsimp)
   apply(rename_tac ca e)(*strict*)
   apply(simp add: setAConcat setBConcat)
  apply(rule conjI)
   apply(simp add: get_labels_derivation_map)
  apply(simp add: derivation_map_def)
  apply(clarsimp)
  done

lemma cfgLM_trans_der_context_prime2: "
  valid_cfg G
  \<Longrightarrow> \<lparr>cfg_conf=w2\<rparr>\<in> cfg_configurations G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=w1'\<rparr>
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=w1@w2\<rparr> (\<pi>1) \<lparr>cfg_conf=w1'@w2\<rparr>"
  apply(rule_tac
      x=" (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@w2\<rparr>)) "
      in exI)
  apply(rule cfgLM_trans_der_context2)
    apply(force)+
  done

lemma cfgLM_trans_der_crop: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=w\<rparr> \<pi> c'
  \<Longrightarrow> n<length \<pi>
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> cfgLM.trans_der G (derivation_take d n) \<lparr>cfg_conf=w\<rparr> (take n \<pi>) c"
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac ea)(*strict*)
   apply(rule cfgLM.derivation_take_preserves_derivation)
   apply(force)
  apply(rename_tac ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac ea)(*strict*)
   apply(rule cfgLM.derivation_take_preserves_belongs)
   apply(force)
  apply(rename_tac ea)(*strict*)
  apply(rule_tac
      t="min (length \<pi>) n"
      and s="n"
      in ssubst)
   apply(rename_tac ea)(*strict*)
   apply(force)
  apply(rename_tac ea)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_take d n) n"
      and s="get_labels d n"
      in ssubst)
   apply(rename_tac ea)(*strict*)
   apply (metis cfgLM.derivation_take_id_prime cfgLM.get_labels_derivation_take)
  apply(rename_tac ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac ea)(*strict*)
   prefer 2
   apply(simp add: derivation_take_def)
  apply(rename_tac ea)(*strict*)
  apply(rule listEqI)
   apply(rename_tac ea)(*strict*)
   apply(simp add: get_labels_def)
   apply(rule_tac
      t="min (length \<pi>) n"
      and s="n"
      in ssubst)
    apply(rename_tac ea)(*strict*)
    apply(force)
   apply(rename_tac ea)(*strict*)
   apply (metis list.size(3) nat_seqEmpty nat_seq_length_Suc0 neq0_conv zero_less_Suc)
  apply(rename_tac ea i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (get_labels d n)=n")
   apply(rename_tac ea i)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac ea i)(*strict*)
  apply(rule_tac
      t="get_labels d n ! i"
      and s="get_labels d (length \<pi>) ! i"
      in ssubst)
   apply(rename_tac ea i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac ea i)(*strict*)
  apply(thin_tac "get_labels d (length \<pi>) = map Some \<pi>")
  apply(simp add: get_labels_def)
  apply(subgoal_tac "nat_seq (Suc 0) n ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac ea i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac ea i)(*strict*)
    apply(force)
   apply(rename_tac ea i)(*strict*)
   apply(force)
  apply(rename_tac ea i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length (get_labels d (length \<pi>))=(length \<pi>)")
   apply(rename_tac ea i)(*strict*)
   prefer 2
   apply (metis get_labels_length)
  apply(rename_tac ea i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (length \<pi>) ! i = (SSn)+(SSi)" for SSn SSi)
   apply(rename_tac ea i)(*strict*)
   prefer 2
   apply(rule nat_seq_nth_compute)
    apply(rename_tac ea i)(*strict*)
    apply(force)
   apply(rename_tac ea i)(*strict*)
   apply(force)
  apply(rename_tac ea i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="map (\<lambda>i. get_label (d i)) (nat_seq (Suc 0) (length \<pi>)) ! i"
      and s=" (\<lambda>i. get_label (d i)) ((nat_seq (Suc 0) (length \<pi>)) ! i) "
      in ssubst)
   apply(rename_tac ea i)(*strict*)
   apply(rule nth_map)
   apply(simp add: get_labels_def)
  apply(rename_tac ea i)(*strict*)
  apply(force)
  done

lemma cfgLM_trans_der_crop_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=w\<rparr> \<pi> c'
  \<Longrightarrow> n<length \<pi>
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=w\<rparr> (take n \<pi>) c"
  apply(rule_tac
      x="(derivation_take d n)"
      in exI)
  apply(rule cfgLM_trans_der_crop)
     apply(blast)+
  done

lemma not_earlier_terminal: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 c (\<pi>1@\<pi>2) \<lparr>cfg_conf=teA A#w1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 c \<pi>1 \<lparr>cfg_conf=teB b#w2\<rparr>
  \<Longrightarrow> Q"
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1(length \<pi>1) = Some (pair e c)")
   apply(rename_tac e ea)(*strict*)
   prefer 2
   apply(rule_tac
      m="length(\<pi>1@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ea eb ca)(*strict*)
  apply(subgoal_tac "d1 (length \<pi>1) = d2(length \<pi>1)")
   apply(rename_tac e ea eb ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac e eb)(*strict*)
   apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
    apply(rename_tac e eb)(*strict*)
    prefer 2
    apply(rule_tac
      d="d1"
      and i="length \<pi>1"
      and j="length \<pi>2"
      in cfgLM.derivation_monotonically_inc)
         apply(rename_tac e eb)(*strict*)
         apply(force)
        apply(rename_tac e eb)(*strict*)
        apply(force)
       apply(rename_tac e eb)(*strict*)
       apply(force)
      apply(rename_tac e eb)(*strict*)
      apply(force)
     apply(rename_tac e eb)(*strict*)
     apply(force)
    apply(rename_tac e eb)(*strict*)
    apply(force)
   apply(rename_tac e eb)(*strict*)
   apply(simp add: cfg_get_history_def)
   apply(clarsimp)
   apply(rename_tac e eb w)(*strict*)
   apply(simp add: maxTermPrefix_vs_maximalPrefixB)
  apply(rename_tac e ea eb ca)(*strict*)
  apply(rule_tac
      ?n2.0="((length \<pi>1))"
      in cfgLM_equal_positions_when_same_productions)
         apply(rename_tac e ea eb ca)(*strict*)
         apply(force)+
   apply(rename_tac e ea eb ca)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="get_labels d1 (length \<pi>1)"
      and s="map Some \<pi>1"
      in ssubst)
    apply(rename_tac e ea eb ca)(*strict*)
    prefer 2
    apply(rule listEqI)
     apply(rename_tac e ea eb ca)(*strict*)
     apply(force)
    apply(rename_tac e ea eb ca i)(*strict*)
    apply(force)
   apply(rename_tac e ea eb ca)(*strict*)
   apply(rule get_labels_drop_tail)
    apply(rename_tac e ea eb ca)(*strict*)
    apply(force)
   apply(rename_tac e ea eb ca)(*strict*)
   apply(force)
  apply(rename_tac e ea eb ca)(*strict*)
  apply(force)
  done

lemma equal_labels_from_same_configuration_up_to_context_implies_same_modification: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1@w2\<rparr> \<pi> \<lparr>cfg_conf=v1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=w1\<rparr> \<pi> \<lparr>cfg_conf=v2\<rparr>
  \<Longrightarrow> v2@w2=v1"
  apply(induct \<pi> arbitrary: d1 d2 v1 v2 rule: rev_induct)
   apply(rename_tac d1 d2 v1 v2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac x xs d1 d2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs d1 d2 v1 v2)(*strict*)
   prefer 2
   apply(simp only: cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs d1 d2 v1 v2 e ea)(*strict*)
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs d1 d2 v1 v2 e ea)(*strict*)
     apply(force)
    apply(rename_tac x xs d1 d2 v1 v2 e ea)(*strict*)
    apply(force)
   apply(rename_tac x xs d1 d2 v1 v2 e ea)(*strict*)
   apply(force)
  apply(rename_tac x xs d1 d2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp only: cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e ea)(*strict*)
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e ea)(*strict*)
     apply(force)
    apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e ea)(*strict*)
    apply(clarify)
    apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e ea l r)(*strict*)
    apply(rule_tac
      x="(pair ea \<lparr>cfg_conf = v2\<rparr>)"
      in exI)
    apply(rule_tac
      t="Suc (length xs)"
      and s="(length (xs @ [x]))"
      in ssubst)
     apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e ea l r)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e ea l r)(*strict*)
    apply(force)
   apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e ea)(*strict*)
   apply(force)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2)(*strict*)
  apply(erule exE)+
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
  apply(clarify)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e1a e2a c1a c2a l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e1a e2a c1a c2a l r cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e1a e2a c1a c2a l r cfg_confa cfg_confaa)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e1a e2a c1a c2a l r cfg_confa cfg_confaa cfg_confb)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 c1 c2 e1a e2a c1a c2a l r cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
  apply(clarify)
  apply(clarsimp)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 e1a e2a l r cfg_confb cfg_confc)(*strict*)
  apply(rename_tac y1 y2)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 e1a e2a l r y1 y2)(*strict*)
  apply(subgoal_tac "x=e2")
   apply(rename_tac x xs d1 d2 v1 v2 e1 e2 e1a e2a l r y1 y2)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(subgoal_tac "Some x=Some e2")
    apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
    apply(force)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(rule_tac
      t="Some x"
      and s="(map Some xs @ [Some x])!(length xs)"
      in ssubst)
    apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
    apply (metis length_map nth_append_length)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(rule_tac
      t="map Some xs @ [Some x]"
      and s="get_labels d1 (Suc (length xs))"
      in ssubst)
    apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
    apply(force)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(rule getLabel_at_pos)
     apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
     apply(force)
    apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
    apply(force)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(force)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 e1a e2a l r y1 y2)(*strict*)
  apply(subgoal_tac "x=e2a")
   apply(rename_tac x xs d1 d2 v1 v2 e1 e2 e1a e2a l r y1 y2)(*strict*)
   prefer 2
   apply(thin_tac "x=e2")
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(subgoal_tac "Some x=Some e2a")
    apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
    apply(force)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(rule_tac
      t="Some x"
      and s="(map Some xs @ [Some x])!(length xs)"
      in ssubst)
    apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
    apply (metis length_map nth_append_length)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(rule_tac
      t="map Some xs @ [Some x]"
      and s="get_labels d2 (Suc (length xs))"
      in ssubst)
    apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
    apply(force)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(rule_tac
      d="d2"
      and c="\<lparr>cfg_conf = v2\<rparr>"
      in getLabel_at_pos)
     apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
     apply(force)
    apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
    apply(force)
   apply(rename_tac x xs d1 d2 v2 e1 e2 e1a e2a l r y1)(*strict*)
   apply(force)
  apply(rename_tac x xs d1 d2 v1 v2 e1 e2 e1a e2a l r y1 y2)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r y1 y2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
  apply(erule_tac
      x="derivation_take d1 (length xs)"
      in meta_allE)
  apply(erule_tac
      x="derivation_take d2 (length xs)"
      in meta_allE)
  apply(erule_tac
      x="l @ teA (prod_lhs e2) # r"
      in meta_allE)
  apply(erule_tac
      x="la @ teA (prod_lhs e2) # ra"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
   apply(rule_tac
      P="\<lambda>X. cfgLM.trans_der G (derivation_take d1 (length xs)) \<lparr>cfg_conf = w1 @ w2\<rparr> X \<lparr>cfg_conf = l @ teA (prod_lhs e2) # r\<rparr>"
      and t="xs"
      and s="take(length xs)(xs@[e2])"
      in ssubst)
    apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
    apply(force)
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
   apply(rule cfgLM_trans_der_crop)
      apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
      apply(force)
     apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
     apply(force)
    apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
    apply(force)
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
   apply(force)
  apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
   apply(rule_tac
      P="\<lambda>X. cfgLM.trans_der G (derivation_take d2 (length xs)) \<lparr>cfg_conf = w1\<rparr> X \<lparr>cfg_conf = la @ teA (prod_lhs e2) # ra\<rparr>"
      and t="xs"
      and s="take(length xs)(xs@[e2])"
      in ssubst)
    apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
    apply(force)
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
   apply(rule cfgLM_trans_der_crop)
      apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
      apply(force)
     apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
     apply(force)
    apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
    apply(force)
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
   apply(force)
  apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a r ra l' l'a)(*strict*)
  apply(subgoal_tac "l'=l'a")
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a r ra l' l'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a ra l'a)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac xs d1 d2 v1 v2 e1 e2 e1a r ra l' l'a)(*strict*)
  apply (metis identical_temrinal_maximal_prefix)
  done

lemma cfgLM_trans_der_preserves_terminals: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=w1@(liftB v)@w2\<rparr> \<pi> c'
  \<Longrightarrow> \<exists>w1 w2. cfg_conf c'=w1@(liftB v)@w2"
  apply(induct \<pi> arbitrary: c' rule: rev_induct)
   apply(rename_tac c')(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac x xs c')(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac x xs c' e)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs c' e)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs c' e)(*strict*)
     apply(force)
    apply(rename_tac x xs c' e)(*strict*)
    apply(force)
   apply(rename_tac x xs c' e)(*strict*)
   apply(force)
  apply(rename_tac x xs c' e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 c1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xs c' e1 e2 c1 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs c' e1 e2 c1 l r cfg_confa)(*strict*)
  apply(case_tac c')
  apply(rename_tac x xs c' e1 e2 c1 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 e2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac x xs e1 e2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac x xs e1 e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 e2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(case_tac e2)
  apply(rename_tac x xs e1 e2 r l' prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 r l' prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac x xs e1 r l' A w)(*strict*)
  apply(erule_tac
      x="\<lparr>cfg_conf = liftB l' @ teA A # r\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x xs e1 r l' A w)(*strict*)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs e1 r l' A w)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac x xs e1 r l' A w)(*strict*)
   apply(force)
  apply(rename_tac x xs e1 r l' A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 r l' A w w1a w2a)(*strict*)
  apply(subgoal_tac "prefix (liftB l') w1a \<or> prefix w1a (liftB l') ")
   apply(rename_tac x xs e1 r l' A w w1a w2a)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac x xs e1 r l' A w w1a w2a)(*strict*)
  apply(erule disjE)
   apply(rename_tac x xs e1 r l' A w w1a w2a)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xs e1 r l' A w w2a c)(*strict*)
   apply(case_tac c)
    apply(rename_tac x xs e1 r l' A w w2a c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs e1 r l' A w w2a)(*strict*)
    apply(case_tac v)
     apply(rename_tac x xs e1 r l' A w w2a)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs e1 r l' A w)(*strict*)
     apply(force)
    apply(rename_tac x xs e1 r l' A w w2a a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac x xs e1 r l' A w w2a c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs e1 l' A w w2a list)(*strict*)
   apply(rule_tac
      x="liftB l' @ w @ list"
      in exI)
   apply(force)
  apply(rename_tac x xs e1 r l' A w w1a w2a)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x xs e1 r l' A w w1a w2a c)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = w1a")
   apply(rename_tac x xs e1 r l' A w w1a w2a c)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB w1a"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_liftB setA_setmp_concat_1 all_not_in_conv emptyE empty_subsetI)
  apply(rename_tac x xs e1 r l' A w w1a w2a c)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = c")
   apply(rename_tac x xs e1 r l' A w w1a w2a c)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB c"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis List.set_simps(1) setA_liftB_substring liftB_commutes_over_concat concat_asso)
  apply(rename_tac x xs e1 r l' A w w1a w2a c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 r l' A w w2a l'a l'b)(*strict*)
  apply(subgoal_tac "l'=l'a@l'b")
   apply(rename_tac x xs e1 r l' A w w2a l'a l'b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs e1 r A w w2a l'a l'b)(*strict*)
   apply(thin_tac "liftB l'a @ liftB l'b = liftB (l'a @ l'b)")
   apply(simp add: liftB_commutes_over_concat)
   apply(subgoal_tac "prefix (liftB l'b) (liftB v) \<or> prefix (liftB v) (liftB l'b) ")
    apply(rename_tac x xs e1 r A w w2a l'a l'b)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac x xs e1 r A w w2a l'a l'b)(*strict*)
   apply(erule disjE)
    apply(rename_tac x xs e1 r A w w2a l'a l'b)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x xs e1 r A w w2a l'a l'b c)(*strict*)
    apply(case_tac c)
     apply(rename_tac x xs e1 r A w w2a l'a l'b c)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs e1 r A w l'a l'b)(*strict*)
     apply(subgoal_tac "l'b=v")
      apply(rename_tac x xs e1 r A w l'a l'b)(*strict*)
      prefer 2
      apply(rule liftB_inj)
      apply(force)
     apply(rename_tac x xs e1 r A w l'a l'b)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs e1 r A w l'a)(*strict*)
     apply(force)
    apply(rename_tac x xs e1 r A w w2a l'a l'b c a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs e1 r A w w2a l'a l'b a list)(*strict*)
    apply (metis Cons_eq_appendI liftB.simps(1) liftB_reflects_length append_Nil teA_not_in_liftB concat_asso in_either_of_append nth_append_length)
   apply(rename_tac x xs e1 r A w w2a l'a l'b)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x xs e1 r A w w2a l'a l'b c)(*strict*)
   apply(case_tac c)
    apply(rename_tac x xs e1 r A w w2a l'a l'b c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x xs e1 r A w l'a l'b)(*strict*)
    apply(subgoal_tac "l'b=v")
     apply(rename_tac x xs e1 r A w l'a l'b)(*strict*)
     prefer 2
     apply(rule liftB_inj)
     apply(rule sym)
     apply(force)
    apply(rename_tac x xs e1 r A w l'a l'b)(*strict*)
    apply(clarify)
    apply(rule_tac
      x="liftB l'a"
      in exI)
    apply(rule_tac
      x="w@r"
      in exI)
    apply(force)
   apply(rename_tac x xs e1 r A w w2a l'a l'b c a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs e1 r A w w2a l'a l'b a list)(*strict*)
   apply (metis Cons_eq_appendI concat_asso)
  apply(rename_tac x xs e1 r l' A w w2a l'a l'b)(*strict*)
  apply (metis liftB_commutes_over_concat liftB_inj)
  done

lemma cfgLM_trans_der_context: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=w1'\<rparr>
  \<Longrightarrow> \<lparr>cfg_conf=(liftB v)@w2\<rparr>\<in> cfg_configurations G
  \<Longrightarrow> cfgLM.trans_der G (derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = (liftB v)@(cfg_conf x)@w2\<rparr>)) \<lparr>cfg_conf=(liftB v)@w1@w2\<rparr> (\<pi>1) \<lparr>cfg_conf=(liftB v)@w1'@w2\<rparr>"
  apply(simp add: cfgLM.trans_der_def)
  apply(rule context_conjI)
   apply(rule cfgLM.derivation_map_preserves_derivation2)
    apply(force)
   apply(clarsimp)
   apply(rename_tac a e b ea)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac a e b ea l r)(*strict*)
   apply(rule_tac
      x="liftB v@l"
      in exI)
   apply(clarsimp)
   apply (metis setA_liftB_subset setA_app empty_subsetI subset_empty)
  apply(rule conjI)
   apply(rule cfgLM.derivation_map_preserves_belongs)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rename_tac c)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(clarsimp)
   apply(rename_tac ca e)(*strict*)
   apply(simp add: setAConcat setBConcat)
  apply(rule conjI)
   apply(simp add: get_labels_derivation_map)
  apply(simp add: derivation_map_def)
  apply(clarsimp)
  done

lemma cfgLM_trans_der_context_prime: "
  valid_cfg G
  \<Longrightarrow> \<lparr>cfg_conf=(liftB v)@w2\<rparr>\<in> cfg_configurations G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=w1'\<rparr>
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=liftB v@w1@w2\<rparr> (\<pi>1) \<lparr>cfg_conf=liftB v@w1'@w2\<rparr>"
  apply(rule_tac
      x="(derivation_map d1 (\<lambda>x. \<lparr>cfg_conf = (liftB v)@(cfg_conf x)@w2\<rparr>))"
      in exI)
  apply(rule cfgLM_trans_der_context)
    apply(force)+
  done

lemma cfgLM_trans_der_der1: "
  valid_cfg G
  \<Longrightarrow> c \<in> cfg_configurations G
  \<Longrightarrow> cfgLM.trans_der G (der1 c) c [] c"
  apply(simp add: cfgLM.trans_der_def)
  apply(rule conjI)
   apply(rule cfgLM.der1_is_derivation)
  apply(rule conjI)
   apply(rule cfgLM.der1_belongs)
   apply(force)
  apply(rule conjI)
   apply (metis get_labelsEmpty)
  apply(rule conjI)
   apply(simp add: der1_def)
  apply(simp add: der1_def)
  done

lemma cfgLM_trans_der_concat_extend: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=(liftB v1)@v2@v4\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=v2\<rparr> \<pi>2 \<lparr>cfg_conf=v3\<rparr>
  \<Longrightarrow> cfgLM.trans_der G (derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = (liftB v1)@(cfg_conf v)@v4\<rparr>)) (length \<pi>1)) \<lparr>cfg_conf=w1\<rparr> (\<pi>1@\<pi>2) \<lparr>cfg_conf=liftB v1@v3@v4\<rparr>"
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac e ea)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(rule cfgLM.derivation_map_preserves_derivation2)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea a eb b)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac e ea a eb b l r)(*strict*)
    apply(rule_tac
      x="liftB v1@l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat)
    apply(rule setA_liftB)
   apply(rename_tac e ea)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_map_def)
  apply(rename_tac e ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac e ea)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_belongs)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac e ea)(*strict*)
   prefer 2
   apply(simp add: derivation_map_def derivation_append_def)
   apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB v1 @ cfg_conf v@v4\<rparr>)) (length \<pi>1)) (length \<pi>1 + length \<pi>2)"
      and s="get_labels SSd1 SSn1 @ get_labels SSd2 SSn2" for SSd1 SSn1 SSd2 SSn2
      in ssubst)
   apply(rename_tac e ea)(*strict*)
   apply(rule cfgLM.get_labels_concat2)
       apply(rename_tac e ea)(*strict*)
       apply(force)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(rule cfgLM.derivation_map_preserves_derivation2)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ea a eb b)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac e ea a eb b l r)(*strict*)
     apply(rule_tac
      x="liftB v1@l"
      in exI)
     apply(clarsimp)
     apply(simp add: setAConcat)
     apply(rule setA_liftB)
    apply(rename_tac e ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ea)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac e ea)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB v1 @ cfg_conf v@v4\<rparr>)) (length \<pi>2)"
      and s="get_labels (d2 ) (length \<pi>2)"
      in ssubst)
   apply(rename_tac e ea)(*strict*)
   apply(rule get_labels_derivation_map)
  apply(rename_tac e ea)(*strict*)
  apply(force)
  done

lemma cfgLM_trans_der_concat_extend_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=(liftB v1)@v2@v4\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=v2\<rparr> \<pi>2 \<lparr>cfg_conf=v3\<rparr>
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=w1\<rparr> (\<pi>1@\<pi>2) \<lparr>cfg_conf=liftB v1@v3@v4\<rparr>"
  apply(rule_tac
      x="(derivation_append d1 (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = (liftB v1)@(cfg_conf v)@v4\<rparr>)) (length \<pi>1))"
      in exI)
  apply(rule cfgLM_trans_der_concat_extend)
    apply(force)+
  done

lemma cfgLM_trans_der_from_empty: "
  cfgLM.trans_der G d \<lparr>cfg_conf=[]\<rparr> \<pi> c2
  \<Longrightarrow> \<pi>=[] \<and> c2=\<lparr>cfg_conf=[]\<rparr>"
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(case_tac "length \<pi>")
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
  apply(rename_tac e nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac e nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac e nat)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
    apply(rename_tac e nat)(*strict*)
    apply(force)
   apply(rename_tac e nat)(*strict*)
   apply(force)
  apply(rename_tac e nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac e nat e2 c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  done

lemma cfgLM_trans_der_biextend: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=liftB v1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=w2\<rparr> \<pi>2 \<lparr>cfg_conf=v2\<rparr>
  \<Longrightarrow> cfgLM.trans_der G (derivation_append
  (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@w2\<rparr>))
  (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = (liftB v1)@(cfg_conf v)\<rparr>))
  (length \<pi>1)) \<lparr>cfg_conf=w1@w2\<rparr> (\<pi>1@\<pi>2) \<lparr>cfg_conf=liftB v1@v2\<rparr>"
  apply(subgoal_tac "\<lparr>cfg_conf = w2\<rparr> \<in> cfg_configurations G")
   prefer 2
   apply(rule cfgLM.trans_der_belongs_configurations1)
   apply(force)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac e ea)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac e ea)(*strict*)
     apply(rule cfgLM.derivation_map_preserves_derivation2)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ea a eb b)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac e ea a eb b l r)(*strict*)
     apply(rule_tac
      x="l"
      in exI)
     apply(clarsimp)
    apply(rename_tac e ea)(*strict*)
    apply(rule cfgLM.derivation_map_preserves_derivation2)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea a eb b)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac e ea a eb b l r)(*strict*)
    apply(rule_tac
      x="liftB v1@l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat)
    apply(rule setA_liftB)
   apply(rename_tac e ea)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac e ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac e ea)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_belongs)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(rule cfgLM.derivation_map_preserves_belongs)
        apply(rename_tac e ea)(*strict*)
        apply(force)
       apply(rename_tac e ea)(*strict*)
       apply(force)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(rule cfgLM.derivation_map_preserves_derivation2)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ea a eb b)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac e ea a eb b l r)(*strict*)
     apply(rule_tac
      x="l"
      in exI)
     apply(clarsimp)
    apply(rename_tac e ea c)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(clarsimp)
    apply(rename_tac e ea ca)(*strict*)
    apply(rule conjI)
     apply(rename_tac e ea ca)(*strict*)
     apply (metis setA_app)
    apply(rename_tac e ea ca)(*strict*)
    apply (metis setB_app)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(rule conjI)
   apply(rename_tac e ea)(*strict*)
   prefer 2
   apply(simp add: derivation_map_def derivation_append_def)
   apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ w2\<rparr>)) (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB v1 @ cfg_conf v\<rparr>)) (length \<pi>1)) (length \<pi>1 + length \<pi>2)"
      and s="get_labels SSd1 SSn1 @ get_labels SSd2 SSn2" for SSd1 SSn1 SSd2 SSn2
      in ssubst)
   apply(rename_tac e ea)(*strict*)
   apply(rule cfgLM.get_labels_concat2)
       apply(rename_tac e ea)(*strict*)
       apply(force)
      apply(rename_tac e ea)(*strict*)
      apply(rule cfgLM.derivation_map_preserves_derivation2)
       apply(rename_tac e ea)(*strict*)
       apply(force)
      apply(rename_tac e ea)(*strict*)
      apply(clarsimp)
      apply(rename_tac e ea a eb b)(*strict*)
      apply(simp add: cfgLM_step_relation_def)
      apply(clarsimp)
      apply(rename_tac e ea a eb b l r)(*strict*)
      apply(rule_tac
      x="l"
      in exI)
      apply(clarsimp)
     apply(rename_tac e ea)(*strict*)
     apply(rule cfgLM.derivation_map_preserves_derivation2)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(clarsimp)
     apply(rename_tac e ea a eb b)(*strict*)
     apply(simp add: cfgLM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac e ea a eb b l r)(*strict*)
     apply(rule_tac
      x="liftB v1@l"
      in exI)
     apply(clarsimp)
     apply(simp add: setAConcat)
     apply(rule setA_liftB)
    apply(rename_tac e ea)(*strict*)
    apply(simp add: derivation_map_def)
   apply(rename_tac e ea)(*strict*)
   apply(simp add: derivation_map_def)
  apply(rename_tac e ea)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = cfg_conf v @ w2\<rparr>)) (length \<pi>1)"
      and s="get_labels d1 (length \<pi>1)"
      in ssubst)
   apply(rename_tac e ea)(*strict*)
   apply(rule get_labels_derivation_map)
  apply(rename_tac e ea)(*strict*)
  apply(rule_tac
      t="get_labels (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = liftB v1@cfg_conf v\<rparr>)) (length \<pi>2)"
      and s="get_labels d2 (length \<pi>2)"
      in ssubst)
   apply(rename_tac e ea)(*strict*)
   apply(rule get_labels_derivation_map)
  apply(rename_tac e ea)(*strict*)
  apply(force)
  done

lemma cfgLM_trans_der_biextend_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=liftB v1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=w2\<rparr> \<pi>2 \<lparr>cfg_conf=v2\<rparr>
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=w1@w2\<rparr> (\<pi>1@\<pi>2) \<lparr>cfg_conf=liftB v1@v2\<rparr>"
  apply(rule_tac
      x="(derivation_append (derivation_map d1 (\<lambda>v. \<lparr>cfg_conf = (cfg_conf v)@w2\<rparr>)) (derivation_map d2 (\<lambda>v. \<lparr>cfg_conf = (liftB v1)@(cfg_conf v)\<rparr>)) (length \<pi>1))"
      in exI)
  apply(rule cfgLM_trans_der_biextend)
    apply(force)+
  done

lemma cfgLM_trans_der_no_terminal_reached: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c1 \<pi> \<lparr>cfg_conf=teA A#x\<rparr>
  \<Longrightarrow> \<forall>i\<le>length \<pi>. hd(cfg_conf(the(get_configuration(d i))))\<noteq>teB b"
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac i e)(*strict*)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac i e)(*strict*)
   prefer 2
   apply(rule_tac
      m="length \<pi>"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac i e)(*strict*)
     apply(force)
    apply(rename_tac i e)(*strict*)
    apply(force)
   apply(rename_tac i e)(*strict*)
   apply(force)
  apply(rename_tac i e)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea c)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history c @ w = cfg_get_history \<lparr>cfg_conf = teA A # x\<rparr>")
   apply(rename_tac i e ea c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and i="i"
      and j="length \<pi>-i"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac i e ea c)(*strict*)
        apply(force)
       apply(rename_tac i e ea c)(*strict*)
       apply(force)
      apply(rename_tac i e ea c)(*strict*)
      apply(force)
     apply(rename_tac i e ea c)(*strict*)
     apply(force)
    apply(rename_tac i e ea c)(*strict*)
    apply(force)
   apply(rename_tac i e ea c)(*strict*)
   apply(force)
  apply(rename_tac i e ea c)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea c w)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(simp add: get_configuration_def)
  apply(case_tac c)
  apply(rename_tac i e ea c w cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea w cfg_conf)(*strict*)
  apply(case_tac cfg_conf)
   apply(rename_tac i e ea w cfg_conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e ea w)(*strict*)
   apply(case_tac "i=length \<pi>")
    apply(rename_tac i e ea w)(*strict*)
    apply(clarsimp)
   apply(rename_tac i e ea w)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac i e ea w)(*strict*)
    prefer 2
    apply(rule_tac
      m="length \<pi>"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac i e ea w)(*strict*)
      apply(simp add: cfgLM.trans_der_def)
     apply(rename_tac i e ea w)(*strict*)
     apply(force)
    apply(rename_tac i e ea w)(*strict*)
    apply(force)
   apply(rename_tac i e ea w)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e ea w e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac i e ea w cfg_conf a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea w list)(*strict*)
  apply(subgoal_tac "maxTermPrefix (teA A # x)=[]")
   apply(rename_tac i e ea w list)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB_front)
  apply(rename_tac i e ea w list)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e ea list)(*strict*)
  apply (metis maxTermPrefix_pull_out list.simps(3))
  done

lemma cfgLM_decompose_eliminating_derivation_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = w1@w2\<rparr> \<pi> \<lparr>cfg_conf = []\<rparr>
  \<Longrightarrow> \<exists>d1 d2 \<pi>1 \<pi>2.
  cfgLM.trans_der G d1 \<lparr>cfg_conf = w1\<rparr> \<pi>1 \<lparr>cfg_conf = []\<rparr>
  \<and> cfgLM.trans_der G d2 \<lparr>cfg_conf = w2\<rparr> \<pi>2 \<lparr>cfg_conf = []\<rparr>
  \<and> \<pi>=\<pi>1@\<pi>2"
  apply(subgoal_tac "\<exists>d1 d2 w1' w2' n1 n2. cfgLM.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgLM.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1'@w2'=[] \<and> maximum_of_domain d1 n1 \<and> maximum_of_domain d2 n2 \<and> n1+n2=(length \<pi>) \<and> get_labels d (length \<pi>)=get_labels d1 n1@ (get_labels d2 n2)")
   prefer 2
   apply(rule cfgLM_decompose_eliminating_derivation)
      apply(force)
     apply(simp add: cfgLM.trans_der_def)
    apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac e)(*strict*)
    apply(rule_tac
      x="length \<pi>"
      in exI)
    apply(clarsimp)
    apply(case_tac "d (Suc (length \<pi>))")
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e a)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length \<pi>) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
     apply(rename_tac e a)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc(length \<pi>)"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac e a)(*strict*)
       apply(force)
      apply(rename_tac e a)(*strict*)
      apply(force)
     apply(rename_tac e a)(*strict*)
     apply(force)
    apply(rename_tac e a)(*strict*)
    apply(clarsimp)
    apply(rename_tac e e2 c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
   apply(simp add: maximum_of_domain_def)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(case_tac "d (Suc (length \<pi>))")
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e a)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length \<pi>) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac e a)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(length \<pi>)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac e a)(*strict*)
      apply(force)
     apply(rename_tac e a)(*strict*)
     apply(force)
    apply(rename_tac e a)(*strict*)
    apply(force)
   apply(rename_tac e a)(*strict*)
   apply(clarsimp)
   apply(rename_tac e e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(simp add: maximum_of_domain_def)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 y e n2 ya)(*strict*)
  apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(case_tac "d1 0")
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = w1 @ w2\<rparr> \<in> cfg_configurations G")
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   prefer 2
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule_tac
      x="d1"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule_tac
      x="d2"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="map the (get_labels d1 n)"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="length (get_labels d1 n)"
      and s="n"
      in ssubst)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(rule cfgLM.derivation_belongs)
      apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
      apply(force)
     apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule_tac
      x="map the (get_labels d2 na)"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="length (get_labels d2 na)"
      and s="na"
      in ssubst)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(rule Some_map_inj)
  apply(rule_tac
      t="map Some \<pi>"
      and s="get_labels d1 n1 @ get_labels d2 n2"
      in ssubst)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(simp (no_asm))
  apply(subgoal_tac "n1=n")
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgLM.maximum_of_domainUnique)
     apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(subgoal_tac "n2=na")
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in cfgLM.maximum_of_domainUnique)
     apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
     apply(force)
    apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac d1 d2 n1 y e n2 ya n na xa xaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
  apply(rule_tac
      t="map (Some \<circ> the) (get_labels d1 n)"
      and s="get_labels d1 n"
      in subst)
   apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
    apply(force)
   apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
  apply(rule conjI)
   apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
  apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
   apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
   apply(force)
  apply(rename_tac d1 d2 e n na xa xaa)(*strict*)
  apply(force)
  done

lemma cfgLM_decompose_derivation: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=a#v\<rparr> \<pi> \<lparr>cfg_conf=w\<rparr>
  \<Longrightarrow> \<exists>d1 d2 \<pi>1 \<pi>2 v1 v2.
  \<pi>=\<pi>1@\<pi>2
  \<and> cfgLM.trans_der G d1 \<lparr>cfg_conf=[a]\<rparr> \<pi>1 \<lparr>cfg_conf=v1\<rparr>
  \<and> cfgLM.trans_der G d2 \<lparr>cfg_conf=v\<rparr> \<pi>2 \<lparr>cfg_conf=v2\<rparr>
  \<and> w=v1@v2
  \<and> (setA v1\<noteq>{} \<longrightarrow> \<pi>2=[])"
  apply(subgoal_tac "\<lparr>cfg_conf = a # v @ w\<rparr> \<in> cfg_configurations G")
   prefer 2
   apply(subgoal_tac "\<lparr>cfg_conf = a # v\<rparr> \<in> cfg_configurations G")
    apply(subgoal_tac "\<lparr>cfg_conf = w\<rparr> \<in> cfg_configurations G")
     apply(simp add: cfg_configurations_def)
     apply(simp add: simpY)
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
    apply(rename_tac e)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(induct \<pi> arbitrary: w rule: rev_induct)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = [a]\<rparr>"
      in exI)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = v\<rparr>"
      in exI)
   apply(rule_tac
      x="[a]"
      in exI)
   apply(rule conjI)
    apply(rename_tac w)(*strict*)
    apply(rule cfgLM_trans_der_der1)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(rule conjI)
    apply(rename_tac w)(*strict*)
    apply(rule cfgLM_trans_der_der1)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac w)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac x xs w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs w)(*strict*)
   prefer 2
   apply(simp only: cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs w e)(*strict*)
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs w e)(*strict*)
     apply(force)
    apply(rename_tac x xs w e)(*strict*)
    apply(force)
   apply(rename_tac x xs w e)(*strict*)
   apply(force)
  apply(rename_tac x xs w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xs w e1 e2 c1 c2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs w e1 e2 c1 c2 l r cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac x xs w e1 e2 c1 c2 l r cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w e1 e2 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac x xs w e1 e2 l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac x xs wa e1 e2 l r A w)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac x xs wa e1 e2 l r A w)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac x xs wa e1 e2 l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs wa e1 r A w l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(erule_tac
      x="liftB l' @ teA A # r"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs wa e1 r A w l')(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs wa e1 r A w l')(*strict*)
    apply(force)
   apply(rename_tac x xs wa e1 r A w l')(*strict*)
   apply(force)
  apply(rename_tac x xs wa e1 r A w l')(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs wa e1 r A w l')(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf = liftB l' @ teA A # r\<rparr>\<in> cfg_configurations G")
    apply(rename_tac x xs wa e1 r A w l')(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac x xs wa e1 r A w l')(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac x xs e1 r A w l')(*strict*)
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac x xs e1 r A w l')(*strict*)
    apply(force)
   apply(rename_tac x xs e1 r A w l')(*strict*)
   apply(force)
  apply(rename_tac x xs wa e1 r A w l')(*strict*)
  apply(clarsimp)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der SSG (der2 SSc SSe SSc') SSc [SSe] SSc'" for SSG SSc SSe SSc')
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
   prefer 2
   apply(rule_tac
      e="\<lparr>prod_lhs = A, prod_rhs = w\<rparr>"
      and c="\<lparr>cfg_conf = [teA A]\<rparr>"
      and c'="\<lparr>cfg_conf = w\<rparr>"
      in cfgLM.trans_der_der2)
     apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
     apply(force)
    apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(simp add: simpY)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w\<rparr>"
      in ballE)
     apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
     apply(force)
    apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
    apply(force)
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
  apply(case_tac "setA v1 \<noteq> {}")
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2 A. v1=liftB w1 @ teA A # w2")
    apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
    prefer 2
    apply(rule left_most_terminal_exists)
    apply(force)
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 v2 w1 w2 Aa)(*strict*)
   apply(simp add: simpY)
   apply(subgoal_tac "l'=w1")
    apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 v2 w1 w2 Aa)(*strict*)
    prefer 2
    apply (metis leading_liftB_prefix_eq)
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 v2 w1 w2 Aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x wa e1 w d1 d2 \<pi>1 v2 w1 w2 Aa)(*strict*)
   apply(subgoal_tac "v=v2")
    apply(rename_tac x wa e1 w d1 d2 \<pi>1 v2 w1 w2 Aa)(*strict*)
    prefer 2
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
   apply(rename_tac x wa e1 w d1 d2 \<pi>1 v2 w1 w2 Aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x wa e1 w d1 d2 \<pi>1 w1 w2 Aa)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
    apply(rename_tac x wa e1 w d1 d2 \<pi>1 w1 w2 Aa)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="d1"
      and ?d2.0="(der2 \<lparr>cfg_conf = [teA Aa]\<rparr> \<lparr>prod_lhs = Aa, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr>)"
      and ?v1.0="w1"
      and ?v2.0="[teA Aa]"
      and ?v4.0="w2"
      in cfgLM_trans_der_concat_extend_prime)
      apply(rename_tac x wa e1 w d1 d2 \<pi>1 w1 w2 Aa)(*strict*)
      apply(force)
     apply(rename_tac x wa e1 w d1 d2 \<pi>1 w1 w2 Aa)(*strict*)
     apply(force)
    apply(rename_tac x wa e1 w d1 d2 \<pi>1 w1 w2 Aa)(*strict*)
    apply(force)
   apply(rename_tac x wa e1 w d1 d2 \<pi>1 w1 w2 Aa)(*strict*)
   apply(thin_tac "cfgLM.trans_der G d1 \<lparr>cfg_conf = [a]\<rparr> \<pi>1 \<lparr>cfg_conf = liftB w1 @ teA Aa # w2\<rparr>")
   apply(rename_tac x wa e1 w d1 d2 \<pi>1 w1 w2 Aa)(*strict*)
   apply(thin_tac "cfgLM.trans_der G (der2 \<lparr>cfg_conf = [teA Aa]\<rparr> \<lparr>prod_lhs = Aa, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr>) \<lparr>cfg_conf = [teA Aa]\<rparr> [\<lparr>prod_lhs = Aa, prod_rhs = w\<rparr>] \<lparr>cfg_conf = w\<rparr>")
   apply(rename_tac x wa e1 w d1 d2 \<pi>1 w1 w2 Aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x wa e1 w d2 \<pi>1 w1 w2 Aa da)(*strict*)
   apply(rule_tac
      x="da"
      in exI)
   apply(rule_tac
      x="d2"
      in exI)
   apply(rule_tac
      x="\<pi>1@[x]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule_tac
      x="liftB w1 @ w @ w2"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x wa e1 w d2 \<pi>1 w1 w2 Aa da)(*strict*)
    apply(rule_tac
      t="x"
      and s="\<lparr>prod_lhs = Aa, prod_rhs = w\<rparr>"
      in ssubst)
     apply(rename_tac x wa e1 w d2 \<pi>1 w1 w2 Aa da)(*strict*)
     apply(simp add: cfgLM.trans_der_def)
     apply(clarsimp)
     apply(rename_tac x e1 w d2 \<pi>1 w1 w2 Aa da ea)(*strict*)
     apply (metis Some_inj get_labels_Not_None length_map lessI nth_Cons_0 nth_append_2_prime_prime)
    apply(rename_tac x wa e1 w d2 \<pi>1 w1 w2 Aa da)(*strict*)
    apply(force)
   apply(rename_tac x wa e1 w d2 \<pi>1 w1 w2 Aa da)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>l'. liftB l' = v1")
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB v1"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v2 l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(rule_tac
      x="d1"
      in exI)
  apply(case_tac "setA v2 = {}")
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v2 l'a)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = v2")
    apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v2 l'a)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB v2"
      in exI)
    apply (rule liftBDeConv2)
    apply(force)
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v2 l'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 l'a l'b)(*strict*)
   apply(thin_tac "setA (liftB l'b) = {}")
   apply (metis setA_liftB liftB_commutes_over_concat elemInsetA equals0D)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v2 l'a)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2 A. v2=liftB w1 @ teA A # w2")
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v2 l'a)(*strict*)
   prefer 2
   apply(rule left_most_terminal_exists)
   apply(force)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 v2 l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
  apply(simp add: simpY)
  apply(subgoal_tac "l'=l'a@w1")
   apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
   prefer 2
   apply (metis append_Nil2 maximalPrefixB_drop_liftB maximalPrefixB_front)
  apply(rename_tac x wa e1 r A w l' d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x wa e1 r A w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
  apply(simp add: simpY)
  apply(clarsimp)
  apply(rename_tac x wa e1 w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv3 @ SSv4\<rparr>" for SSG SSw1 SSrenPI10 SSrenPI20 SSv1 SSv3 SSv4)
   apply(rename_tac x wa e1 w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d2"
      and ?d2.0="(der2 \<lparr>cfg_conf = [teA Aa]\<rparr> \<lparr>prod_lhs = Aa, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr>)"
      and ?v1.0="w1"
      and ?v2.0="[teA Aa]"
      and ?v4.0="w2"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac x wa e1 w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
     apply(force)
    apply(rename_tac x wa e1 w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
    apply(force)
   apply(rename_tac x wa e1 w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
   apply(force)
  apply(rename_tac x wa e1 w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf = v\<rparr> \<pi>2 \<lparr>cfg_conf = liftB w1 @ teA Aa # w2\<rparr>")
  apply(rename_tac x wa e1 w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
  apply(thin_tac "cfgLM.trans_der G (der2 \<lparr>cfg_conf = [teA Aa]\<rparr> \<lparr>prod_lhs = Aa, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr>) \<lparr>cfg_conf = [teA Aa]\<rparr> [\<lparr>prod_lhs = Aa, prod_rhs = w\<rparr>] \<lparr>cfg_conf = w\<rparr>")
  apply(rename_tac x wa e1 w d1 d2 \<pi>1 \<pi>2 l'a w1 w2 Aa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x wa e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da)(*strict*)
  apply(rule_tac
      x="da"
      in exI)
  apply(rule_tac
      x="\<pi>1"
      in exI)
  apply(rule_tac
      x="\<pi>2@[x]"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="liftB l'a"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="liftB w1 @ w @ w2"
      in exI)
  apply(simp add: simpY)
  apply(rule_tac
      t="x"
      and s="\<lparr>prod_lhs = Aa, prod_rhs = w\<rparr>"
      in ssubst)
   apply(rename_tac x wa e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac x e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da e ea)(*strict*)
   apply(rule Some_inj)
   apply(rule_tac
      t="Some x"
      and s="((map Some \<pi>1 @ map Some \<pi>2) @ [Some x])!(length \<pi>1+length \<pi>2)"
      in ssubst)
    apply(rename_tac x e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da e ea)(*strict*)
    apply(rule_tac
      t="((map Some \<pi>1 @ map Some \<pi>2) @ [Some x])!(length \<pi>1+length \<pi>2)"
      and s="([Some x])!((length \<pi>1+length \<pi>2)-length(map Some \<pi>1 @ map Some \<pi>2))"
      in ssubst)
     apply(rename_tac x e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da e ea)(*strict*)
     apply(rule nth_append_2)
     apply(force)
    apply(rename_tac x e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da e ea)(*strict*)
    apply(force)
   apply(rename_tac x e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da e ea)(*strict*)
   apply(rule_tac
      t="(map Some \<pi>1 @ map Some \<pi>2) @ [Some x]"
      and s="get_labels d (Suc (length \<pi>1 + length \<pi>2))"
      in ssubst)
    apply(rename_tac x e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da e ea)(*strict*)
    apply(force)
   apply(rename_tac x e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da e ea)(*strict*)
   apply (metis get_labels_Not_None length_append lessI)
  apply(rename_tac x wa e1 w d1 \<pi>1 \<pi>2 l'a w1 w2 Aa da)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM.trans_der_def)
  done

lemma cfgLM_decompose_derivation2: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=v\<rparr> \<pi> \<lparr>cfg_conf=w1@[x]@w2\<rparr>
  \<Longrightarrow> \<exists>d1 dx d2 \<pi>1 \<pi>x \<pi>2 v1 Vx v2 w1'' w2'' w1' w2'.
  cfgLM.trans_der G d1 \<lparr>cfg_conf=v1\<rparr> \<pi>1 \<lparr>cfg_conf=w1'\<rparr>
  \<and> cfgLM.trans_der G dx \<lparr>cfg_conf=[Vx]\<rparr> \<pi>x \<lparr>cfg_conf=w1''@[x]@w2''\<rparr>
  \<and> cfgLM.trans_der G d2 \<lparr>cfg_conf=v2\<rparr> \<pi>2 \<lparr>cfg_conf=w2'\<rparr>
  \<and> v=v1@[Vx]@v2
  \<and> \<pi>=\<pi>1@\<pi>x@\<pi>2
  \<and> w1=w1'@w1''
  \<and> w2=w2''@w2'"
  apply(induct v arbitrary: d \<pi> w1 w2)
   apply(rename_tac d \<pi> w1 w2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d \<pi> w1 w2 e)(*strict*)
   apply(case_tac "\<pi>")
    apply(rename_tac d \<pi> w1 w2 e)(*strict*)
    apply(clarsimp)
   apply(rename_tac d \<pi> w1 w2 e a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2 e a list)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac d w1 w2 e a list)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc(length list)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d w1 w2 e a list)(*strict*)
      apply(force)
     apply(rename_tac d w1 w2 e a list)(*strict*)
     apply(force)
    apply(rename_tac d w1 w2 e a list)(*strict*)
    apply(force)
   apply(rename_tac d w1 w2 e a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2 e a list e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac a v d \<pi> w1 w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>d1 d2 \<pi>1 \<pi>2 v1 v2. SSrenPI = \<pi>1 @ \<pi>2 \<and> cfgLM.trans_der SSG d1 \<lparr>cfg_conf = [SSa]\<rparr> \<pi>1 \<lparr>cfg_conf = v1\<rparr> \<and> cfgLM.trans_der SSG d2 \<lparr>cfg_conf = SSv\<rparr> \<pi>2 \<lparr>cfg_conf = v2\<rparr> \<and> SSw = v1 @ v2 \<and> (setA v1 \<noteq> {} \<longrightarrow> \<pi>2 = [])" for SSrenPI SSa SSG SSv SSw)
   apply(rename_tac a v d \<pi> w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and \<pi>="\<pi>"
      and w="w1@x#w2"
      and a="a"
      and v="v"
      in cfgLM_decompose_derivation)
    apply(rename_tac a v d \<pi> w1 w2)(*strict*)
    apply(force)
   apply(rename_tac a v d \<pi> w1 w2)(*strict*)
   apply(force)
  apply(rename_tac a v d \<pi> w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
  apply(case_tac "setA v1 \<noteq> {}")
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 v1 v2)(*strict*)
   apply(subgoal_tac "v=v2")
    apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 v1 v2)(*strict*)
    prefer 2
    apply(simp add: cfgLM.trans_der_def)
    apply(clarsimp)
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 v1 v2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2)(*strict*)
   apply(subgoal_tac "strict_prefix v1 (w1@[x]) \<or> prefix (w1@[x]) v1")
    apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2)(*strict*)
    prefer 2
    apply(rule mutual_strict_prefix_prefix)
    apply(rule sym)
    apply(force)
   apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2)(*strict*)
   apply(erule disjE)
    apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac a d w1 d1 d2 \<pi>1 v2 c)(*strict*)
    apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
    apply(rule_tac
      x="d1"
      in exI)
    apply(rule_tac
      x="d2"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="\<pi>1"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="a"
      in exI)
    apply(rule_tac
      x="v2"
      in exI)
    apply(rule_tac
      x="w1"
      in exI)
    apply(rule_tac
      x="c"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule conjI)
     apply(rename_tac a d w1 d1 d2 \<pi>1 v2 c)(*strict*)
     apply(rule cfgLM_trans_der_der1)
      apply(rename_tac a d w1 d1 d2 \<pi>1 v2 c)(*strict*)
      apply(force)
     apply(rename_tac a d w1 d1 d2 \<pi>1 v2 c)(*strict*)
     apply(simp add: cfg_configurations_def)
    apply(rename_tac a d w1 d1 d2 \<pi>1 v2 c)(*strict*)
    apply(rule conjI)
     apply(rename_tac a d w1 d1 d2 \<pi>1 v2 c)(*strict*)
     apply(force)
    apply(rename_tac a d w1 d1 d2 \<pi>1 v2 c)(*strict*)
    apply(clarsimp)
   apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2 c)(*strict*)
   apply(subgoal_tac "c=[] \<or> (\<exists>w' a'. c=w'@[a'])")
    apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2 c)(*strict*)
    prefer 2
    apply(rule case_list)
   apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2 c)(*strict*)
   apply(erule disjE)
    apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2 c)(*strict*)
    apply(clarsimp)
   apply(rename_tac a d w1 w2 d1 d2 \<pi>1 v1 v2 c)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d w2 d1 d2 \<pi>1 v1 w')(*strict*)
   apply(subgoal_tac "\<exists>w1 w2 A. v1=liftB w1 @ teA A # w2")
    apply(rename_tac a d w2 d1 d2 \<pi>1 v1 w')(*strict*)
    prefer 2
    apply(rule left_most_terminal_exists)
    apply(force)
   apply(rename_tac a d w2 d1 d2 \<pi>1 v1 w')(*strict*)
   apply(clarsimp)
   apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A)(*strict*)
   apply(simp add: simpY)
   apply(subgoal_tac "\<lparr>cfg_conf = a # w' @ x # w2\<rparr> \<in> cfg_configurations G")
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A)(*strict*)
    prefer 2
    apply(simp only: cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A e ea eb)(*strict*)
    apply(rule_tac
      d="d"
      in cfgLM.belongs_configurations)
     apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A e ea eb)(*strict*)
     apply(force)
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A e ea eb)(*strict*)
    apply(force)
   apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A)(*strict*)
   apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = liftB SSv @ SSw1 @ SSw2\<rparr> SSrenPI10 \<lparr>cfg_conf = liftB SSv @ SSw1' @ SSw2\<rparr>" for SSG SSw1 SSrenPI10 SSv SSw1' SSw2)
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A)(*strict*)
    prefer 2
    apply(rule_tac
      ?d1.0="d1"
      and v="[]"
      and ?w2.0="w'"
      in cfgLM_trans_der_context_prime)
      apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A)(*strict*)
      apply(force)
     apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A)(*strict*)
     apply(simp add: cfg_configurations_def simpY)
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A)(*strict*)
    apply(force)
   apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
   apply(erule_tac
      x="da"
      in allE)
   apply(erule_tac
      x="der1 \<lparr>cfg_conf=[x]\<rparr>"
      in allE)
   apply(erule_tac
      x="der1 \<lparr>cfg_conf=w2\<rparr>"
      in allE)
   apply(erule_tac
      x="\<pi>1"
      in allE)
   apply(erule_tac
      x="[]"
      in allE)
   apply(erule_tac
      x="[]"
      in allE)
   apply(erule_tac
      x="a#w'"
      in allE)
   apply(erule_tac
      x="x"
      in allE)
   apply(erule_tac
      x="w2"
      in allE)
   apply(erule_tac
      x="[]"
      in allE)
   apply(erule_tac
      x="[]"
      in allE)
   apply(erule_tac
      x="liftB w1 @ teA A # w2a @ w'"
      in allE)
   apply(clarsimp)
   apply(erule impE)
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
    apply(rule cfgLM_trans_der_der1)
     apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
     apply(force)
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
   apply(erule_tac
      x="w2"
      in allE)
   apply(erule impE)
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
    apply(rule cfgLM_trans_der_der1)
     apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
     apply(force)
    apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
    apply(simp add: cfg_configurations_def simpY)
   apply(rename_tac a d w2 d1 d2 \<pi>1 w' w1 w2a A da)(*strict*)
   apply(force)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>l'. liftB l' = v1")
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB v1"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "strict_prefix (liftB l') (w1@[x]) \<or> prefix (w1@[x]) (liftB l')")
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l')(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(rule sym)
   apply(force)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l')(*strict*)
  apply(erule disjE)
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l')(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l' c)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = w1")
    apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l' c)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB w1"
      in exI)
    apply (rule liftBDeConv2)
    apply(rule setA_substring)
    apply(force)
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l' c)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = [x]")
    apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB [x]"
      in exI)
    apply (rule liftBDeConv2)
    apply(rule_tac
      ?w1.0="liftB l'a"
      in setA_substring2)
    apply(force)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a l'b)(*strict*)
   apply(case_tac l'b)
    apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a l'b)(*strict*)
    apply(clarsimp)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a l'b aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a aa list)(*strict*)
   apply(case_tac list)
    apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a aa list)(*strict*)
    prefer 2
    apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a aa list ab lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a aa list)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a aa)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = c")
    apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a aa)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB c"
      in exI)
    apply (rule liftBDeConv2)
    apply(rule_tac ?w2.0="liftB l'a @ [teB aa]" in setA_substring_prime)
    apply(force)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' c l'a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' l'a aa l'b)(*strict*)
   apply(subgoal_tac "l'a@aa#l'b=l'")
    apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' l'a aa l'b)(*strict*)
    prefer 2
    apply(rule liftB_inj)
    apply(simp add: simpY)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l' l'a aa l'b)(*strict*)
   apply(clarsimp)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 v2 l'a aa l'b)(*strict*)
   apply(thin_tac "liftB l'a @ teB aa # liftB l'b = liftB (l'a @ aa # l'b)")
   apply(simp add: simpY)
   apply(clarsimp)
   apply(rename_tac a v d d1 d2 \<pi>1 \<pi>2 v2 l'a aa l'b)(*strict*)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf = []\<rparr>"
      in exI)
   apply(rule_tac
      x="d1"
      in exI)
   apply(rule_tac
      x="d2"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="\<pi>1"
      in exI)
   apply(rule_tac
      x="\<pi>2"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="a"
      in exI)
   apply(rule_tac
      x="v"
      in exI)
   apply(rule_tac
      x="liftB l'a"
      in exI)
   apply(rule_tac
      x="liftB l'b"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(rule cfgLM_trans_der_der1)
    apply(rename_tac a v d d1 d2 \<pi>1 \<pi>2 v2 l'a aa l'b)(*strict*)
    apply(force)
   apply(rename_tac a v d d1 d2 \<pi>1 \<pi>2 v2 l'a aa l'b)(*strict*)
   apply(simp add: cfg_configurations_def)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l')(*strict*)
  apply(simp add: strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l' c)(*strict*)
  apply(subgoal_tac "c=[] \<or> (\<exists>w' a'. c=w'@[a'])")
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l' c)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l' c)(*strict*)
  apply(erule disjE)
   apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l' c)(*strict*)
   apply(clarsimp)
  apply(rename_tac a v d w1 w2 d1 d2 \<pi>1 \<pi>2 v2 l' c)(*strict*)
  apply(clarsimp)
  apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 l' w')(*strict*)
  apply(erule_tac
      x="d2"
      in meta_allE)
  apply(erule_tac
      x="\<pi>2"
      in meta_allE)
  apply(erule_tac
      x="w'"
      in meta_allE)
  apply(erule_tac
      x="w2"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 l' w')(*strict*)
   apply(force)
  apply(rename_tac a v d w2 d1 d2 \<pi>1 \<pi>2 l' w')(*strict*)
  apply(clarsimp)
  apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d \<lparr>cfg_conf = SSw1 @ SSw2\<rparr> (SSrenPI10 @ SSrenPI20) \<lparr>cfg_conf = liftB SSv1 @ SSv2\<rparr>" for SSG SSw1 SSw2 SSrenPI10 SSrenPI20 SSv1 SSv2)
   apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and ?d1.0="d1"
      and ?d2.0="d1a"
      in cfgLM_trans_der_biextend_prime)
     apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
     apply(force)
    apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
    apply(force)
   apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
   apply(force)
  apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
  apply(thin_tac "cfgLM.trans_der G d1 \<lparr>cfg_conf = [a]\<rparr> \<pi>1 \<lparr>cfg_conf = liftB l'\<rparr>")
  apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = a # v1 @ Vx # v2\<rparr> (\<pi>1 @ \<pi>1a @ \<pi>x @ \<pi>2a) \<lparr>cfg_conf = liftB l' @ w1' @ w1'' @ x # w2'' @ w2'\<rparr>")
  apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
  apply(thin_tac "cfgLM.trans_der G d1a \<lparr>cfg_conf = v1\<rparr> \<pi>1a \<lparr>cfg_conf = w1'\<rparr>")
  apply(rename_tac a d d1 d2 \<pi>1 l' d1a dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2')(*strict*)
  apply(clarsimp)
  apply(rename_tac a d2 \<pi>1 l' dx d2a \<pi>1a \<pi>x \<pi>2a v1 Vx v2 w1'' w2'' w1' w2' d)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(erule_tac
      x="dx"
      in allE)
  apply(erule_tac
      x="d2a"
      in allE)
  apply(erule_tac
      x="\<pi>1@\<pi>1a"
      in allE)
  apply(erule_tac
      x="\<pi>x"
      in allE)
  apply(erule_tac
      x="\<pi>2a"
      in allE)
  apply(erule_tac
      x="a#v1"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="w1''"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="w2''"
      in allE)
  apply(clarsimp)
  apply(force)
  done

lemma equal_elimination_for_equal_nonterminal: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=[teA A1]\<rparr> \<pi> \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=[teA A2]\<rparr> \<pi> \<lparr>cfg_conf=liftB \<alpha>2\<rparr>
  \<Longrightarrow> A1=A2"
  apply(case_tac \<pi>)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(case_tac "\<alpha>2")
    apply(clarsimp)
   apply(rename_tac a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac a list e ea)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac a list e ea)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(length list)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac a list e ea)(*strict*)
     apply(force)
    apply(rename_tac a list e ea)(*strict*)
    apply(force)
   apply(rename_tac a list e ea)(*strict*)
   apply(force)
  apply(rename_tac a list e ea)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac a list e ea)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc(length list)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac a list e ea)(*strict*)
     apply(force)
    apply(rename_tac a list e ea)(*strict*)
    apply(force)
   apply(rename_tac a list e ea)(*strict*)
   apply(force)
  apply(rename_tac a list e ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list e ea e2 e2a c2 c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac a list e ea e2 e2a c2 c2a l r la ra)(*strict*)
  apply(case_tac la)
   apply(rename_tac a list e ea e2 e2a c2 c2a l r la ra)(*strict*)
   prefer 2
   apply(rename_tac a list e ea e2 e2a c2 c2a l r la ra aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list e ea e2 e2a c2 c2a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list e ea e2 e2a c2 c2a l r)(*strict*)
  apply(case_tac l)
   apply(rename_tac a list e ea e2 e2a c2 c2a l r)(*strict*)
   prefer 2
   apply(rename_tac a list e ea e2 e2a c2 c2a l r aa lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac a list e ea e2 e2a c2 c2a l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list e ea e2 e2a c2 c2a)(*strict*)
  apply(case_tac c2)
  apply(rename_tac a list e ea e2 e2a c2 c2a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list e ea e2 e2a c2a)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac a list e ea e2 e2a c2a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a list e ea e2 e2a)(*strict*)
  apply(subgoal_tac "e2=a")
   apply(rename_tac a list e ea e2 e2a)(*strict*)
   apply(subgoal_tac "e2a=a")
    apply(rename_tac a list e ea e2 e2a)(*strict*)
    apply(force)
   apply(rename_tac a list e ea e2 e2a)(*strict*)
   apply(subgoal_tac "Some e2a = Some a")
    apply(rename_tac a list e ea e2 e2a)(*strict*)
    apply(force)
   apply(rename_tac a list e ea e2 e2a)(*strict*)
   apply(rule_tac
      t="Some a"
      and s="(Some a # map Some list)!0"
      in ssubst)
    apply(rename_tac a list e ea e2 e2a)(*strict*)
    apply(force)
   apply(rename_tac a list e ea e2 e2a)(*strict*)
   apply(rule sym)
   apply(rule_tac
      d="d2"
      in getLabel_at_pos)
     apply(rename_tac a list e ea e2 e2a)(*strict*)
     apply(force)
    apply(rename_tac a list e ea e2 e2a)(*strict*)
    apply(force)
   apply(rename_tac a list e ea e2 e2a)(*strict*)
   apply(force)
  apply(rename_tac a list e ea e2 e2a)(*strict*)
  apply(subgoal_tac "Some e2 = Some a")
   apply(rename_tac a list e ea e2 e2a)(*strict*)
   apply(force)
  apply(rename_tac a list e ea e2 e2a)(*strict*)
  apply(rule_tac
      t="Some a"
      and s="(Some a # map Some list)!0"
      in ssubst)
   apply(rename_tac a list e ea e2 e2a)(*strict*)
   apply(force)
  apply(rename_tac a list e ea e2 e2a)(*strict*)
  apply(rule sym)
  apply(rule_tac
      d="d1"
      in getLabel_at_pos)
    apply(rename_tac a list e ea e2 e2a)(*strict*)
    apply(force)
   apply(rename_tac a list e ea e2 e2a)(*strict*)
   apply(force)
  apply(rename_tac a list e ea e2 e2a)(*strict*)
  apply(force)
  done

lemma cfgLM_trans_der_unique_result: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 c p c1
  \<Longrightarrow> cfgLM.trans_der G d2 c p c2
  \<Longrightarrow> c1=c2"
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(subgoal_tac "d1(length p) =d2(length p)")
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(rule_tac
      ?n2.0="length p"
      in cfgLM_equal_positions_when_same_productions)
         apply(rename_tac e ea)(*strict*)
         apply(force)
        apply(rename_tac e ea)(*strict*)
        apply(force)
       apply(rename_tac e ea)(*strict*)
       apply(force)
      apply(rename_tac e ea)(*strict*)
      apply(force)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(force)
  done

lemma cfgLM_trans_der_coincide_up_to_unused_context: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w\<rparr> \<pi> \<lparr>cfg_conf=w'\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=liftB \<alpha>@w@y\<rparr> \<pi> \<lparr>cfg_conf=w''\<rparr>
  \<Longrightarrow> liftB \<alpha>@w'@y = w''"
  apply(induct \<pi> arbitrary: w' w'' rule: rev_induct)
   apply(rename_tac w' w'')(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac x xs w' w'')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs w' w'')(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs w' w'' e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs w' w'' e ea)(*strict*)
     apply(force)
    apply(rename_tac x xs w' w'' e ea)(*strict*)
    apply(force)
   apply(rename_tac x xs w' w'' e ea)(*strict*)
   apply(force)
  apply(rename_tac x xs w' w'')(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (length xs) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac x xs w' w'')(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs w' w'' e ea e1 e2 c1 c2)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc(length xs)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac x xs w' w'' e ea e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac x xs w' w'' e ea e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac x xs w' w'' e ea e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac x xs w' w'')(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a c2 c2a)(*strict*)
  apply(subgoal_tac "c2=\<lparr>cfg_conf = w'\<rparr>")
   apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a c2 c2a)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a c2 c2a e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(force)
  apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a c2 c2a)(*strict*)
  apply(subgoal_tac "c2a=\<lparr>cfg_conf = w''\<rparr>")
   apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a c2 c2a)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a c2 c2a e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(force)
  apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a c2 c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
  apply(subgoal_tac "e2=x")
   apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
   prefer 2
   apply(rule cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
       apply(force)
      apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
      apply(force)
     apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
     apply(force)
    apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
    apply(force)
   apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
   apply(force)
  apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
  apply(subgoal_tac "e2a=x")
   apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
       apply(force)
      apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
      apply(force)
     apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
     apply(force)
    apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
    apply(force)
   apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
   apply(force)
  apply(rename_tac x xs w' w'' e1 e1a e2 e2a c1 c1a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w' w'' e1 e1a c1 c1a)(*strict*)
  apply(case_tac c1)
  apply(rename_tac x xs w' w'' e1 e1a c1 c1a cfg_conf)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac x xs w' w'' e1 e1a c1 c1a cfg_conf cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w' w'' e1 e1a cfg_conf cfg_confa)(*strict*)
  apply(rename_tac w1 w2)
  apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
  apply(erule_tac
      x="w1"
      in meta_allE)
  apply(erule_tac
      x="w2"
      in meta_allE)
  apply(erule_tac meta_impE)
   apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
    apply(force)
   apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
   apply(force)
  apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
    apply(force)
   apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
   apply(force)
  apply(rename_tac x xs w' w'' e1 e1a w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs w' w'' e1 e1a w1)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xs e1 e1a l r la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac x xs e1 e1a l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac x xs e1 e1a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 e1a r la ra l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac x xs e1 e1a r la ra l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac x xs e1 e1a r la ra l')(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 e1a r ra l' l'a)(*strict*)
  apply(subgoal_tac "\<alpha>@l'a=l'")
   apply(rename_tac x xs e1 e1a r ra l' l'a)(*strict*)
   prefer 2
   apply (metis append_Nil2 maximalPrefixB_drop_liftB maximalPrefixB_front)
  apply(rename_tac x xs e1 e1a r ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs e1 e1a r ra l'a)(*strict*)
  apply(subgoal_tac "teA (prod_lhs x) # ra @ y = teA (prod_lhs x) # r")
   apply(rename_tac x xs e1 e1a r ra l'a)(*strict*)
   prefer 2
   apply (metis liftB_commutes_over_concat append_Cons append_linj concat_asso prefix_def)
  apply(rename_tac x xs e1 e1a r ra l'a)(*strict*)
  apply(clarsimp)
  done

lemma existence_of_realizable: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c1 \<pi> c2
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> 0<length \<pi>
  \<Longrightarrow> \<exists>\<pi>'. \<exists>c.
  prefix \<pi>' \<pi>
  \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=[teA (prod_lhs(hd \<pi>))]\<rparr> \<pi>' c)
  \<and> (setA (cfg_conf c)={} \<or> \<pi>'=\<pi>)"
  apply(induct \<pi> arbitrary: d c2 rule: length_induct)
  apply(rename_tac xs d c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "xs=[] \<or> (\<exists>w' a'. SSc=w'@[a'])" for SSc)
   apply(rename_tac xs d c2)(*strict*)
   prefer 2
   apply(rule case_list)
  apply(rename_tac xs d c2)(*strict*)
  apply(erule disjE)
   apply(rename_tac xs d c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac xs d c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c2 w' a')(*strict*)
  apply(erule_tac
      x="w'"
      and P="\<lambda>ys. length ys < Suc (length w') \<longrightarrow> (\<exists>x. Ex (cfgLMTD G x c1 ys)) \<longrightarrow> set ys \<subseteq> cfg_productions G \<longrightarrow> ys \<noteq> [] \<longrightarrow> (\<exists>\<pi>'. \<pi>' \<sqsubseteq> ys \<and> (\<exists>c. (\<exists>d. cfgLMTD G d \<lparr>cfg_conf = [teA (prod_lhs (hd ys))]\<rparr> \<pi>' c) \<and> (setA (cfg_conf c) = {} \<or> \<pi>' = ys)))"
      in allE)
  apply(rename_tac d c2 w' a')(*strict*)
  apply(clarsimp)
  apply(case_tac w')
   apply(rename_tac d c2 w' a')(*strict*)
   apply(clarsimp)
   apply(rename_tac d c2 a')(*strict*)
   apply(erule_tac
      x="[a']"
      in allE)
   apply(simp add: prefix_def)
   apply(erule_tac
      x="\<lparr>cfg_conf = prod_rhs a'\<rparr>"
      in allE)
   apply(erule_tac
      x="der2 \<lparr>cfg_conf = [teA (prod_lhs a')]\<rparr> a' \<lparr>cfg_conf = prod_rhs a'\<rparr>"
      in allE)
   apply(subgoal_tac "cfgLM.trans_der G (der2 \<lparr>cfg_conf = [teA (prod_lhs a')]\<rparr> a' \<lparr>cfg_conf = prod_rhs a'\<rparr>) \<lparr>cfg_conf = [teA (prod_lhs a')]\<rparr> [a'] \<lparr>cfg_conf = prod_rhs a'\<rparr>")
    apply(rename_tac d c2 a')(*strict*)
    prefer 2
    apply(rule cfgLM.trans_der_der2)
      apply(rename_tac d c2 a')(*strict*)
      apply(force)
     apply(rename_tac d c2 a')(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: valid_cfg_def)
    apply(rename_tac d c2 a')(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac d c2 a')(*strict*)
   apply(force)
  apply(rename_tac d c2 w' a' a list)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (length w') = Some (pair e c)")
   apply(rename_tac d c2 w' a' a list)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d c2 w' a' a list e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc (length w')"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac d c2 w' a' a list e)(*strict*)
     apply(force)
    apply(rename_tac d c2 w' a' a list e)(*strict*)
    apply(force)
   apply(rename_tac d c2 w' a' a list e)(*strict*)
   apply(force)
  apply(rename_tac d c2 w' a' a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c2 a' a list e c)(*strict*)
  apply(subgoal_tac "cfgLM_step_relation G c a' c2")
   apply(rename_tac d c2 a' a list e c)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length(a#list)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac d c2 a' a list e c)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac d c2 a' a list e c ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="Suc(length(a#list))"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac d c2 a' a list e c ea)(*strict*)
      apply(force)
     apply(rename_tac d c2 a' a list e c ea)(*strict*)
     apply(force)
    apply(rename_tac d c2 a' a list e c ea)(*strict*)
    apply(force)
   apply(rename_tac d c2 a' a list e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
   apply(rule_tac
      t="c2"
      and s="c2a"
      in ssubst)
    apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac d c2 a' a list e c e2 c2a ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(force)
   apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
   apply(subgoal_tac "e2=a'")
    apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
    apply(force)
   apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
   apply(rule cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
       apply(force)
      apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
      apply(force)
     apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
     apply(force)
    apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
    apply(force)
   apply(rename_tac d c2 a' a list e c e2 c2a)(*strict*)
   apply(force)
  apply(rename_tac d c2 a' a list e c)(*strict*)
  apply(erule impE)
   apply(rename_tac d c2 a' a list e c)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac d c2 a' a list e c)(*strict*)
    apply(force)
   apply(rename_tac d c2 a' a list e c)(*strict*)
   apply(force)
  apply(rename_tac d c2 a' a list e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c2 a' a list e c \<pi>' ca da)(*strict*)
  apply(case_tac "setA (cfg_conf ca) = {}")
   apply(rename_tac d c2 a' a list e c \<pi>' ca da)(*strict*)
   apply(erule_tac
      x="\<pi>'"
      in allE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac d c2 a' a list e c \<pi>' ca da cb)(*strict*)
   apply(erule impE)
    apply(rename_tac d c2 a' a list e c \<pi>' ca da cb)(*strict*)
    apply(rule_tac
      x="cb@[a']"
      in exI)
    apply(force)
   apply(rename_tac d c2 a' a list e c \<pi>' ca da cb)(*strict*)
   apply(erule_tac
      x="ca"
      in allE)
   apply(clarsimp)
  apply(rename_tac d c2 a' a list e c \<pi>' ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c2 a' a list e c ca da)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac d c2 a' a list e c ca da)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac d c2 a' a list e c ca da ea eb)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc(length(a#list))"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac d c2 a' a list e c ca da ea eb)(*strict*)
     apply(force)
    apply(rename_tac d c2 a' a list e c ca da ea eb)(*strict*)
    apply(force)
   apply(rename_tac d c2 a' a list e c ca da ea eb)(*strict*)
   apply(force)
  apply(rename_tac d c2 a' a list e c ca da)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c2 a' a list e c ca da e1 e2 c1a c2a)(*strict*)
  apply(subgoal_tac "e2=a")
   apply(rename_tac d c2 a' a list e c ca da e1 e2 c1a c2a)(*strict*)
   prefer 2
   apply(rule cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac d c2 a' a list e c ca da e1 e2 c1a c2a)(*strict*)
       apply(force)
      apply(rename_tac d c2 a' a list e c ca da e1 e2 c1a c2a)(*strict*)
      apply(force)
     apply(rename_tac d c2 a' a list e c ca da e1 e2 c1a c2a)(*strict*)
     apply(force)
    apply(rename_tac d c2 a' a list e c ca da e1 e2 c1a c2a)(*strict*)
    apply(force)
   apply(rename_tac d c2 a' a list e c ca da e1 e2 c1a c2a)(*strict*)
   apply(force)
  apply(rename_tac d c2 a' a list e c ca da e1 e2 c1a c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a l la r ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a l la r ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a l la r ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a la r ra l')(*strict*)
  apply(case_tac c)
  apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a la r ra l' cfg_confa)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a la r ra l' cfg_confa cfg_confaa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a la r ra l' cfg_confa cfg_confaa cfg_confb)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac d c2 a' a list e c ca da e1 c1a c2a la r ra l' cfg_confa cfg_confaa cfg_confb cfg_confc)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a' a list e ca da e1 la r ra l')(*strict*)
  apply(case_tac ca)
  apply(rename_tac d a' a list e ca da e1 la r ra l' cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a' a list e da e1 la r ra l' cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac d a' a list e da e1 la r ra l' w)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac d a' a list e da e1 la r ra l' w)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac d a' a list e da e1 la r ra l' w)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a' a list e da e1 r ra l' w l'a)(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(subgoal_tac "\<exists>w1 w2 A. SSw = liftB w1 @ teA A # w2" for SSw)
   apply(rename_tac d a' a list e da e1 r ra l' w l'a)(*strict*)
   prefer 2
   apply(rule left_most_terminal_exists)
   apply(force)
  apply(rename_tac d a' a list e da e1 r ra l' w l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
  apply(simp add: setAConcat)
  apply(thin_tac "(a # list) \<sqsubseteq> (a # list)")
  apply(subgoal_tac "liftB l'a @ (liftB w1 @ teA A # w2) @ ra = liftB l' @ teA (prod_lhs a') # r")
   apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="da"
      and ?d2.0="d"
      and w'="liftB w1 @ teA A # w2"
      in cfgLM_trans_der_coincide_up_to_unused_context)
     apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
     apply(force)
    apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
    apply(force)
   apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(rule_tac
      m="Suc 0"
      in get_labels_drop_tail)
    apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
    apply(force)
   apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
   apply(force)
  apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "l'=l'a@w1")
   apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
   prefer 2
   apply (metis liftB_commutes_over_concat append_assoc identical_temrinal_maximal_prefix)
  apply(rename_tac d a' a list e da e1 r ra l' l'a w1 w2 A)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a' a list e da e1 r ra l'a w1 w2 A)(*strict*)
  apply(subgoal_tac "teA A # w2 @ ra = teA (prod_lhs a') # r")
   apply(rename_tac d a' a list e da e1 r ra l'a w1 w2 A)(*strict*)
   prefer 2
   apply (metis liftB_commutes_over_concat append_Cons append_linj concat_asso prefix_def)
  apply(rename_tac d a' a list e da e1 r ra l'a w1 w2 A)(*strict*)
  apply(clarsimp)
  apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
  apply(thin_tac "liftB l'a @ liftB w1 = liftB (l'a @ w1)")
  apply(erule_tac
      x="(a # list @ [a'])"
      in allE)
  apply(clarsimp)
  apply(simp add: prefix_def)
  apply(erule_tac
      x="\<lparr>cfg_conf = liftB w1 @ (prod_rhs a') @ w2\<rparr>"
      in allE)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      c="\<lparr>cfg_conf=[teA (prod_lhs a')]\<rparr>"
      and e="a'"
      and c'="\<lparr>cfg_conf=(prod_rhs a')\<rparr>"
      in cfgLM.trans_der_der2)
     apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
     apply(force)
    apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
    apply(simp add: valid_cfg_def cfg_configurations_def)
   apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="da"
      and ?d2.0="der2 \<lparr>cfg_conf = [teA (prod_lhs a')]\<rparr> a' \<lparr>cfg_conf = prod_rhs a'\<rparr>"
      and ?w1.0="[teA (prod_lhs a)]"
      and ?v2.0="[teA (prod_lhs a')]"
      and ?\<pi>1.0="a#list"
      and ?v1.0="w1"
      and ?v4.0="w2"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
     apply(force)
    apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
    apply(force)
   apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
   apply(force)
  apply(rename_tac d a' a list e da e1 ra l'a w1 w2)(*strict*)
  apply(clarsimp)
  done

lemma cfgLM_trans_der_equal_position: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 c (\<pi>@\<pi>1) c1
  \<Longrightarrow> cfgLM.trans_der G d2 c (\<pi>@\<pi>2) c2
  \<Longrightarrow> d1 (length \<pi>) = d2 (length \<pi>)"
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e ea)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 (length \<pi>) = Some (pair e c)")
   apply(rename_tac e ea)(*strict*)
   prefer 2
   apply(rule_tac
      m="length(\<pi>@\<pi>1)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 (length \<pi>) = Some (pair e c)")
   apply(rename_tac e ea)(*strict*)
   prefer 2
   apply(rule_tac
      m="length(\<pi>@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(rename_tac e ea)(*strict*)
  apply(erule exE)+
  apply(rename_tac e ea eb ec ca caa)(*strict*)
  apply(rule_tac
      ?n2.0="length(\<pi>)"
      in cfgLM_equal_positions_when_same_productions)
         apply(rename_tac e ea eb ec ca caa)(*strict*)
         apply(force)
        apply(rename_tac e ea eb ec ca caa)(*strict*)
        apply(force)
       apply(rename_tac e ea eb ec ca caa)(*strict*)
       apply(force)
      apply(rename_tac e ea eb ec ca caa)(*strict*)
      apply(force)
     apply(rename_tac e ea eb ec ca caa)(*strict*)
     apply(force)
    apply(rename_tac e ea eb ec ca caa)(*strict*)
    apply(force)
   apply(rename_tac e ea eb ec ca caa)(*strict*)
   apply(rule_tac
      t="map the (get_labels d1 (length \<pi>))"
      and s="\<pi>"
      in ssubst)
    apply(rename_tac e ea eb ec ca caa)(*strict*)
    apply(rule_tac
      t="get_labels d1 (length \<pi>)"
      and s="map Some \<pi>"
      in ssubst)
     apply(rename_tac e ea eb ec ca caa)(*strict*)
     apply(rule_tac
      m="length \<pi>1"
      in get_labels_drop_tail)
      apply(rename_tac e ea eb ec ca caa)(*strict*)
      apply(force)
     apply(rename_tac e ea eb ec ca caa)(*strict*)
     apply(force)
    apply(rename_tac e ea eb ec ca caa)(*strict*)
    apply(rule listEqI)
     apply(rename_tac e ea eb ec ca caa)(*strict*)
     apply(force)
    apply(rename_tac e ea eb ec ca caa i)(*strict*)
    apply(force)
   apply(rename_tac e ea eb ec ca caa)(*strict*)
   apply(rule sym)
   apply(rule_tac
      t="get_labels d2 (length \<pi>)"
      and s="map Some \<pi>"
      in ssubst)
    apply(rename_tac e ea eb ec ca caa)(*strict*)
    apply(rule_tac
      m="length \<pi>2"
      in get_labels_drop_tail)
     apply(rename_tac e ea eb ec ca caa)(*strict*)
     apply(force)
    apply(rename_tac e ea eb ec ca caa)(*strict*)
    apply(force)
   apply(rename_tac e ea eb ec ca caa)(*strict*)
   apply(rule listEqI)
    apply(rename_tac e ea eb ec ca caa)(*strict*)
    apply(force)
   apply(rename_tac e ea eb ec ca caa i)(*strict*)
   apply(force)
  apply(rename_tac e ea eb ec ca caa)(*strict*)
  apply(force)
  done

lemma unique_existence_of_realizable_hlp: "
       valid_cfg G
  \<Longrightarrow> \<pi>1 \<sqsubseteq> \<pi>
  \<Longrightarrow> \<pi>2 \<sqsubseteq> \<pi>
  \<Longrightarrow> setA (cfg_conf cx1) = {} \<or> \<pi>1 = \<pi>
  \<Longrightarrow> cfgLM.trans_der G dx1 \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>1 cx1
  \<Longrightarrow> cfgLM.trans_der G dx2 \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>))]\<rparr> \<pi>2 cx2
  \<Longrightarrow> length \<pi>1 < length \<pi>2
  \<Longrightarrow> \<pi>1 = \<pi>2"
  apply(subgoal_tac "strict_prefix \<pi>1 \<pi>2")
   prefer 2
   apply (metis append_Nil2 less_irrefl_nat less_or_eq_imp_le prefix_common_max prefix_def strict_prefix_def)
  apply(simp add: prefix_def strict_prefix_def)
  apply(clarsimp)
  apply(rename_tac ca cb)(*strict*)
  apply(case_tac cb)
   apply(rename_tac ca cb)(*strict*)
   apply(force)
  apply(rename_tac ca cb a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca a list)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dx2 (length (\<pi>1)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac ca a list)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac ca a list e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length((\<pi>1 @ a # list))"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac ca a list e ea)(*strict*)
     apply(force)
    apply(rename_tac ca a list e ea)(*strict*)
    apply(force)
   apply(rename_tac ca a list e ea)(*strict*)
   apply(force)
  apply(rename_tac ca a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca a list e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac ca a list e1 e2 c1 c2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac ca a list e1 e2 c1 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca a list e1 e2 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac ca a list e1 e2 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca a list e1 e2 l r)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac ca a list e1 e2 l r)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac ca a list e1 e2 l r)(*strict*)
  apply(clarsimp)
  apply(rename_tac ca a list e1 e2 r l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "e2=a")
   apply(rename_tac ca a list e1 e2 r l')(*strict*)
   prefer 2
   apply(rule_tac
      d="dx2"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac ca a list e1 e2 r l')(*strict*)
       apply(force)
      apply(rename_tac ca a list e1 e2 r l')(*strict*)
      apply(force)
     apply(rename_tac ca a list e1 e2 r l')(*strict*)
     apply(force)
    apply(rename_tac ca a list e1 e2 r l')(*strict*)
    apply(force)
   apply(rename_tac ca a list e1 e2 r l')(*strict*)
   apply(force)
  apply(rename_tac ca a list e1 e2 r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac ca a list e1 r l')(*strict*)
  apply(subgoal_tac "dx1 (length \<pi>1) = dx2 (length \<pi>1)")
   apply(rename_tac ca a list e1 r l')(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac ca a list e1 r l' e)(*strict*)
   apply(simp add: setAConcat)
  apply(rename_tac ca a list e1 r l')(*strict*)
  apply(rule_tac
      ?\<pi>1.0="[]"
      in cfgLM_trans_der_equal_position)
    apply(rename_tac ca a list e1 r l')(*strict*)
    apply(force)
   apply(rename_tac ca a list e1 r l')(*strict*)
   apply(force)
  apply(rename_tac ca a list e1 r l')(*strict*)
  apply(force)
  done

lemma unique_existence_of_realizable: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c1 \<pi> c2
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G
  \<Longrightarrow> 0<length \<pi>
  \<Longrightarrow> \<exists>!\<pi>'. \<exists>c.
  prefix \<pi>' \<pi>
  \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=[teA (prod_lhs(hd \<pi>))]\<rparr> \<pi>' c)
  \<and> (setA (cfg_conf c)={} \<or> \<pi>'=\<pi>)"
  apply(rule ex_ex1I)
   apply(rule existence_of_realizable)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac \<pi>' y)(*strict*)
  apply(clarsimp)
  apply(rename_tac \<pi>' y c ca da daa)(*strict*)
  apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)
  apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
  apply(case_tac "length \<pi>1 = length \<pi>2")
   apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
   apply (metis order_refl mutual_prefix_implies_equality2 prefix_common_max)
  apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
  apply(case_tac "length \<pi>1<length \<pi>2")
   apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
   apply(rule unique_existence_of_realizable_hlp)
         apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
         apply(force)
        apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
  apply(rule sym)
  apply(rule unique_existence_of_realizable_hlp)
        apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
        apply(force)
       apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
       apply(force)
      apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
      apply(force)
     apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
     apply(force)
    apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
    apply(force)
   apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
   apply(force)
  apply(rename_tac \<pi>1 \<pi>2 cx1 cx2 dx1 dx2)(*strict*)
  apply(force)
  done

lemma unique_existence_of_realizable_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c1 (\<pi>1@\<pi>@\<pi>2) c2
  \<Longrightarrow> 0<length \<pi>
  \<Longrightarrow> \<exists>!\<pi>'. \<exists>c.
  prefix \<pi>' \<pi>
  \<and> (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=[teA (prod_lhs(hd \<pi>))]\<rparr> \<pi>' c)
  \<and> (setA (cfg_conf c)={} \<or> \<pi>'=\<pi>)"
  apply(subgoal_tac "\<exists>e c. d (length \<pi>1) = Some (pair e c)")
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(\<pi>1@\<pi>@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(subgoal_tac "\<exists>e c. d (length (\<pi>1@\<pi>)) = Some (pair e c)")
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e ea c)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(\<pi>1@\<pi>@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac e ea c)(*strict*)
     apply(force)
    apply(rename_tac e ea c)(*strict*)
    apply(force)
   apply(rename_tac e ea c)(*strict*)
   apply(force)
  apply(erule exE)+
  apply(rename_tac e ea c ca)(*strict*)
  apply(subgoal_tac "\<exists>d. cfgLM.trans_der SSG d SSci SSrenPIprime SScj" for SSG SSci SSrenPIprime SScj)
   apply(rename_tac e ea c ca)(*strict*)
   prefer 2
   apply(rule_tac
      i="length \<pi>1"
      and j="length (\<pi>1@\<pi>)"
      in cfgLM.trans_der_slice)
         apply(rename_tac e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac e ea c ca)(*strict*)
        apply(force)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca)(*strict*)
    apply(force)
   apply(rename_tac e ea c ca)(*strict*)
   apply(force)
  apply(rename_tac e ea c ca)(*strict*)
  apply(erule exE)+
  apply(rename_tac e ea c ca da)(*strict*)
  apply(rule_tac
      ?c1.0="c"
      and ?c2.0="ca"
      and d="da"
      in unique_existence_of_realizable)
     apply(rename_tac e ea c ca da)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca da)(*strict*)
    apply(force)
   apply(rename_tac e ea c ca da)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea c ca da x)(*strict*)
   apply(rule_tac
      t="cfg_productions G"
      and s="cfg_step_labels G"
      in ssubst)
    apply(rename_tac e ea c ca da x)(*strict*)
    apply(simp add: cfg_step_labels_def)
   apply(rename_tac e ea c ca da x)(*strict*)
   apply(rule cfgLM.trans_der_step_labels)
     apply(rename_tac e ea c ca da x)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca da x)(*strict*)
    apply(force)
   apply(rename_tac e ea c ca da x)(*strict*)
   apply(force)
  apply(rename_tac e ea c ca da)(*strict*)
  apply(force)
  done

lemma cfgLM_unique_final_conf: "
  valid_cfg G
  \<Longrightarrow> \<exists>c. \<exists>d. cfgLM.trans_der
  G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia \<pi>)))]\<rparr> x c
  \<Longrightarrow> \<exists>!c. \<exists>d. cfgLM.trans_der
                    G d \<lparr>cfg_conf = [teA (prod_lhs (hd (drop ia \<pi>)))]\<rparr> x c"
  apply(clarsimp)
  apply(rename_tac c d)(*strict*)
  apply(rule ex1I)
   apply(rename_tac c d)(*strict*)
   apply(force)
  apply(rename_tac c d ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac c d ca da)(*strict*)
  apply(subgoal_tac "d (length x)=da(length x)")
   apply(rename_tac c d ca da)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(force)
  apply(rename_tac c d ca da)(*strict*)
  apply(rule_tac
      ?\<pi>1.0="[]"
      and ?\<pi>2.0="[]"
      in cfgLM_trans_der_equal_position)
    apply(rename_tac c d ca da)(*strict*)
    apply(force)
   apply(rename_tac c d ca da)(*strict*)
   apply(force)
  apply(rename_tac c d ca da)(*strict*)
  apply(force)
  done

lemma local_combine: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf=liftB \<alpha>@w@wx\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w\<rparr> \<pi>1 \<lparr>cfg_conf=w'@w1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d' \<lparr>cfg_conf=w'\<rparr> \<pi>' \<lparr>cfg_conf=liftB \<alpha>'\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d1' \<lparr>cfg_conf=liftB (\<alpha>@\<alpha>')@w1@wx\<rparr> \<pi>1' \<lparr>cfg_conf=liftB \<beta>\<rparr>
  \<Longrightarrow> \<exists>dX. cfgLM.trans_der G dX \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> (\<pi>@\<pi>1@\<pi>'@\<pi>1') \<lparr>cfg_conf=liftB \<beta>\<rparr>"
  apply(subgoal_tac "\<exists>dX. cfgLM.trans_der G dX \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> (\<pi>@\<pi>1) \<lparr>cfg_conf=liftB \<alpha>@(w'@w1)@wx\<rparr>")
   prefer 2
   apply(rule_tac
      ?v4.0="wx"
      and ?v2.0="w"
      and ?d1.0="d"
      and ?d2.0="d1"
      in cfgLM_trans_der_concat_extend_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf = liftB \<alpha> @ w@wx\<rparr>")
  apply(thin_tac "cfgLM.trans_der G d1 \<lparr>cfg_conf = w\<rparr> \<pi>1 \<lparr>cfg_conf = w' @ w1\<rparr>")
  apply(clarsimp)
  apply(rename_tac dX)(*strict*)
  apply(subgoal_tac "\<exists>dX. cfgLM.trans_der G dX \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> ((\<pi>@\<pi>1)@\<pi>') \<lparr>cfg_conf=liftB \<alpha>@liftB \<alpha>'@w1@wx\<rparr>")
   apply(rename_tac dX)(*strict*)
   prefer 2
   apply(rule_tac
      ?v4.0="w1@wx"
      and ?v2.0="w'"
      and ?d1.0="dX"
      and ?d2.0="d'"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac dX)(*strict*)
     apply(force)
    apply(rename_tac dX)(*strict*)
    apply(force)
   apply(rename_tac dX)(*strict*)
   apply(force)
  apply(rename_tac dX)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d' \<lparr>cfg_conf = w'\<rparr> \<pi>' \<lparr>cfg_conf = liftB \<alpha>'\<rparr>")
  apply(rename_tac dX)(*strict*)
  apply(thin_tac "cfgLM.trans_der G dX \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> (\<pi> @ \<pi>1) \<lparr>cfg_conf = liftB \<alpha> @ w' @ w1@wx\<rparr>")
  apply(rename_tac dX)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="\<pi> @ \<pi>1 @ \<pi>' @ \<pi>1'"
      and s="(\<pi> @ \<pi>1 @ \<pi>') @ \<pi>1'"
      in ssubst)
   apply(rename_tac dX)(*strict*)
   apply(force)
  apply(rename_tac dX)(*strict*)
  apply(rule_tac
      t="liftB \<beta>"
      and s="liftB[] @ liftB \<beta>@[]"
      in ssubst)
   apply(rename_tac dX)(*strict*)
   apply(force)
  apply(rename_tac dX)(*strict*)
  apply(rule_tac
      ?v4.0="[]"
      and ?v1.0="[]"
      and ?d1.0="dX"
      and ?d2.0="d1'"
      in cfgLM_trans_der_concat_extend_prime)
    apply(rename_tac dX)(*strict*)
    apply(force)
   apply(rename_tac dX)(*strict*)
   apply(force)
  apply(rename_tac dX)(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  apply(force)
  done

lemma mutual_prefixing_of_in_between_derivations: "
  valid_cfg G
  \<Longrightarrow> CFGlm_unambiguous G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf=liftB \<alpha>@w@wx\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w\<rparr> \<pi>1 \<lparr>cfg_conf=w'@w1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=w\<rparr> \<pi>2 \<lparr>cfg_conf=w'@w2\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d' \<lparr>cfg_conf=w'\<rparr> \<pi>' \<lparr>cfg_conf=liftB \<alpha>'\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d1' \<lparr>cfg_conf=liftB (\<alpha>@\<alpha>')@w1@wx\<rparr> \<pi>1' \<lparr>cfg_conf=liftB \<beta>\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2' \<lparr>cfg_conf=liftB (\<alpha>@\<alpha>')@w2@wx\<rparr> \<pi>2' \<lparr>cfg_conf=liftB \<beta>\<rparr>
  \<Longrightarrow> prefix \<pi>1 \<pi>2 \<or> prefix \<pi>2 \<pi>1"
  apply(rule_tac
      w="\<pi>"
      and w'="\<pi>'"
      and ?v1'.0="\<pi>1'"
      and ?v2'.0="\<pi>2'"
      in mutual_prefix_prefix_with_left_context)
  apply(subgoal_tac "\<exists>dX. cfgLM.trans_der G dX \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> (\<pi>@\<pi>1@\<pi>'@\<pi>1') \<lparr>cfg_conf=liftB \<beta>\<rparr>")
   prefer 2
   apply(rule local_combine)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>dX. cfgLM.trans_der G dX \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> (\<pi>@\<pi>2@\<pi>'@\<pi>2') \<lparr>cfg_conf=liftB \<beta>\<rparr>")
   prefer 2
   apply(rule local_combine)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr> \<pi> \<lparr>cfg_conf=liftB \<alpha>@w@wx\<rparr>")
  apply(thin_tac "cfgLM.trans_der G d1 \<lparr>cfg_conf=w\<rparr> \<pi>1 \<lparr>cfg_conf=w'@w1\<rparr>")
  apply(thin_tac "cfgLM.trans_der G d2 \<lparr>cfg_conf=w\<rparr> \<pi>2 \<lparr>cfg_conf=w'@w2\<rparr>")
  apply(thin_tac "cfgLM.trans_der G d' \<lparr>cfg_conf=w'\<rparr> \<pi>' \<lparr>cfg_conf=liftB \<alpha>'\<rparr>")
  apply(thin_tac "cfgLM.trans_der G d1' \<lparr>cfg_conf=liftB (\<alpha>@\<alpha>')@w1@wx\<rparr> \<pi>1' \<lparr>cfg_conf=liftB \<beta>\<rparr>")
  apply(thin_tac "cfgLM.trans_der G d2' \<lparr>cfg_conf=liftB (\<alpha>@\<alpha>')@w2@wx\<rparr> \<pi>2' \<lparr>cfg_conf=liftB \<beta>\<rparr>")
  apply(simp add: CFGlm_unambiguous_def)
  apply(clarsimp)
  apply(rename_tac dX dXa)(*strict*)
  apply(rename_tac d1 d2)
  apply(rename_tac d1 d2)(*strict*)
  apply(erule_tac
      x="d1"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(simp add: cfgLM.trans_der_def)
   apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac d1 d2)(*strict*)
  apply(erule_tac
      x="d2"
      in allE)
  apply(erule impE)
   apply(rename_tac d1 d2)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(simp add: cfgLM.trans_der_def)
   apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(rename_tac d1 d2)(*strict*)
  apply(erule_tac
      x="length ((\<pi> @ \<pi>1 @ \<pi>' @ \<pi>1'))"
      in allE)
  apply(erule_tac
      x="length ((\<pi> @ \<pi>2 @ \<pi>' @ \<pi>2'))"
      in allE)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac d1 d2 e ea)(*strict*)
  apply(erule impE)
   apply(rename_tac d1 d2 e ea)(*strict*)
   apply(rule_tac
      x="\<beta>"
      in exI)
   apply (simp only: liftB_commutes_over_concat)
  apply(rename_tac d1 d2 e ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac d2 e ea)(*strict*)
  apply(subgoal_tac "(length \<pi> + (length \<pi>2 + (length \<pi>' + length \<pi>2')))=(length \<pi> + (length \<pi>1 + (length \<pi>' + length \<pi>1')))")
   apply(rename_tac d2 e ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac d2 ea)(*strict*)
   apply(rule Some_map_inj)
   apply(simp add: map_append)
  apply(rename_tac d2 e ea)(*strict*)
  apply(rule_tac
      ?w2.0="\<beta>"
      and ?w1.0="\<beta>"
      and ?e1.0="ea"
      and ?e2.0="e"
      and d="d2"
      in cfgLM_unique_terminal_configurations)
     apply(rename_tac d2 e ea)(*strict*)
     apply(force)
    apply(rename_tac d2 e ea)(*strict*)
    apply(force)
   apply(rename_tac d2 e ea)(*strict*)
   apply (simp only: liftB_commutes_over_concat)
  apply(rename_tac d2 e ea)(*strict*)
  apply (simp only: liftB_commutes_over_concat)
  done

lemma cfgLM_derivation_drop: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c0 (\<pi>1@\<pi>2) cn
  \<Longrightarrow> cfgLM.trans_der G d c0 (\<pi>1) ci
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d ci \<pi>2 cn"
  apply(subgoal_tac "\<exists>e. d (length \<pi>1) = Some (pair e ci)")
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule_tac
      n="length \<pi>1"
      and d="d"
      in cfgLM.trans_der_skip_prime)
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

lemma cfgLM_drop_terminal_prefix: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=liftB \<alpha>@v\<rparr> \<pi> \<lparr>cfg_conf=liftB \<alpha>@w\<rparr>
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=v\<rparr> \<pi> \<lparr>cfg_conf=w\<rparr>"
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "\<exists>d'. cfgLM.derivation SSG d' \<and> get_labels d' SSn = get_labels SSd SSn \<and> d' 0 = Some (pair None \<lparr>cfg_conf = SSv0\<rparr>) \<and> d' SSn = Some (pair SSe \<lparr>cfg_conf = SSv1\<rparr>)" for SSG SSd SSv0 SSn SSe SSv1)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rule_tac
      n="length \<pi>"
      in cfgLM_left_context_can_be_dropped)
      apply(rename_tac e)(*strict*)
      apply(force)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rename_tac e d')(*strict*)
  apply(rule_tac
      x="d'"
      in exI)
  apply(clarsimp)
  apply(rule cfgLM.derivation_belongs)
     apply(rename_tac e d')(*strict*)
     apply(force)
    apply(rename_tac e d')(*strict*)
    apply(force)
   apply(rename_tac e d')(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf = liftB \<alpha>@v\<rparr> \<in> cfg_configurations G")
    apply(rename_tac e d')(*strict*)
    apply(simp add: cfg_configurations_def)
    apply(simp add: setAConcat)
    apply(simp add: setBConcat)
   apply(rename_tac e d')(*strict*)
   apply(rule cfgLM.belongs_configurations)
    apply(rename_tac e d')(*strict*)
    apply(force)
   apply(rename_tac e d')(*strict*)
   apply(force)
  apply(rename_tac e d')(*strict*)
  apply(force)
  done

lemma cfgLM_trans_der_drop_leading_terminals: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=liftB \<alpha>@w1\<rparr> \<pi> \<lparr>cfg_conf=liftB \<alpha>@w2\<rparr>
  \<Longrightarrow> cfgLM.trans_der G (derivation_map (derivation_take d (length \<pi>)) (\<lambda>c. \<lparr>cfg_conf=drop(length \<alpha>)(cfg_conf c)\<rparr>)) \<lparr>cfg_conf=w1\<rparr> \<pi> \<lparr>cfg_conf=w2\<rparr>"
  apply(simp add: cfgLM.trans_der_def)
  apply(rule context_conjI)
   apply(rule_tac
      P="\<lambda>c. \<exists>w. cfg_conf c=liftB \<alpha>@w "
      in cfgLM.derivation_map_preserves_derivation)
     apply(rule cfgLM.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e c ea)(*strict*)
    apply(simp add: derivation_take_def)
    apply(case_tac "i\<le>(length \<pi>)")
     apply(rename_tac i e c ea)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac i e c ea)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
     apply(rename_tac c e i ea)(*strict*)
     prefer 2
     apply(rename_tac i e c ea)(*strict*)
     apply(rule_tac
      d="d"
      and i="0"
      and j="i"
      in cfgLM.derivation_monotonically_inc)
          apply(rename_tac i e c ea)(*strict*)
          apply(force)
         apply(rename_tac i e c ea)(*strict*)
         apply(force)
        apply(rename_tac i e c ea)(*strict*)
        apply(force)
       apply(rename_tac i e c ea)(*strict*)
       apply(force)
      apply(rename_tac i e c ea)(*strict*)
      apply(force)
     apply(rename_tac i e c ea)(*strict*)
     apply(force)
    apply(rename_tac i e c ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e c ea w)(*strict*)
    apply(simp add: cfg_get_history_def)
    apply(case_tac c)
    apply(rename_tac i e c ea w cfg_confa)(*strict*)
    apply(rename_tac v)
    apply(rename_tac i e c ea w v)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e ea w v)(*strict*)
    apply(subgoal_tac "prefix (liftB \<alpha>) v")
     apply(rename_tac i e ea w v)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
    apply(rename_tac e i ea w v)(*strict*)
    apply (metis concat_asso maxTermPrefix_shift prefix_of_maxTermPrefix_is_terminal_string_prefix)
   apply(rename_tac c1 e c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a e b ea w wa)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac a e b ea w wa l r)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac a e b ea w wa l r)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_substring setA_substring_prime)
   apply(rename_tac a e b ea w wa l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac a e b ea w wa r l')(*strict*)
   apply(case_tac a)
   apply(rename_tac a e b ea w wa r l' cfg_confa)(*strict*)
   apply(case_tac b)
   apply(rename_tac a e b ea w wa r l' cfg_confa cfg_confaa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea w wa r l')(*strict*)
   apply(thin_tac "setA (liftB l') = {}")
   apply(subgoal_tac "length (liftB \<alpha>) = length \<alpha>")
    apply(rename_tac e ea w wa r l')(*strict*)
    apply(rule_tac
      t="length (liftB \<alpha>)"
      and s="length \<alpha>"
      in ssubst)
     apply(rename_tac e ea w wa r l')(*strict*)
     apply(force)
    apply(rename_tac e ea w wa r l')(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "prefix \<alpha> l'")
     apply(rename_tac e ea w wa r l')(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac e ea w wa r c)(*strict*)
     apply(simp add: liftB_commutes_over_concat)
     apply(clarsimp)
     apply(rename_tac e ea r c)(*strict*)
     apply(rule_tac
      x="liftB c"
      in exI)
     apply(clarsimp)
     apply(rename_tac e ea c)(*strict*)
     apply (metis setA_liftB)
    apply(rename_tac e ea w wa r l')(*strict*)
    apply (metis hlpX)
   apply(rename_tac e ea w wa r l')(*strict*)
   apply (metis liftB_reflects_length)
  apply(rule conjI)
   apply(rule cfgLM.derivation_belongs)
      apply(force)
     apply(simp add: derivation_map_def derivation_take_def)
    apply(clarsimp)
    apply(rename_tac e)(*strict*)
    apply(rule_tac
      t="length (liftB \<alpha>)"
      and s="length \<alpha>"
      in ssubst)
     apply(rename_tac e)(*strict*)
     apply (metis liftB_reflects_length)
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="drop (length \<alpha>) (liftB \<alpha>)"
      and s="[]"
      in ssubst)
     apply(rename_tac e)(*strict*)
     apply (metis liftB_reflects_length drop_eq_Nil le_refl)
    apply(rename_tac e)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<lparr>cfg_conf = liftB \<alpha> @ w1\<rparr> \<in> cfg_configurations G")
     apply(rename_tac e)(*strict*)
     apply(simp add: cfg_configurations_def)
     apply(simp add: setAConcat)
     apply(simp add: setBConcat)
    apply(rename_tac e)(*strict*)
    apply(rule cfgLM.belongs_configurations)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(force)
  apply(rule conjI)
   apply(rule_tac
      t="get_labels (derivation_map (derivation_take d (length \<pi>)) (\<lambda>c. \<lparr>cfg_conf = drop (length \<alpha>) (cfg_conf c)\<rparr>)) (length \<pi>)"
      and s="get_labels ((derivation_take d (length \<pi>))) (length \<pi>)"
      in ssubst)
    apply(rule get_labels_derivation_map)
   apply(rule_tac
      t="get_labels (derivation_take d (length \<pi>)) (length \<pi>)"
      and s="get_labels d (length \<pi>)"
      in subst)
    apply(rule cfgLM.get_labels_derivation_take)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: derivation_map_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule_tac
      t="drop (length \<alpha>) (liftB \<alpha>)"
      and s="[]"
      in ssubst)
   apply(rename_tac e)(*strict*)
   apply (metis liftB_reflects_length drop_eq_Nil le_refl)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="length (liftB \<alpha>)"
      and s="length \<alpha>"
      in ssubst)
   apply(rename_tac e)(*strict*)
   apply (metis liftB_reflects_length)
  apply(rename_tac e)(*strict*)
  apply(clarsimp)
  done

lemma cfgLM_trans_der_drop_leading_terminals_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=liftB \<alpha>@w1\<rparr> \<pi> \<lparr>cfg_conf=liftB \<alpha>@w2\<rparr>
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=w1\<rparr> \<pi> \<lparr>cfg_conf=w2\<rparr>"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfgLM_trans_der_drop_leading_terminals)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfgLM_trans_der_coincide: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 c0 \<pi>1 c1
  \<Longrightarrow> cfgLM.trans_der G d2 c0 \<pi> c3
  \<Longrightarrow> \<pi>=\<pi>1@\<pi>2
  \<Longrightarrow> i\<le>length \<pi>1
  \<Longrightarrow> d2 i=d1 i"
  apply(induct i)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>1)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i e ea)(*strict*)
     apply(force)
    apply(rename_tac i e ea)(*strict*)
    apply(force)
   apply(rename_tac i e ea)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac i)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac i e ea e1 e2 c1a c2)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>1@\<pi>2)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac i e ea e1 e2 c1a c2)(*strict*)
     apply(force)
    apply(rename_tac i e ea e1 e2 c1a c2)(*strict*)
    apply(force)
   apply(rename_tac i e ea e1 e2 c1a c2)(*strict*)
   apply(force)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
  apply(subgoal_tac "e2 = \<pi>1!i")
   apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
       apply(force)
      apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
      apply(force)
     apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
     apply(force)
    apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
    apply(force)
   apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
   apply(force)
  apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
  apply(subgoal_tac "e2a = (\<pi>1@\<pi>2)!i")
   apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
       apply(force)
      apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
      apply(force)
     apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
     apply(force)
    apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
    apply(force)
   apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
   apply(force)
  apply(rename_tac i e1 e2 e2a c1a c2 c2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 c1a c2 c2a)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac i e1 c1a c2 c2a)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac i e1 c1a c2 c2a)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i e1 c1a c2 c2a l r la ra)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac i e1 c1a c2 c2a l r la ra cfg_confa)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac i e1 c1a c2 c2a l r la ra cfg_confa cfg_confaa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac i e1 c1a c2 c2a l r la ra cfg_confa cfg_confaa cfg_confb)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 l r la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac i e1 l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac i e1 l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 r la ra l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac i e1 r la ra l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac i e1 r la ra l')(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 r ra l' l'a)(*strict*)
  apply(subgoal_tac "l'a=l'")
   apply(rename_tac i e1 r ra l' l'a)(*strict*)
   prefer 2
   apply (metis simple_identify)
  apply(rename_tac i e1 r ra l' l'a)(*strict*)
  apply(clarsimp)
  done

lemma cfgLM_trans_der_coincide2: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 c0 \<pi>1 c1
  \<Longrightarrow> cfgLM.trans_der G d2 c0 \<pi> c3
  \<Longrightarrow> \<pi>=\<pi>1@\<pi>2
  \<Longrightarrow> d2 (length \<pi>1) = d1 (length \<pi>1)"
  apply(rule cfgLM_trans_der_coincide)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfgLM_trans_der_coincide3: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 c0 \<pi>1 c1
  \<Longrightarrow> d2 (length \<pi>1) = Some (pair e c2)
  \<Longrightarrow> cfgLM.trans_der G d2 c0 \<pi> c3
  \<Longrightarrow> \<pi>=\<pi>1@\<pi>2
  \<Longrightarrow> c1=c2"
  apply(subgoal_tac "d2 (length \<pi>1) = d1 (length \<pi>1)")
   apply(simp add: cfgLM.trans_der_def)
  apply(rule cfgLM_trans_der_coincide2)
     apply(force)+
  done

lemma nonterminal_in_any_pre_configuration: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = w1 @ y\<rparr> \<pi> \<lparr>cfg_conf = w @ c\<rparr>
  \<Longrightarrow> cfgLM.trans_der G da \<lparr>cfg_conf = w1\<rparr> \<pi> ca
  \<Longrightarrow> k < length \<pi>
  \<Longrightarrow> \<exists>w1 A w2. cfg_conf (the (get_configuration (d k))) = liftB w1 @ teA A # w2 @ y"
  apply(induct k)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(simp add: get_configuration_def)
   apply(clarsimp)
   apply(rename_tac e ea)(*strict*)
   apply(case_tac \<pi>)
    apply(rename_tac e ea)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ea a list)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac e ea a list)(*strict*)
    prefer 2
    apply(rule_tac
      m="length (a # list)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac e ea a list)(*strict*)
      apply(force)
     apply(rename_tac e ea a list)(*strict*)
     apply(force)
    apply(rename_tac e ea a list)(*strict*)
    apply(force)
   apply(rename_tac e ea a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea a list e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e ea a list e2 c2 l r)(*strict*)
   apply(case_tac c2)
   apply(rename_tac e ea a list e2 c2 l r cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea a list e2 l r)(*strict*)
   apply(subgoal_tac "\<exists>l'. liftB l' = l")
    apply(rename_tac e ea a list e2 l r)(*strict*)
    prefer 2
    apply(rule_tac
      x="filterB l"
      in exI)
    apply (rule liftBDeConv2)
    apply (metis setA_substring setA_substring_prime)
   apply(rename_tac e ea a list e2 l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea a list e2 r l')(*strict*)
   apply(subgoal_tac "strict_prefix (liftB l') w1 \<or> SSX" for SSX)
    apply(rename_tac e ea a list e2 r l')(*strict*)
    prefer 2
    apply(rule mutual_strict_prefix_prefix)
    apply(rule sym)
    apply(force)
   apply(rename_tac e ea a list e2 r l')(*strict*)
   apply(erule disjE)
    apply(rename_tac e ea a list e2 r l')(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac e ea a list e2 r l' cb)(*strict*)
    apply(subgoal_tac "X" for X)
     apply(rename_tac e ea a list e2 r l' cb)(*strict*)
     prefer 2
     apply(rule liftB_append)
     apply(force)
    apply(rename_tac e ea a list e2 r l' cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea a list e2 r l1 l2)(*strict*)
    apply(thin_tac "liftB l1 @ liftB l2 = liftB (l1 @ l2)")
    apply(thin_tac "setA (liftB (l1 @ l2)) = {}")
    apply(simp add: liftB_commutes_over_concat)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. da 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
     apply(rename_tac e ea a list e2 r l1 l2)(*strict*)
     prefer 2
     apply(rule_tac
      m="length (a # list)"
      in cfgLM.step_detail_before_some_position)
       apply(rename_tac e ea a list e2 r l1 l2)(*strict*)
       apply(force)
      apply(rename_tac e ea a list e2 r l1 l2)(*strict*)
      apply(force)
     apply(rename_tac e ea a list e2 r l1 l2)(*strict*)
     apply(force)
    apply(rename_tac e ea a list e2 r l1 l2)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea a list e2 r l1 l2 e2a c2)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac e ea a list e2 r l1 l2 e2a c2 l ra)(*strict*)
    apply(case_tac c2)
    apply(rename_tac e ea a list e2 r l1 l2 e2a c2 l ra cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ea a list e2 r l1 l2 e2a l ra)(*strict*)
    apply (metis liftB_with_nonterminal_inside)
   apply(rename_tac e ea a list e2 r l')(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
   apply(rename_tac e ea a list e2 r l' cb)(*strict*)
   apply(case_tac cb)
    apply(rename_tac e ea a list e2 r l' cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ea a list e2 r l' cb aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ea a list e2 l' lista)(*strict*)
   apply(force)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d k = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac k w1a A w2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac k w1a A w2 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="(length \<pi>)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac k w1a A w2 e ea)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e ea)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e ea)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. da k = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac k w1a A w2 e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac k w1a A w2 e1 e2 c1 c2 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="(length \<pi>)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac k w1a A w2 e1 e2 c1 c2 e ea)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e2 c1 c2 e ea)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e2 c1 c2 e ea)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e2 c1 c2 e1a e2a c1a c2a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c1)
  apply(rename_tac k w1a A w2 e1 e2 c1 c2 e1a e2a c1a c2a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e2 c2 e1a e2a c1a c2a)(*strict*)
  apply(case_tac c2)
  apply(rename_tac k w1a A w2 e1 e2 c2 e1a e2a c1a c2a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a cfg_conf)(*strict*)
  apply(rename_tac v)
  apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
  apply(subgoal_tac "e2 = \<pi>!k")
   apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
       apply(force)
      apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
      apply(force)
     apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
  apply(subgoal_tac "e2a = \<pi>!k")
   apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
   prefer 2
   apply(rule_tac
      d="da"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
       apply(force)
      apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
      apply(force)
     apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e2 e1a e2a c1a c2a v)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e1a c1a c2a v)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac k w1a A w2 e1 e1a c1a c2a v cfg_conf)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac k w1a A w2 e1 e1a c1a c2a v cfg_conf cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e1a v cfg_conf cfg_confa)(*strict*)
  apply(rename_tac v1 v2)
  apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = w1 @ y\<rparr> (take k \<pi>) \<lparr>cfg_conf = liftB w1a @ teA A # w2 @ y\<rparr>")
   apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
   prefer 2
   apply(rule_tac
      n="k"
      in cfgLM.trans_der_crop)
       apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
       apply(force)
      apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
      apply(force)
     apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G da \<lparr>cfg_conf = w1\<rparr> (take k \<pi>) \<lparr>cfg_conf = v1\<rparr>")
   apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
   prefer 2
   apply(rule_tac
      n="k"
      in cfgLM.trans_der_crop)
       apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
       apply(force)
      apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
      apply(force)
     apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>="take k \<pi>"
      and ?w1.0="w1"
      and ?w2.0="y"
      and ?d1.0="d"
      and ?d2.0="da"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e1a v v1 v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = w1 @ y\<rparr> (take k \<pi>) \<lparr>cfg_conf = liftB w1a @ teA A # w2 @ y\<rparr>")
  apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = w1\<rparr> (take k \<pi>) \<lparr>cfg_conf = liftB w1a @ teA A # w2\<rparr>")
  apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = w1 @ y\<rparr> (take (Suc k) \<pi>) \<lparr>cfg_conf = v\<rparr>")
   apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc k"
      in cfgLM.trans_der_crop)
       apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
       apply(force)
      apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
      apply(force)
     apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G da \<lparr>cfg_conf = w1\<rparr> (take (Suc k) \<pi>) \<lparr>cfg_conf = v2\<rparr>")
   apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
   prefer 2
   apply(rule_tac
      n="Suc k"
      in cfgLM.trans_der_crop)
       apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
       apply(force)
      apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
      apply(force)
     apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>="take (Suc k) \<pi>"
      and ?w1.0="w1"
      and ?w2.0="y"
      and ?d1.0="d"
      and ?d2.0="da"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
     apply(force)
    apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
    apply(force)
   apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
   apply(force)
  apply(rename_tac k w1a A w2 e1 e1a v v2)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e1a v2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G d \<lparr>cfg_conf = w1 @ y\<rparr> (take (Suc k) \<pi>) \<lparr>cfg_conf = v2 @ y\<rparr>")
  apply(rename_tac k w1a A w2 e1 e1a v2)(*strict*)
  apply(thin_tac "cfgLM.trans_der G da \<lparr>cfg_conf = w1\<rparr> (take (Suc k) \<pi>) \<lparr>cfg_conf = v2\<rparr>")
  apply(rename_tac k w1a A w2 e1 e1a v2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e1a l r la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac k w1a A w2 e1 e1a l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac k w1a A w2 e1 e1a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e1a r la ra l')(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac k w1a A w2 e1 e1a r la ra l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac k w1a A w2 e1 e1a r la ra l')(*strict*)
  apply(clarsimp)
  apply(rename_tac k w1a A w2 e1 e1a r ra l' l'a)(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(subgoal_tac "w1a=l'")
   apply(rename_tac k w1a A w2 e1 e1a r ra l' l'a)(*strict*)
   prefer 2
   apply (metis simple_identify)
  apply(rename_tac k w1a A w2 e1 e1a r ra l' l'a)(*strict*)
  apply(subgoal_tac "w1a=l'a")
   apply(rename_tac k w1a A w2 e1 e1a r ra l' l'a)(*strict*)
   prefer 2
   apply (metis simple_identify)
  apply(rename_tac k w1a A w2 e1 e1a r ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e1 e1a r l')(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. da (Suc k) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac k e1 e1a r l')(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac k e1 e1a r l' e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="(length \<pi>)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac k e1 e1a r l' e ea)(*strict*)
     apply(force)
    apply(rename_tac k e1 e1a r l' e ea)(*strict*)
    apply(force)
   apply(rename_tac k e1 e1a r l' e ea)(*strict*)
   apply(force)
  apply(rename_tac k e1 e1a r l')(*strict*)
  apply(clarsimp)
  apply(rename_tac k e1 e1a r l' e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac k e1 e1a r l' e2 c2 l ra)(*strict*)
  apply(case_tac c2)
  apply(rename_tac k e1 e1a r l' e2 c2 l ra cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e1 e1a r l' e2 l ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac k e1 e1a r l' e2 l ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply (metis setA_substring setA_substring_prime)
  apply(rename_tac k e1 e1a r l' e2 l ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e1 e1a r l' e2 ra l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(force)
  done

lemma cfgLM_trans_der_preserves_terminal_prefix: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c0 \<pi> \<lparr>cfg_conf=w\<rparr>
  \<Longrightarrow> n\<le>length \<pi>
  \<Longrightarrow> d n = Some (pair e \<lparr>cfg_conf=liftB \<alpha>@\<beta>\<rparr>)
  \<Longrightarrow> prefix (liftB \<alpha>) w"
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac ea)(*strict*)
   apply(rule_tac
      d="d"
      and i="n"
      and j="length \<pi>-n"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac ea)(*strict*)
        apply(simp add: )
       apply(rename_tac ea)(*strict*)
       apply(force)
      apply(rename_tac ea)(*strict*)
      apply(force)
     apply(rename_tac ea)(*strict*)
     apply(force)
    apply(rename_tac ea)(*strict*)
    apply(force)
   apply(rename_tac ea)(*strict*)
   apply(force)
  apply(simp add: cfg_get_history_def)
  apply(clarsimp)
  apply(rename_tac wa)(*strict*)
  apply(subgoal_tac "maxTermPrefix (liftB \<alpha> @ \<beta>) = \<alpha>@maxTermPrefix \<beta>")
   apply(rename_tac wa)(*strict*)
   apply(rule prefix_of_maxTermPrefix_is_terminal_string_prefix)
   apply(force)
  apply(rename_tac wa)(*strict*)
  apply (metis maxTermPrefix_shift)
  done

lemma cfgLM_trans_der_biextend2_prime: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=w1\<rparr> \<pi>1 \<lparr>cfg_conf=w1'\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=w2\<rparr> \<pi>2 \<lparr>cfg_conf=w2'\<rparr>
  \<Longrightarrow> \<pi>3=\<pi>1@\<pi>2
  \<Longrightarrow> w1'=liftB \<alpha>2@w1''
  \<Longrightarrow> w2=w1''@C1
  \<Longrightarrow> w3=liftB \<alpha>1@w1@C1@C2
  \<Longrightarrow> w3'=liftB \<alpha>1@liftB \<alpha>2@w2'@C2
  \<Longrightarrow> \<lparr>cfg_conf=liftB \<alpha>1@C1@C2\<rparr> \<in> cfg_configurations G
  \<Longrightarrow> \<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf=w3\<rparr> \<pi>3 \<lparr>cfg_conf=w3'\<rparr>"
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      G="G"
      and v="\<alpha>1"
      and ?w2.0="C1@C2"
      and ?d1.0="d1"
      in cfgLM_trans_der_context_prime)
     apply(force)
    apply(force)
   apply(force)
  apply(thin_tac "cfgLM.trans_der G d1 \<lparr>cfg_conf = w1\<rparr> \<pi>1 \<lparr>cfg_conf = liftB \<alpha>2 @ w1''\<rparr>")
  apply(clarsimp)
  apply(rename_tac d)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac d)(*strict*)
   prefer 2
   apply(rule_tac
      ?v2.0="w1''@C1"
      and G="G"
      and ?v1.0="\<alpha>1@\<alpha>2"
      and ?v4.0="C2"
      and ?d1.0="d"
      and ?d2.0="d2"
      in cfgLM_trans_der_concat_extend_prime)
     apply(rename_tac d)(*strict*)
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(simp add: liftB_commutes_over_concat)
   apply(rename_tac d)(*strict*)
   apply(force)
  apply(rename_tac d)(*strict*)
  apply(simp add: liftB_commutes_over_concat)
  done

lemma entire_realizable_hlp: "
valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = [teA A]\<rparr> (\<pi>1 @ \<pi>2) \<lparr>cfg_conf = w\<rparr>
  \<Longrightarrow> \<pi>1 \<noteq> []
  \<Longrightarrow> x \<sqsubseteq> \<pi>1 \<and> (\<exists>c. (\<exists>d. cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs (hd \<pi>1))]\<rparr> x c) \<and> (setA (cfg_conf c) = {} \<or> x = \<pi>1))
  \<Longrightarrow> x = \<pi>1"
  apply(clarsimp)
  apply(rename_tac c da)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac c da ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac c da ca cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac da ca cfg_conf)(*strict*)
  apply(rename_tac w2)
  apply(rename_tac da ca w2)(*strict*)
  apply(case_tac x)
   apply(rename_tac da ca w2)(*strict*)
   apply(clarsimp)
   apply(case_tac ca)
    apply(rename_tac da ca w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac da ca w2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac da w2 a list)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
  apply(rename_tac da ca w2 a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "A=prod_lhs a")
   apply(rename_tac da ca w2 a list)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. d 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
    apply(rename_tac da ca w2 a list)(*strict*)
    prefer 2
    apply(unfold cfgLM.trans_der_def)
    apply(erule exE)+
    apply(rename_tac da ca w2 a list e ea)(*strict*)
    apply(fold cfgLM.trans_der_def)
    apply(rule_tac
      m="length (a # list@ca@\<pi>2)"
      in cfgLM.step_detail_before_some_position)
      apply(rename_tac da ca w2 a list e ea)(*strict*)
      apply(force)
     apply(rename_tac da ca w2 a list e ea)(*strict*)
     apply(force)
    apply(rename_tac da ca w2 a list e ea)(*strict*)
    apply(force)
   apply(rename_tac da ca w2 a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac da ca w2 a list e1 e2 c1 c2)(*strict*)
   apply(subgoal_tac "c1=\<lparr>cfg_conf = [teA A]\<rparr>")
    apply(rename_tac da ca w2 a list e1 e2 c1 c2)(*strict*)
    prefer 2
    apply(simp add: cfgLM.trans_der_def)
   apply(rename_tac da ca w2 a list e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac da ca w2 a list e1 e2 c2 l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac da ca w2 a list e1 e2 c2 l r)(*strict*)
    prefer 2
    apply(rename_tac da ca w2 a list e1 e2 c2 l r aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac da ca w2 a list e1 e2 c2 l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
   apply(subgoal_tac "e2=a")
    apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      in cfgLM.trans_der_getLabel_at_pos)
        apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
        apply(force)
       apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
       apply(force)
      apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
      apply(force)
     apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac da ca w2 a list e1 e2 c2)(*strict*)
   apply(clarsimp)
  apply(rename_tac da ca w2 a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (length(a#list)) = Some (pair e c)")
   apply(rename_tac da ca w2 a list)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac da ca w2 a list e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (a#list@ca@\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac da ca w2 a list e ea)(*strict*)
     apply(force)
    apply(rename_tac da ca w2 a list e ea)(*strict*)
    apply(force)
   apply(rename_tac da ca w2 a list e ea)(*strict*)
   apply(force)
  apply(rename_tac da ca w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac da ca w2 a list e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac da ca w2 a list e c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac da ca w2 a list e cfg_conf)(*strict*)
  apply(rename_tac wx)
  apply(rename_tac da ca w2 a list e wx)(*strict*)
  apply(subgoal_tac "cfgLM.trans_der G d \<lparr>cfg_conf = [teA (prod_lhs a)]\<rparr> (a#list) \<lparr>cfg_conf = wx\<rparr>")
   apply(rename_tac da ca w2 a list e wx)(*strict*)
   prefer 2
   apply(rule_tac
      n="length(a#list)"
      in cfgLM.trans_der_crop)
       apply(rename_tac da ca w2 a list e wx)(*strict*)
       apply(simp add: )
      apply(rename_tac da ca w2 a list e wx)(*strict*)
      apply(force)
     apply(rename_tac da ca w2 a list e wx)(*strict*)
     apply(force)
    apply(rename_tac da ca w2 a list e wx)(*strict*)
    apply(force)
   apply(rename_tac da ca w2 a list e wx)(*strict*)
   apply(force)
  apply(rename_tac da ca w2 a list e wx)(*strict*)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac da ca w2 a list e wx)(*strict*)
   prefer 2
   apply(rule_tac
      ?d1.0="d"
      and ?d2.0="da"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac da ca w2 a list e wx)(*strict*)
     apply(simp add: )
    apply(rename_tac da ca w2 a list e wx)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac da ca w2 a list e wx)(*strict*)
   apply(force)
  apply(rename_tac da ca w2 a list e wx)(*strict*)
  apply(clarsimp)
  apply(rename_tac da ca a list e wx)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = wx")
   apply(rename_tac da ca a list e wx)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB wx"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac da ca a list e wx)(*strict*)
  apply(clarsimp)
  apply(rename_tac da ca a list e l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (length(a#list)) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac da ca a list e l')(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac da ca a list e l' ea eb ec)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (a # list@ca@\<pi>2)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac da ca a list e l' ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac da ca a list e l' ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac da ca a list e l' ea eb ec)(*strict*)
   apply(clarsimp)
   apply(rename_tac da ca a list l' ea eb ec)(*strict*)
   apply(case_tac ca)
    apply(rename_tac da ca a list l' ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac da ca a list l' ea eb ec aa lista)(*strict*)
   apply(force)
  apply(rename_tac da ca a list e l')(*strict*)
  apply(clarsimp)
  apply(rename_tac da ca a list e l' e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac da ca a list e l' e2 c2 l r)(*strict*)
  apply (metis liftB_with_nonterminal_inside)
  done

lemma productions_suffix_starts_at_begin: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c1 \<pi> c2
  \<Longrightarrow> (\<forall>i<length \<pi>. \<exists>A. hd(cfg_conf(the(get_configuration(d i)))) = teA A)
  \<Longrightarrow> i<length \<pi>
  \<Longrightarrow> hd(cfg_conf(the(get_configuration(d i))))=teA(prod_lhs(hd(drop i \<pi>)))"
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac e)(*strict*)
     apply(force)
    apply(rename_tac e)(*strict*)
    apply(force)
   apply(rename_tac e)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e1 e2 c1a c2a)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c1a)
  apply(rename_tac e1 e2 c1a c2a cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac e1 e2 c1a c2a w)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2a w)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2a w A)(*strict*)
  apply(case_tac "drop i \<pi>")
   apply(rename_tac e1 e2 c2a w A)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 c2a w A a list)(*strict*)
  apply(clarsimp)
  apply(case_tac w)
   apply(rename_tac e1 e2 c2a w A a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c2a A a list)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac e1 e2 c2a w A a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 c2a A a list lista)(*strict*)
  apply(subgoal_tac "a=e2")
   apply(rename_tac e1 e2 c2a A a list lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 c2a A list lista)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e1 e2 c2a A list lista l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac e1 e2 c2a A list lista l r)(*strict*)
    prefer 2
    apply(rename_tac e1 e2 c2a A list lista l r a listb)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1 e2 c2a A list lista l r)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1 e2 c2a A a list lista)(*strict*)
  apply(rule sym)
  apply(rule_tac
      d="d"
      in cfgLM.trans_der_getLabel_at_pos)
      apply(rename_tac e1 e2 c2a A a list lista)(*strict*)
      apply(force)
     apply(rename_tac e1 e2 c2a A a list lista)(*strict*)
     apply(force)
    apply(rename_tac e1 e2 c2a A a list lista)(*strict*)
    apply(force)
   apply(rename_tac e1 e2 c2a A a list lista)(*strict*)
   apply(force)
  apply(rename_tac e1 e2 c2a A a list lista)(*strict*)
  apply (metis nth_via_drop)
  done

lemma cfgLM_trans_der_cfgLM_derivation_can_be_decomposed: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = w1@w2\<rparr> \<pi> \<lparr>cfg_conf = liftB \<alpha>\<rparr>
  \<Longrightarrow> \<exists>d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2. \<pi>1@\<pi>2=\<pi> \<and> \<alpha>=\<alpha>1@\<alpha>2 \<and> cfgLM.trans_der G d1 \<lparr>cfg_conf = w1\<rparr> \<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr> \<and> cfgLM.trans_der G d2 \<lparr>cfg_conf = w2\<rparr> \<pi>2 \<lparr>cfg_conf = liftB \<alpha>2\<rparr>"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      ?d.0="d"
      in cfgLM_derivation_can_be_decomposed)
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
  apply(clarsimp)
  apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
  apply(rule_tac
      x="d1"
      in exI)
  apply(rule_tac
      x="d2"
      in exI)
  apply(rule_tac
      x="map the (get_labels d1 n1)"
      in exI)
  apply(rule_tac
      x="map the (get_labels d2 n2)"
      in exI)
  apply(rule conjI)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(rule_tac
      t="\<pi>"
      and s="map the (get_labels d (n1 + n2))"
      in ssubst)
    apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
    apply(simp add: cfgLM.trans_der_def)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply (metis List.map_append)
  apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
  apply(rule_tac
      x="v1"
      in exI)
  apply(rule_tac
      x="v2"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
   apply(rule conjI)
    apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
    apply(rule_tac
      t="length (get_labels d1 n1)"
      and s="n1"
      in ssubst)
     apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
     apply (metis get_labels_length)
    apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
    apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
     apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
     apply(force)
    apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
    apply(force)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
   apply(rule_tac
      t="length (get_labels d1 n1)"
      and s="n1"
      in ssubst)
    apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
   apply(force)
  apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2)(*strict*)
  apply(simp add: cfgLM.trans_der_def)
  apply(clarsimp)
  apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
  apply(rule conjI)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
   apply(rule_tac
      t="length (get_labels d2 n2)"
      and s="n2"
      in ssubst)
    apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
    apply (metis get_labels_length)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
   apply(rule cfgLM.get_labels_the_Some_on_defined_positions)
    apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
    apply(force)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
   apply(force)
  apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
  apply(rule_tac
      t="length (get_labels d2 n2)"
      and s="n2"
      in ssubst)
   apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
   apply (metis get_labels_length)
  apply(rename_tac v1 v2 d1 d2 e1 e2 n1 n2 e)(*strict*)
  apply(force)
  done

lemma cfgLM_trans_der_cfgLM_derivation_can_be_decomposed_into_trans_der_list: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = liftA w\<rparr> \<pi> \<lparr>cfg_conf = liftB \<alpha>\<rparr>
  \<Longrightarrow> \<exists>ds f\<pi> fw.
          cfgLM.trans_der_list G ds
           (map (\<lambda>x. \<lparr>cfg_conf = [teA x]\<rparr>) w) f\<pi> (map (\<lambda>x. \<lparr>cfg_conf = liftB x\<rparr>) fw) \<and>
          foldl (@) [] fw = \<alpha> \<and> foldl (@) [] f\<pi> = \<pi>"
  apply(induct w arbitrary: d \<pi> \<alpha>)
   apply(rename_tac d \<pi> \<alpha>)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "SSrenPI=[] \<and> SSc2=\<lparr>cfg_conf=[]\<rparr>" for SSrenPI SSc2)
    apply(rename_tac d \<pi> \<alpha>)(*strict*)
    prefer 2
    apply(rule_tac cfgLM_trans_der_from_empty)
    apply(force)
   apply(rename_tac d \<pi> \<alpha>)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<alpha>)(*strict*)
   apply(case_tac \<alpha>)
    apply(rename_tac d \<alpha>)(*strict*)
    prefer 2
    apply(rename_tac d \<alpha> a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac d \<alpha>)(*strict*)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_list_def)
  apply(rename_tac a w d \<pi> \<alpha>)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac a w d \<pi> \<alpha>)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="[teA a]"
      in cfgLM_trans_der_cfgLM_derivation_can_be_decomposed)
    apply(rename_tac a w d \<pi> \<alpha>)(*strict*)
    apply(force)
   apply(rename_tac a w d \<pi> \<alpha>)(*strict*)
   apply(force)
  apply(rename_tac a w d \<pi> \<alpha>)(*strict*)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(erule_tac
      x="d2"
      in meta_allE)
  apply(erule_tac
      x="\<pi>2"
      in meta_allE)
  apply(erule_tac
      x="\<alpha>2"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 \<pi>1 \<alpha>1 ds f\<pi> fw)(*strict*)
  apply(rule_tac
      x="d1#ds"
      in exI)
  apply(rule_tac
      x="\<pi>1#f\<pi>"
      in exI)
  apply(rule_tac
      x="\<alpha>1#fw"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) \<alpha>1 fw"
      in ssubst)
   apply(rename_tac a w d d1 d2 \<pi>1 \<alpha>1 ds f\<pi> fw)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w d d1 d2 \<pi>1 \<alpha>1 ds f\<pi> fw)(*strict*)
  apply(rule_tac
      t="foldl (@) \<pi>1 f\<pi>"
      in ssubst)
   apply(rename_tac a w d d1 d2 \<pi>1 \<alpha>1 ds f\<pi> fw)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w d d1 d2 \<pi>1 \<alpha>1 ds f\<pi> fw)(*strict*)
  apply(clarsimp)
  apply(simp add: cfgLM.trans_der_list_def)
  apply(clarsimp)
  apply(rename_tac a w d d1 d2 \<pi>1 \<alpha>1 ds f\<pi> fw i)(*strict*)
  apply(case_tac i)
   apply(rename_tac a w d d1 d2 \<pi>1 \<alpha>1 ds f\<pi> fw i)(*strict*)
   apply(clarsimp)
  apply(rename_tac a w d d1 d2 \<pi>1 \<alpha>1 ds f\<pi> fw i nat)(*strict*)
  apply(clarsimp)
  done

lemma generation_derivation_has_always_nonterminal_at_front: "
  valid_cfg G
  \<Longrightarrow> X\<noteq>None
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = liftA w\<rparr> (\<pi>) \<lparr>cfg_conf = option_to_list X @ v\<rparr>
  \<Longrightarrow> (\<exists>b. Some (teB b) = X) \<longrightarrow> (\<forall>i<length (\<pi>). hd (cfg_conf (the (get_configuration (d i)))) \<noteq> the X)
  \<Longrightarrow> \<forall>i<length (\<pi>). \<exists>A. hd (cfg_conf (the (get_configuration (d i)))) = teA A"
  apply(case_tac "X")
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a i)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac a i)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac a i e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac a i e)(*strict*)
     apply(force)
    apply(rename_tac a i e)(*strict*)
    apply(force)
   apply(rename_tac a i e)(*strict*)
   apply(force)
  apply(rename_tac a i)(*strict*)
  apply(clarsimp)
  apply(rename_tac a i e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c1)
  apply(rename_tac a i e1 e2 c1 c2 cfg_confa)(*strict*)
  apply(rename_tac wx)
  apply(rename_tac a i e1 e2 c1 c2 wx)(*strict*)
  apply(clarsimp)
  apply(rename_tac a i e1 e2 c2 wx)(*strict*)
  apply(case_tac wx)
   apply(rename_tac a i e1 e2 c2 wx)(*strict*)
   apply(clarsimp)
   apply(rename_tac a i e1 e2 c2)(*strict*)
   apply(simp add: cfgLM_step_relation_def)
  apply(rename_tac a i e1 e2 c2 wx aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a i e1 e2 c2 aa list)(*strict*)
  apply(case_tac aa)
   apply(rename_tac a i e1 e2 c2 aa list ab)(*strict*)
   apply(clarsimp)
  apply(rename_tac a i e1 e2 c2 aa list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a i e1 e2 c2 list b)(*strict*)
  apply(subgoal_tac "\<exists>w. cfg_get_history SSci @ w = cfg_get_history SScij" for SSci SScij)
   apply(rename_tac a i e1 e2 c2 list b)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac a i e1 e2 c2 list b e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      d="d"
      and i="i"
      and j="length \<pi>-i"
      in cfgLM.derivation_monotonically_inc)
        apply(rename_tac a i e1 e2 c2 list b e)(*strict*)
        apply(force)
       apply(rename_tac a i e1 e2 c2 list b e)(*strict*)
       apply(force)
      apply(rename_tac a i e1 e2 c2 list b e)(*strict*)
      apply(force)
     apply(rename_tac a i e1 e2 c2 list b e)(*strict*)
     apply(force)
    apply(rename_tac a i e1 e2 c2 list b e)(*strict*)
    apply(force)
   apply(rename_tac a i e1 e2 c2 list b e)(*strict*)
   apply(force)
  apply(rename_tac a i e1 e2 c2 list b)(*strict*)
  apply(clarsimp)
  apply(rename_tac a i e1 e2 c2 list b wa)(*strict*)
  apply(simp add: cfg_get_history_def)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "maxTermPrefix (teB b # list) = b#maxTermPrefix list")
   apply(rename_tac a i e1 e2 c2 list b wa)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_pull_out)
  apply(rename_tac a i e1 e2 c2 list b wa)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
   apply(rename_tac a i e1 e2 c2 list b wa aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c2 list b wa aa)(*strict*)
   apply(subgoal_tac "maxTermPrefix (teA aa # v) = []")
    apply(rename_tac i e1 e2 c2 list b wa aa)(*strict*)
    apply(force)
   apply(rename_tac i e1 e2 c2 list b wa aa)(*strict*)
   apply (metis maxTermPrefix_vs_maximalPrefixB maximalPrefixB_front)
  apply(rename_tac a i e1 e2 c2 list b wa ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c2 list b wa ba)(*strict*)
  apply(subgoal_tac "maxTermPrefix (teB ba # v) = ba#maxTermPrefix v")
   apply(rename_tac i e1 e2 c2 list b wa ba)(*strict*)
   prefer 2
   apply (metis maxTermPrefix_pull_out)
  apply(rename_tac i e1 e2 c2 list b wa ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c2 list wa ba)(*strict*)
  apply(force)
  done

lemma from_derives_prefix: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf = [teA A]@w\<rparr> \<pi> \<lparr>cfg_conf = liftB \<alpha>\<rparr>
  \<Longrightarrow> \<exists>d1 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2. \<pi>1@\<pi>2=\<pi> \<and> \<alpha>=\<alpha>1@\<alpha>2 \<and> cfgLM.trans_der G d1 \<lparr>cfg_conf = [teA A]\<rparr> \<pi>1 \<lparr>cfg_conf = liftB \<alpha>1\<rparr>"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac
      ?w1.0="[teA A]"
      and ?w2.0="w"
      in cfgLM_trans_der_cfgLM_derivation_can_be_decomposed)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac d1 d2 \<pi>1 \<pi>2 \<alpha>1 \<alpha>2)(*strict*)
  apply(rule_tac
      x="d1"
      in exI)
  apply(rule_tac
      x="\<pi>1"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      x="\<alpha>1"
      in exI)
  apply(clarsimp)
  done

lemma unique_generation_length: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d1 c \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 c \<pi>2 cX
  \<Longrightarrow> \<pi>1@w=\<pi>2
  \<Longrightarrow> w=[]"
  apply(case_tac "w=[]")
   apply(force)
  apply(subgoal_tac "False")
   apply(force)
  apply(subgoal_tac "\<exists>e c. d2 (length \<pi>1) = Some (pair e c)")
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(\<pi>2)"
      in cfgLM.pre_some_position_is_some_position)
     apply(rename_tac e ea)(*strict*)
     apply(force)
    apply(rename_tac e ea)(*strict*)
    apply(force)
   apply(rename_tac e ea)(*strict*)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e ca)(*strict*)
  apply(case_tac ca)
  apply(rename_tac e ca cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac e cfg_conf)(*strict*)
  apply(case_tac c)
  apply(rename_tac e cfg_conf cfg_confa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e cfg_conf cfg_confa)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>="(\<pi>1 @ w)"
      and d="d2"
      in cfgLM_trans_der_crop)
      apply(rename_tac e cfg_conf cfg_confa)(*strict*)
      apply(force)
     apply(rename_tac e cfg_conf cfg_confa)(*strict*)
     apply(force)
    apply(rename_tac e cfg_conf cfg_confa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac e cfg_conf cfg_confa)(*strict*)
   apply(force)
  apply(rename_tac e cfg_conf cfg_confa)(*strict*)
  apply(rename_tac w1 w2)
  apply(rename_tac e w1 w2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "SSv2@SSw2=SSv1" for SSv2 SSw2 SSv1)
   apply(rename_tac e w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      \<pi>="\<pi>1"
      and ?w2.0="[]"
      and ?d1.0="d1"
      and ?d2.0="derivation_take d2 (length \<pi>1)"
      in equal_labels_from_same_configuration_up_to_context_implies_same_modification)
     apply(rename_tac e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac e w1 w2)(*strict*)
   apply(force)
  apply(rename_tac e w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w2)(*strict*)
  apply(case_tac w)
   apply(rename_tac e w2)(*strict*)
   apply(force)
  apply(rename_tac e w2 a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 (length \<pi>1) = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac e w2 a list)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac e w2 a list ea eb ec)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>1 @ a # list)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac e w2 a list ea eb ec)(*strict*)
     apply(force)
    apply(rename_tac e w2 a list ea eb ec)(*strict*)
    apply(force)
   apply(rename_tac e w2 a list ea eb ec)(*strict*)
   apply(force)
  apply(rename_tac e w2 a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w2 a list e2 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply (metis liftB_with_nonterminal_inside)
  done

lemma cfgLM_trans_der_prods: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d c1 \<pi> c2
  \<Longrightarrow> set \<pi> \<subseteq> cfg_productions G"
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "\<exists>k<length \<pi>. \<pi>!k=x")
   apply(rename_tac x)(*strict*)
   prefer 2
   apply (metis set_elem_nth)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc k) = Some (pair (Some e) c)")
   apply(rename_tac k)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac k e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length (\<pi>)"
      in cfgLM.pre_some_position_is_some_position_prime)
      apply(rename_tac k e)(*strict*)
      apply(force)
     apply(rename_tac k e)(*strict*)
     apply(force)
    apply(rename_tac k e)(*strict*)
    apply(force)
   apply(rename_tac k e)(*strict*)
   apply(clarsimp)
  apply(rename_tac k)(*strict*)
  apply(clarsimp)
  apply(rename_tac k e c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac k e c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac k e c)(*strict*)
       apply(force)
      apply(rename_tac k e c)(*strict*)
      apply(force)
     apply(rename_tac k e c)(*strict*)
     apply(force)
    apply(rename_tac k e c)(*strict*)
    apply(force)
   apply(rename_tac k e c)(*strict*)
   apply(force)
  apply(rename_tac k e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac k c)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac k c)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac k c e)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule cfgLM.belongs_step_labels)
    apply(rename_tac k c e)(*strict*)
    apply(force)
   apply(rename_tac k c e)(*strict*)
   apply(force)
  apply(rename_tac k c)(*strict*)
  apply(simp add: cfg_step_labels_def)
  done

lemma no_terminal_production_implies_always_no_terminals: "
  valid_cfg G
  \<Longrightarrow> cfgLM.trans_der G d \<lparr>cfg_conf=liftA w\<rparr> \<pi> c
  \<Longrightarrow> (\<forall>p\<in> set(butlast \<pi>). setB (prod_rhs p) = {})
  \<Longrightarrow> n<length \<pi>
  \<Longrightarrow> d n = Some (pair e cx)
  \<Longrightarrow> setB (cfg_conf cx) = {}"
  apply(induct n arbitrary: e cx)
   apply(rename_tac e cx)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac ea)(*strict*)
   apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  apply(rename_tac n e cx)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e cx)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and i="n"
      and kleene_starT="False"
      and END="False"
      in cfgLM.trans_der_step_detail)
     apply(rename_tac n e cx)(*strict*)
     apply(simp add: )
    apply(rename_tac n e cx)(*strict*)
    apply(force)
   apply(rename_tac n e cx)(*strict*)
   apply(force)
  apply(rename_tac n e cx)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cx ea ci)(*strict*)
  apply(erule_tac
      x="ea"
      in meta_allE)
  apply(erule_tac
      x="ci"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n cx ea ci)(*strict*)
   apply(force)
  apply(rename_tac n cx ea ci)(*strict*)
  apply(erule_tac
      x="\<pi>!n"
      in ballE)
   apply(rename_tac n cx ea ci)(*strict*)
   prefer 2
   apply(rule_tac
      xs="\<pi>"
      in rev_cases)
    apply(rename_tac n cx ea ci)(*strict*)
    apply(clarsimp)
   apply(rename_tac n cx ea ci ys y)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(ys@[y])!n=ys!n")
    apply(rename_tac n cx ea ci ys y)(*strict*)
    apply(force)
   apply(rename_tac n cx ea ci ys y)(*strict*)
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac n cx ea ci)(*strict*)
  apply(case_tac ci)
  apply(rename_tac n cx ea ci cfg_confa)(*strict*)
  apply(case_tac cx)
  apply(rename_tac n cx ea ci cfg_confa cfg_confaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n ea cfg_conf cfg_confa)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n ea l r)(*strict*)
  apply(simp add: setAConcat setBConcat setA_liftB setA_liftA setB_liftA setB_liftB)
  done

lemma equal_elimination_for_equal_nonterminals_prime_prime_prime: "
  valid_cfg G
  \<Longrightarrow> LR1ProdFormSimp G
  \<Longrightarrow> cfgLM.trans_der G d1 \<lparr>cfg_conf=liftB \<alpha>1@liftA \<beta>1\<rparr> \<pi>1 \<lparr>cfg_conf=liftB \<alpha>1'\<rparr>
  \<Longrightarrow> cfgLM.trans_der G d2 \<lparr>cfg_conf=liftB \<alpha>2@liftA \<beta>2\<rparr> (\<pi>2@\<pi>3) \<lparr>cfg_conf=liftB \<alpha>2'\<rparr>
  \<Longrightarrow> length \<pi>1=length \<pi>2
  \<Longrightarrow> (\<forall>k<length \<pi>1. \<forall>x1 x2 y1 y2. prod_rhs (\<pi>1!k) = liftB x1 @ liftA y1 \<longrightarrow> prod_rhs (\<pi>2!k) = liftB x2 @ liftA y2 \<longrightarrow> length y1=length y2)
  \<Longrightarrow> (\<forall>k<length \<pi>1. \<forall>x1 x2 y1 y2. prod_rhs (\<pi>1!k) = liftB x1 @ liftA y1 \<longrightarrow> prod_rhs (\<pi>2!k) = liftB x2 @ liftA y2 \<longrightarrow> y1=y2 \<longrightarrow> \<pi>1!k = \<pi>2!k)
  \<Longrightarrow> length \<beta>1=length \<beta>2
  \<Longrightarrow> \<beta>1=\<beta>2 \<and> \<pi>1=\<pi>2"
  apply(induct \<pi>1 arbitrary: d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>2 \<pi>3)
   apply(rename_tac d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>2 \<pi>3)(*strict*)
   apply(simp add: cfgLM.trans_der_def)
   apply(clarsimp)
   apply(rename_tac d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 ea)(*strict*)
   apply(case_tac \<beta>1)
    apply(rename_tac d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 ea)(*strict*)
    prefer 2
    apply(rename_tac d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 ea a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac d1 d2 \<alpha>1 \<alpha>2 \<beta>2 \<pi>3 ea a list)(*strict*)
    apply (metis liftA.simps(2) nonterminal_not_in_liftB)
   apply(rename_tac d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 ea)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>2 \<pi>3)(*strict*)
  apply(case_tac \<pi>2)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>2 \<pi>3)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>2 \<pi>3 aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 aa list)(*strict*)
  apply(rename_tac b \<pi>2)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2)(*strict*)
  apply(erule_tac
      x="derivation_drop d1 (Suc 0)"
      in meta_allE)
  apply(erule_tac
      x="derivation_drop d2 (Suc 0)"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e ea)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(a#\<pi>1)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e ea)(*strict*)
     apply(force)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e ea)(*strict*)
    apply(force)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e ea)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 0 = Some (pair e1 c1) \<and> SSd (Suc (SSn)) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2" for SSd SSn)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2)(*strict*)
   prefer 2
   apply(unfold cfgLM.trans_der_def)
   apply(erule exE)+
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e ea e1 e2 c1 c2)(*strict*)
   apply(fold cfgLM.trans_der_def)
   apply(rule_tac
      m="length(b#\<pi>2@\<pi>3)"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e ea e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e ea e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e ea e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a l r la ra)(*strict*)
  apply(subgoal_tac "\<exists>l'. liftB l' = l")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a l r la ra)(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB l"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a l r la ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a r la ra l')(*strict*)
  apply(thin_tac "setA (liftB l') = {}")
  apply(subgoal_tac "\<exists>l'. liftB l' = la")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a r la ra l')(*strict*)
   prefer 2
   apply(rule_tac
      x="filterB la"
      in exI)
   apply (rule liftBDeConv2)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a r la ra l')(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a r ra l' l'a)(*strict*)
  apply(thin_tac "setA (liftB l'a) = {}")
  apply(case_tac c1a)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a r ra l' l'a cfg_confa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a r ra l' l'a cfg_confa cfg_confaa)(*strict*)
  apply(case_tac c2a)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 c1a c2 c2a r ra l' l'a cfg_confa cfg_confaa cfg_confb)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 r ra l' l'a)(*strict*)
  apply(case_tac c1)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a c1 r ra l' l'a cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
  apply(subgoal_tac "e2=a")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
   prefer 2
   apply(rule_tac
      d="d1"
      and n="0"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
       apply(force)
      apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
      apply(force)
     apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
     apply(force)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
    apply(force)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
  apply(subgoal_tac "e2a=b")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and n="0"
      in cfgLM.trans_der_getLabel_at_pos)
       apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
       apply(force)
      apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
      apply(force)
     apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
     apply(force)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
    apply(force)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a e2 e2a r ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a r ra l' l'a)(*strict*)
  apply(subgoal_tac "Some (pair e1 \<lparr>cfg_conf = liftB l' @ teA (prod_lhs a) # r\<rparr>) = Some (pair None \<lparr>cfg_conf = liftB \<alpha>1 @ liftA \<beta>1\<rparr>)")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a r ra l' l'a)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a r ra l' l'a)(*strict*)
  apply(subgoal_tac "Some (pair e1a \<lparr>cfg_conf = liftB l'a @ teA (prod_lhs b) # ra\<rparr>) = Some (pair None \<lparr>cfg_conf = liftB \<alpha>2 @ liftA \<beta>2\<rparr>)")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a r ra l' l'a)(*strict*)
   prefer 2
   apply(simp add: cfgLM.trans_der_def)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 e1 e1a r ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 r ra l' l'a)(*strict*)
  apply(subgoal_tac "l'a = \<alpha>2")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 r ra l' l'a)(*strict*)
   prefer 2
   apply(rule initial_liftB_strings_coincide)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 r ra l' l'a)(*strict*)
  apply(subgoal_tac "l' = \<alpha>1")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 r ra l' l'a)(*strict*)
   prefer 2
   apply(rule initial_liftB_strings_coincide)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 r ra l' l'a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 r ra)(*strict*)
  apply(case_tac \<beta>1)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 r ra)(*strict*)
   apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>1 \<beta>2 \<pi>3 b \<pi>2 r ra aa list)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>2 \<pi>3 b \<pi>2 ra list)(*strict*)
  apply(case_tac \<beta>2)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>2 \<pi>3 b \<pi>2 ra list)(*strict*)
   apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<beta>2 \<pi>3 b \<pi>2 ra list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 list lista)(*strict*)
  apply(rename_tac \<beta>1 \<beta>2)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. prod_rhs a = liftB w1 @ liftA w2")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2)(*strict*)
   prefer 2
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="a"
      in ballE)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2)(*strict*)
   apply(erule disjE)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 ba A B)(*strict*)
    apply(rule_tac
      x="[ba]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 ba A B)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 A B C)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[B,C]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. prod_rhs b = liftB w1 @ liftA w2")
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2)(*strict*)
   prefer 2
   apply(simp add: LR1ProdFormSimp_def)
   apply(erule_tac
      x="b"
      in ballE)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2)(*strict*)
   apply(erule disjE)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 ba A B)(*strict*)
    apply(rule_tac
      x="[ba]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 ba A B)(*strict*)
   apply(erule disjE)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 ba A B)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[B]"
      in exI)
    apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 ba A B)(*strict*)
   apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 \<pi>2 \<beta>1 \<beta>2 w1 w2 A B C)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(rule_tac
      x="[B,C]"
      in exI)
   apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
  apply(erule_tac x="0" and P="\<lambda>x. x < Suc (length \<pi>2) \<longrightarrow> (\<forall>x1 x2 y1. prod_rhs ((a # \<pi>1) ! x) = liftB x1 @ liftA y1 \<longrightarrow> (\<forall>y2. prod_rhs ((b # \<pi>2) ! x) = liftB x2 @ liftA y2 \<longrightarrow> length y1 = length y2))" in allE')
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="w1"
      in allE)
  apply(erule_tac
      x="w1a"
      in allE)
  apply(erule_tac
      x="w2"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="w2a"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="\<alpha>1@w1"
      in meta_allE)
  apply(erule_tac
      x="\<alpha>2@w1a"
      in meta_allE)
  apply(erule_tac
      x="w2@\<beta>1"
      in meta_allE)
  apply(erule_tac
      x="w2a@\<beta>2"
      in meta_allE)
  apply(erule_tac
      x="\<pi>2"
      in meta_allE)
  apply(erule_tac
      x="\<pi>3"
      in meta_allE)
  apply(erule_tac meta_impE)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(rule_tac
      t="\<pi>1"
      and s="drop(Suc 0)(a#\<pi>1)"
      in ssubst)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
    apply(force)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(rule cfgLM.trans_der_skip)
      apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
      apply(force)
     apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
     apply(force)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
    apply(clarsimp)
    apply(simp add: simpY)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(rule_tac
      t="\<pi>2@\<pi>3"
      and s="drop(Suc 0)(b#\<pi>2@\<pi>3)"
      in ssubst)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
    apply(force)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(rule cfgLM.trans_der_skip)
      apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
      apply(force)
     apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
     apply(force)
    apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
    apply(clarsimp)
    apply(simp add: simpY)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a k x1 x2 y1 y2)(*strict*)
   apply(erule_tac
      x="Suc k"
      and P="\<lambda>X. X < Suc (length \<pi>2) \<longrightarrow> (\<forall>x1 x2 y1. prod_rhs ((a # \<pi>1) ! X) = liftB x1 @ liftA y1 \<longrightarrow> (\<forall>y2. prod_rhs ((b # \<pi>2) ! X) = liftB x2 @ liftA y2 \<longrightarrow> length y1 = length y2))"
      in allE)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a k x1 x2 y1 y2)(*strict*)
   apply(clarsimp)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a k x1 x2 y1)(*strict*)
   apply(erule_tac
      x="Suc k"
      and P="\<lambda>x. x < Suc (length \<pi>2) \<longrightarrow> (\<forall>x1 x2 y1. prod_rhs ((a # \<pi>1) ! x) = liftB x1 @ liftA y1 \<longrightarrow> prod_rhs ((b # \<pi>2) ! x) = liftB x2 @ liftA y1 \<longrightarrow> (a # \<pi>1) ! x = (b # \<pi>2) ! x)"
      in allE)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a k x1 x2 y1)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
   apply(force)
  apply(rename_tac a \<pi>1 d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>1 \<beta>2 w1 w2 w1a w2a)(*strict*)
  apply(clarsimp)
  apply(rename_tac a d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>2 w1 w1a w2a)(*strict*)
  apply(erule_tac
      x="0"
      and P="\<lambda>x. x < Suc (length \<pi>2) \<longrightarrow> (\<forall>x1 x2 y1. prod_rhs ((a # \<pi>2) ! x) = liftB x1 @ liftA y1 \<longrightarrow> prod_rhs ((b # \<pi>2) ! x) = liftB x2 @ liftA y1 \<longrightarrow> (a # \<pi>2) ! x = (b # \<pi>2) ! x)"
      in allE)
  apply(rename_tac a d1 d2 \<alpha>1 \<alpha>2 \<pi>3 b \<pi>2 \<beta>2 w1 w1a w2a)(*strict*)
  apply(clarsimp)
  apply(force)
  done

end

