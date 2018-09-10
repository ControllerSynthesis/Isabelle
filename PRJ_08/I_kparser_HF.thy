section {*I\_kparser\_HF*}
theory
  I_kparser_HF

imports
  I_kparser_base

begin

record ('stack, 'event) parserHF_conf =
  parserHF_conf_fixed :: "'event list"
  parserHF_conf_history :: "'event list"
  parserHF_conf_stack :: "'stack list"

definition parserHF_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf set"
  where
    "parserHF_configurations G \<equiv>
  {\<lparr>parserHF_conf_fixed = f,
    parserHF_conf_history=h,
    parserHF_conf_stack = l\<rparr>
    | f h l.
    set l \<subseteq> parser_nonterms G
    \<and> set f \<subseteq> parser_events G
    \<and> set h \<subseteq> parser_events G
    \<and> parser_bottom G \<notin> set h
    \<and> suffix h (butlast_if_match f (parser_bottom G))
    \<and> (parser_bottom G \<notin> set f
        \<or> (\<exists>w. f = w @ [parser_bottom G]
                \<and> parser_bottom G \<notin> set w))}"

definition parserHF_configurations_ALT :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf set"
  where
    "parserHF_configurations_ALT G \<equiv>
  {\<lparr>parserHF_conf_fixed = f,
    parserHF_conf_history=h,
    parserHF_conf_stack = l\<rparr>
    | f h l.
    set l \<subseteq> parser_nonterms G
    \<and> set h \<subseteq> parser_events G - {parser_bottom G}
    \<and> suffix h (butlast_if_match f (parser_bottom G))
    \<and> f \<in> parser_fixed_schedulers G}"

lemma parserHF_configurations_ALT_vs_parserHF_configurations: "
  valid_parser G
  \<Longrightarrow> parserHF_configurations_ALT G = parserHF_configurations G"
  apply(simp add: parserHF_configurations_ALT_def parserHF_configurations_def)
  apply(rule antisym)
   prefer 2
   apply(clarsimp)
   apply(rename_tac f h l)(*strict*)
   apply(case_tac "parser_bottom G \<in> set f")
    apply(rename_tac f h l)(*strict*)
    apply(simp add: parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac h l w)(*strict*)
    apply(rule conjI)
     apply(rename_tac h l w)(*strict*)
     apply(force)
    apply(rename_tac h l w)(*strict*)
    apply(simp add: parser_fixed_schedulers_def prefix_closure_def)
    apply(rule_tac x="w @ [parser_bottom G]" in exI)
    apply(rule conjI)
     apply(rename_tac h l w)(*strict*)
     prefer 2
     apply(simp add: prefix_def)
    apply(rename_tac h l w)(*strict*)
    apply(simp add: parser_schedulers_def)
   apply(rename_tac f h l)(*strict*)
   apply(rule conjI)
    apply(rename_tac f h l)(*strict*)
    apply(force)
   apply(rename_tac f h l)(*strict*)
   apply(simp add: parser_fixed_schedulers_def)
   apply(simp add: prefix_closure_def parser_schedulers_def)
   apply(rule_tac
      x="f@ [parser_bottom G]"
      in exI)
   apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac f h l)(*strict*)
  apply(simp add: parser_fixed_schedulers_def)
  apply(simp add: prefix_closure_def parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac f h l va)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac f h l va c)(*strict*)
  apply(rule conjI)
   apply(rename_tac f h l va c)(*strict*)
   apply(simp add: valid_parser_def)
   apply(clarsimp)
   apply(rename_tac f h l va c x)(*strict*)
   apply(subgoal_tac "x\<in> set(va @ [parser_bottom G])")
    apply(rename_tac f h l va c x)(*strict*)
    prefer 2
    apply(rule_tac
      A="set f"
      in set_mp)
     apply(rename_tac f h l va c x)(*strict*)
     apply(rule_tac
      t="va @ [parser_bottom G]"
      and s="f @ c"
      in ssubst)
      apply(rename_tac f h l va c x)(*strict*)
      apply(force)
     apply(rename_tac f h l va c x)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac f h l va c x)(*strict*)
    apply(force)
   apply(rename_tac f h l va c x)(*strict*)
   apply(force)
  apply(rename_tac f h l va c)(*strict*)
  apply(rule conjI)
   apply(rename_tac f h l va c)(*strict*)
   apply(force)
  apply(rename_tac f h l va c)(*strict*)
  apply(rule conjI)
   apply(rename_tac f h l va c)(*strict*)
   apply(force)
  apply(rename_tac f h l va c)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      xs="c"
      in rev_cases)
   apply(rename_tac f h l va c)(*strict*)
   apply(clarsimp)
  apply(rename_tac f h l va c ys y)(*strict*)
  apply(clarsimp)
  done

definition parserHF_step_relation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation G c1 p c2 \<equiv>
  p \<in> parser_rules G \<and> ((\<exists>x. parserHF_conf_stack c1=x@(rule_lpop p) \<and> parserHF_conf_stack c2=x@(rule_lpush p)) \<and> (parserHF_conf_history c2=parserHF_conf_history c1@(drop (length(parserHF_conf_fixed c1)) (butlast_if_match (rule_rpop p) (parser_bottom G))) \<and> parserHF_conf_fixed c2 = (rule_rpush p) @ (drop (length (rule_rpop p)) (parserHF_conf_fixed c1)) \<and> (prefix (rule_rpop p) (parserHF_conf_fixed c1) \<or> prefix (parserHF_conf_fixed c1) (rule_rpop p))))"

definition parserHF_step_relation_ALT :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT G c1 e c2 \<equiv>
  e \<in> parser_rules G
  \<and> (\<exists>x. parserHF_conf_stack c1 = x @ rule_lpop e
          \<and> parserHF_conf_stack c2 = x @ rule_lpush e)
  \<and> parserHF_conf_history c2
      = parserHF_conf_history c1
        @ drop
            (length(parserHF_conf_fixed c1))
            (butlast_if_match (rule_rpop e) (parser_bottom G))
  \<and> parserHF_conf_fixed c2
      = rule_rpush e
        @ drop
            (length (rule_rpop e))
            (parserHF_conf_fixed c1)
  \<and> (prefix (rule_rpop e) (parserHF_conf_fixed c1)
    \<or> prefix (parserHF_conf_fixed c1) (rule_rpop e))"

lemma parserHF_step_relation_ALT_vs_parserHF_step_relation: "
  parserHF_step_relation_ALT M c1 p c2 = parserHF_step_relation M c1 p c2"
  apply(simp add: parserHF_step_relation_ALT_def parserHF_step_relation_def)
  done

(*1a 1b 1c not fixed before AND not fixed afterwards*)
definition parserHF_step_relation_ALT2_1a :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT2_1a G c1 e c2 \<equiv>
    (\<exists>v1 v2 v3 h s s1 q1 s2 q2.
        c1 = \<lparr>parserHF_conf_fixed = v1, parserHF_conf_history = h, parserHF_conf_stack = s @ s1 @ [q1]\<rparr>
      \<and> e = \<lparr>rule_lpop = s1 @ [q1], rule_rpop = v1 @ v2 @ v3, rule_lpush = s2 @ [q2], rule_rpush = v3\<rparr>
      \<and> c2 = \<lparr>parserHF_conf_fixed = v3, parserHF_conf_history = h @ v2 @ v3, parserHF_conf_stack = s @ s2 @ [q2]\<rparr>
      \<and> parser_bottom G \<notin> set (v1 @ v2 @ v3))"

definition parserHF_step_relation_ALT2_1b :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT2_1b G c1 e c2 \<equiv>
    (\<exists>v1 v2 v3 h s s1 q1 s2 q2.
        c1 = \<lparr>parserHF_conf_fixed = v1 @ v2, parserHF_conf_history = h, parserHF_conf_stack = s @ s1 @ [q1]\<rparr>
      \<and> e = \<lparr>rule_lpop = s1 @ [q1], rule_rpop = v1 @ v2 @ v3, rule_lpush = s2 @ [q2], rule_rpush = v2 @ v3\<rparr>
      \<and> c2 = \<lparr>parserHF_conf_fixed = v2 @ v3, parserHF_conf_history = h @ v3, parserHF_conf_stack = s @ s2 @ [q2]\<rparr>
      \<and> parser_bottom G \<notin> set (v1 @ v2 @ v3))"

definition parserHF_step_relation_ALT2_1c :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT2_1c G c1 e c2 \<equiv>
    (\<exists>v1 v2 v3 h s s1 q1 s2 q2.
        c1 = \<lparr>parserHF_conf_fixed = v1 @ v2 @ v3, parserHF_conf_history = h, parserHF_conf_stack = s @ s1 @ [q1]\<rparr>
      \<and> e = \<lparr>rule_lpop = s1 @ [q1], rule_rpop = v1 @ v2, rule_lpush = s2 @ [q2], rule_rpush = v2\<rparr>
      \<and> c2 = \<lparr>parserHF_conf_fixed = v2 @ v3, parserHF_conf_history = h, parserHF_conf_stack = s @ s2 @ [q2]\<rparr>
      \<and> parser_bottom G \<notin> set (v1 @ v2 @ v3))"

(*2a 2b not fixed before but fixed afterwards*)
definition parserHF_step_relation_ALT2_2a :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT2_2a G c1 e c2 \<equiv>
    (\<exists>v1 v2 v3 h s s1 q1 s2 q2.
        c1 = \<lparr>parserHF_conf_fixed = v1, parserHF_conf_history = h, parserHF_conf_stack = s @ s1 @ [q1]\<rparr>
      \<and> e = \<lparr>rule_lpop = s1 @ [q1], rule_rpop = v1 @ v2 @ v3 @ [parser_bottom G], rule_lpush = s2 @ [q2], rule_rpush = v3 @ [parser_bottom G]\<rparr>
      \<and> c2 = \<lparr>parserHF_conf_fixed = v3 @ [parser_bottom G], parserHF_conf_history = h @ v2 @ v3, parserHF_conf_stack = s @ s2 @ [q2]\<rparr>
      \<and> parser_bottom G \<notin> set (v1 @ v2 @ v3))"

definition parserHF_step_relation_ALT2_2b :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT2_2b G c1 e c2 \<equiv>
    (\<exists>v1 v2 v3 h s s1 q1 s2 q2.
        c1 = \<lparr>parserHF_conf_fixed = v1 @ v2, parserHF_conf_history = h, parserHF_conf_stack = s @ s1 @ [q1]\<rparr>
      \<and> e = \<lparr>rule_lpop = s1 @ [q1], rule_rpop = v1 @ v2 @ v3 @ [parser_bottom G], rule_lpush = s2 @ [q2], rule_rpush = v2 @ v3 @ [parser_bottom G]\<rparr>
      \<and> c2 = \<lparr>parserHF_conf_fixed = v2 @ v3 @ [parser_bottom G], parserHF_conf_history = h @ v3, parserHF_conf_stack = s @ s2 @ [q2]\<rparr>
      \<and> parser_bottom G \<notin> set (v1 @ v2 @ v3))"

(*3a 3b fixed before*)
definition parserHF_step_relation_ALT2_3a :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT2_3a G c1 e c2 \<equiv>
    (\<exists>v1 v2 v3 h s s1 q1 s2 q2.
        c1 = \<lparr>parserHF_conf_fixed = v1 @ v2 @ v3 @ [parser_bottom G], parserHF_conf_history = h, parserHF_conf_stack = s @ s1 @ [q1]\<rparr>
      \<and> e = \<lparr>rule_lpop = s1 @ [q1], rule_rpop = v1 @ v2, rule_lpush = s2 @ [q2], rule_rpush = v2\<rparr>
      \<and> c2 = \<lparr>parserHF_conf_fixed = v2 @ v3 @ [parser_bottom G], parserHF_conf_history = h, parserHF_conf_stack = s @ s2 @ [q2]\<rparr>
      \<and> parser_bottom G \<notin> set (v1 @ v2 @ v3))"

definition parserHF_step_relation_ALT2_3b :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT2_3b G c1 e c2 \<equiv>
    (\<exists>v1 v2 h s s1 q1 s2 q2.
        c1 = \<lparr>parserHF_conf_fixed = v1 @ v2 @ [parser_bottom G], parserHF_conf_history = h, parserHF_conf_stack = s @ s1 @ [q1]\<rparr>
      \<and> e = \<lparr>rule_lpop = s1 @ [q1], rule_rpop = v1 @ v2 @ [parser_bottom G], rule_lpush = s2 @ [q2], rule_rpush = v2 @ [parser_bottom G]\<rparr>
      \<and> c2 = \<lparr>parserHF_conf_fixed = v2 @ [parser_bottom G], parserHF_conf_history = h, parserHF_conf_stack = s @ s2 @ [q2]\<rparr>
      \<and> parser_bottom G \<notin> set (v1 @ v2))"

definition parserHF_step_relation_ALT2 :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHF_conf
  \<Rightarrow> bool"
  where
    "parserHF_step_relation_ALT2 G c1 e c2 \<equiv>
  e \<in> parser_rules G
  \<and> (
      parserHF_step_relation_ALT2_1a G c1 e c2
    \<or> parserHF_step_relation_ALT2_1b G c1 e c2
    \<or> parserHF_step_relation_ALT2_1c G c1 e c2
    \<or> parserHF_step_relation_ALT2_2a G c1 e c2
    \<or> parserHF_step_relation_ALT2_2b G c1 e c2
    \<or> parserHF_step_relation_ALT2_3a G c1 e c2
    \<or> parserHF_step_relation_ALT2_3b G c1 e c2
    )"

lemma parserHF_step_relation_ALT2_1a_intro: "
  e \<in> parser_rules G \<Longrightarrow> parserHF_step_relation_ALT2_1a G c1 e c2 \<Longrightarrow> parserHF_step_relation_ALT2 G c1 e c2"
  apply(simp add: parserHF_step_relation_ALT2_def)
  done

lemma parserHF_step_relation_ALT2_2b_intro: "
  e \<in> parser_rules G \<Longrightarrow> parserHF_step_relation_ALT2_2b G c1 e c2 \<Longrightarrow> parserHF_step_relation_ALT2 G c1 e c2"
  apply(simp add: parserHF_step_relation_ALT2_def)
  done

lemma parserHF_step_relation_ALT2_1b_intro: "
  e \<in> parser_rules G \<Longrightarrow> parserHF_step_relation_ALT2_1b G c1 e c2 \<Longrightarrow> parserHF_step_relation_ALT2 G c1 e c2"
  apply(simp add: parserHF_step_relation_ALT2_def)
  done

lemma parserHF_step_relation_ALT2_1c_intro: "
  e \<in> parser_rules G \<Longrightarrow> parserHF_step_relation_ALT2_1c G c1 e c2 \<Longrightarrow> parserHF_step_relation_ALT2 G c1 e c2"
  apply(simp add: parserHF_step_relation_ALT2_def)
  done

lemma parserHF_step_relation_ALT2_2a_intro: "
  e \<in> parser_rules G \<Longrightarrow> parserHF_step_relation_ALT2_2a G c1 e c2 \<Longrightarrow> parserHF_step_relation_ALT2 G c1 e c2"
  apply(simp add: parserHF_step_relation_ALT2_def)
  done

lemma parserHF_step_relation_ALT2_3b_intro: "
  e \<in> parser_rules G \<Longrightarrow> parserHF_step_relation_ALT2_3b G c1 e c2 \<Longrightarrow> parserHF_step_relation_ALT2 G c1 e c2"
  apply(simp add: parserHF_step_relation_ALT2_def)
  done

lemma parserHF_step_relation_ALT2_3a_intro: "
  e \<in> parser_rules G \<Longrightarrow> parserHF_step_relation_ALT2_3a G c1 e c2 \<Longrightarrow> parserHF_step_relation_ALT2 G c1 e c2"
  apply(simp add: parserHF_step_relation_ALT2_def)
  done

lemma parserHF_step_relation_ALT2__vs__parserHF_step_relation_ALT: "
  valid_parser G
  \<Longrightarrow> c1 \<in> parserHF_configurations G
  \<Longrightarrow> parserHF_step_relation_ALT2 G c1 e c2 = parserHF_step_relation_ALT G c1 e c2"
  apply(rule antisym)
   apply(simp add: parserHF_step_relation_ALT2_def parserHF_step_relation_ALT_def)
   apply(clarsimp)
   apply(erule disjE) 
    apply(simp add: parserHF_step_relation_ALT2_1a_def)
    apply(clarsimp)
    apply (metis append_Nil2 butlast_if_match_direct2_prime butlast_if_match_pull_out drop_butlast_if_match_distrib prefix_append)
   apply(erule disjE) 
    apply(simp add: parserHF_step_relation_ALT2_1b_def)
    apply(clarsimp)
    apply (metis append_assoc butlast_if_match_direct2_prime drop_butlast_if_match_distrib length_append prefix_append)
   apply(erule disjE) 
    apply(simp add: parserHF_step_relation_ALT2_1c_def)
    apply(clarsimp)
    apply (metis append_assoc butlast_if_match_direct2_prime drop_length_append length_append not_set_append prefix_append)
   apply(erule disjE) 
    apply(simp add: parserHF_step_relation_ALT2_2a_def)
    apply(clarsimp)
    apply (metis append_assoc butlast_if_match_direct drop_butlast_if_match_distrib length_append prefix_append)    
   apply(erule disjE)
    apply(simp add: parserHF_step_relation_ALT2_2b_def)
    apply(clarsimp)
    apply (metis append_assoc butlast_if_match_direct drop_butlast_if_match_distrib length_append prefix_append)    
   apply(erule disjE)
    apply(simp add: parserHF_step_relation_ALT2_3a_def)
    apply(clarsimp)
    apply(rule conjI)
     apply (metis append_assoc append_self_conv butlast_if_match_direct2_prime butlast_if_match_pull_out drop_length_append le_SucI length_append)
    apply (metis append_assoc prefix_def)
   apply(simp add: parserHF_step_relation_ALT2_3b_def)
   apply(clarsimp)
   apply(rule conjI)
    apply (metis add_Suc_right butlast_if_match_length_le length_Suc length_append)
   apply(simp add: prefix_def)
  apply(clarsimp)
  apply(simp add: parserHF_step_relation_ALT_def)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label G e")
   prefer 2
   apply (metis valid_parser_def)
  apply(case_tac c1)
  apply(rename_tac f1 h1 s1)
  apply(case_tac c2)
  apply(rename_tac f2 h2 s2)
  apply(case_tac e)
  apply(rename_tac lpop rpop lpush rpush)
  apply(clarsimp)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(subgoal_tac "drop (length rpop + length c) (butlast_if_match rpop (parser_bottom G)) = []")
    prefer 2
    apply (metis drop_entire_butlast_if_match drop_length_append length_append)  
   apply(clarsimp)
   apply(thin_tac "length (butlast_if_match rpop (parser_bottom G)) \<le> length rpop + length c")
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rule_tac xs="lpop" in rev_cases)
    apply(force)
   apply(clarsimp)
   apply(rule_tac xs="lpush" in rev_cases)
    apply(force)
   apply(clarsimp)
   apply(case_tac "\<exists>w'. kPrefix k (w @ [parser_bottom G]) @ c = w'@[parser_bottom G]")
    prefer 2
    apply(clarsimp)
    apply(case_tac "k \<le> length w")
     prefer 2
     apply(simp add: parserHF_configurations_def)
     apply(simp add: kPrefix_def)
    apply(simp add: kPrefix_def)
    apply(rule parserHF_step_relation_ALT2_1c_intro)
     apply(force)
    apply(simp add: parserHF_step_relation_ALT2_1c_def)
    apply(rule_tac x="xb" in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply (metis append_same_eq append_take_drop_id drop_prefix_closureise set_take_subset subsetD triv_compl)
    apply(rule conjI)
     apply (metis (no_types, hide_lams) Diff_iff Un_iff all_not_in_conv empty_subsetI insert_subset set_append set_take_subset subsetD)
    apply(simp add: parserHF_configurations_def)
   apply(clarsimp)
   apply(rule_tac xs="c" in rev_cases)
    prefer 2
    apply(clarsimp)
    apply(rule parserHF_step_relation_ALT2_3a_intro)
     apply(force)
    apply(rule_tac t="kPrefix k (w @ [parser_bottom G])" and s="xb @ rpush" in ssubst)
     apply(force)
    apply(simp add: parserHF_step_relation_ALT2_3a_def)
    apply(rule_tac x="xb" in exI)
    apply(clarsimp)
    apply(case_tac "k \<le> length w")
     apply(simp add: parserHF_configurations_def)
     apply(simp add: kPrefix_def)
     apply (metis Un_iff set_append)
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(simp add: parserHF_configurations_def)
   apply(clarsimp)
   apply(case_tac "k \<le> length w")
    apply(simp add: kPrefix_def)
    apply (metis Un_iff insertCI set_append set_simps(2) set_take_subset subset_trans triv_compl)
   apply(simp add: kPrefix_def)
   apply(clarsimp)
   apply(rule parserHF_step_relation_ALT2_3b_intro)
    apply(force)  
   apply(simp add: parserHF_step_relation_ALT2_3b_def)
   apply (metis triv_compl)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(subgoal_tac "drop (length f1) (butlast_if_match (f1 @ c) (parser_bottom G)) = butlast_if_match c (parser_bottom G)")
   prefer 2
   apply (metis drop_butlast_if_match_distrib)
  apply(clarsimp)
  apply(thin_tac "drop (length f1) (butlast_if_match (f1 @ c) (parser_bottom G)) =
       butlast_if_match c (parser_bottom G)")
  apply(case_tac "\<exists>c'. c = c' @[parser_bottom G]")
   apply(clarsimp)
   apply(subgoal_tac "butlast_if_match (c' @ [parser_bottom G]) (parser_bottom G) = c'")
    prefer 2
    apply (metis butlast_if_match_direct)
   apply(clarsimp)
   apply(thin_tac "butlast_if_match (c' @ [parser_bottom G]) (parser_bottom G) = c'")
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rule_tac xs="lpop" in rev_cases)
    apply(force)
   apply(clarsimp)
   apply(rule_tac xs="lpush" in rev_cases)
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "f1@c'=xb@xc") 
    prefer 2
    apply (metis append1_eq_conv append_assoc)
   apply(subgoal_tac "prefix f1 xb \<or> prefix xb f1")
    prefer 2
    apply (metis mutual_prefix_prefix)
   apply(erule disjE)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(case_tac "k \<le> length w")
     apply(simp add: kPrefix_def)
     apply(subgoal_tac "parser_bottom G \<in> set w")
      apply(force)
     apply(rule_tac A="set (take k w)" in set_mp)
      apply(rule set_take_subset)
     apply(rule_tac A="set (f1 @ c @ xc @ [parser_bottom G])" in set_mp)
      apply(force)
     apply(simp (no_asm))
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(rule parserHF_step_relation_ALT2_2a_intro)
     apply(force)
    apply(rename_tac s v1 h k v3 s1 q1 s2 q2 v2)
    apply(simp add: parserHF_step_relation_ALT2_2a_def)
    apply(force)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(case_tac "k \<le> length w")
    apply(simp add: kPrefix_def)  
    apply(subgoal_tac "parser_bottom G \<in> set w")
     apply(force)
    apply(rule_tac A="set (take k w)" in set_mp)
     apply(rule set_take_subset)
    apply(rule_tac A="set (xb @ c @ c' @ [parser_bottom G])" in set_mp)
     apply(force)
    apply(simp (no_asm))
   apply(simp add: kPrefix_def)
   apply(clarsimp)
   apply(rename_tac s h v3 k v1 s1 q1 s2 q2 v2)
   apply(rule parserHF_step_relation_ALT2_2b_intro)
    apply(force)
   apply(simp add: parserHF_step_relation_ALT2_2b_def)
   apply (metis triv_compl)
  apply(clarsimp)
  apply(rule_tac xs="c" in rev_cases)
   apply(clarsimp)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rule_tac xs="lpop" in rev_cases)
    apply(force)
   apply(clarsimp)
   apply(rule_tac xs="lpush" in rev_cases)
    apply(force)
   apply(clarsimp)
   apply(simp add: butlast_if_match_def) 
   apply(case_tac "k \<le> length w")
    apply(simp add: kPrefix_def)
    apply(subgoal_tac "\<exists>w'. w =xb@rpush @w' \<and> length (xb@rpush) = k")
     prefer 2
     apply(rule_tac x="drop k w" in exI)
     apply(rule conjI)
      apply (metis append_assoc append_take_drop_id)
     apply (metis take_all_length)
    apply(rule_tac t="take k w" and s="xb@rpush" in ssubst)  
     apply(force)
    apply(thin_tac "xb @ rpush = take k w")
    apply(clarsimp)
    apply(rule parserHF_step_relation_ALT2_1c_intro)
     apply(force)
    apply(simp add: parserHF_step_relation_ALT2_1c_def)  
    apply (metis triv_compl)  
   apply(simp add: kPrefix_def)
   apply(clarsimp)
   apply(rename_tac s h k v1 s1 q1 s2 q2 v2)
   apply(rule parserHF_step_relation_ALT2_3b_intro)
    apply(force)
   apply(simp add: parserHF_step_relation_ALT2_3b_def)
   apply (metis triv_compl)
  apply(clarsimp)
  apply(subgoal_tac "butlast_if_match (ys @ [y]) (parser_bottom G) =ys@[y]")
   prefer 2
   apply (metis butlast_if_match_direct2)
  apply(clarsimp)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(thin_tac "butlast_if_match (ys @ [y]) (parser_bottom G) = ys @ [y]")
  apply(case_tac "k \<le> length w")
   prefer 2
   apply(simp add: kPrefix_def)
  apply(simp add: kPrefix_def)
  apply(subgoal_tac "\<exists>w'. w =f1 @ ys @ [y] @w' \<and> length (f1 @ ys @ [y]) = k")
   prefer 2
   apply(rule_tac x="drop k w" in exI)
   apply(rule conjI)
    apply (metis append_assoc append_take_drop_id)
   apply (metis take_all_length)
  apply(rule_tac t="take k w" and s="f1 @ ys @ [y]" in ssubst)  
   apply(force)
  apply(thin_tac "f1 @ ys @ [y] = take k w")
  apply(clarsimp)
  apply(rule_tac xs="lpop" in rev_cases)
   apply(force)
  apply(clarsimp)
  apply(rule_tac xs="lpush" in rev_cases)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "prefix f1 xb \<or> prefix xb f1")
   prefer 2
   apply (metis mutual_prefix_prefix)
  apply(erule disjE)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rule_tac xs="rpush" in rev_cases)
    apply(clarsimp)
    apply(rule parserHF_step_relation_ALT2_1a_intro)
     apply(force)
    apply(simp add: parserHF_step_relation_ALT2_1a_def)
    apply(force)
   apply(clarsimp)
   apply(rule parserHF_step_relation_ALT2_1a_intro)
    apply(force)
   apply(simp add: parserHF_step_relation_ALT2_1a_def)
   apply(force)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac s h v3a v3b v1 w' s1 q1 s2 q2 v2)
  apply(rule parserHF_step_relation_ALT2_1b_intro)
   apply(force)
  apply(simp add: parserHF_step_relation_ALT2_1b_def)
  apply(force)
  done


definition parserHF_initial_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf set"
  where
    "parserHF_initial_configurations G \<equiv>
  {c. parserHF_conf_history c = []
      \<and> parserHF_conf_fixed c = []
      \<and> parserHF_conf_stack c = [parser_initial G]}
  \<inter> parserHF_configurations G"

definition parserHF_marking_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHF_conf set"
  where
    "parserHF_marking_configurations G \<equiv>
  {c. \<exists>f \<in> parser_marking G. \<exists>w.
      parserHF_conf_stack c = w @ [f]
      \<and> parserHF_conf_fixed c \<in> {[], [parser_bottom G]}}
  \<inter> parserHF_configurations G"

definition parserHF_marking_condition :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHF_conf)derivation
  \<Rightarrow> bool"
  where
    "parserHF_marking_condition G d \<equiv>
  \<exists>i e c.
    d i = Some (pair e c)
    \<and> c \<in> parserHF_marking_configurations G
    \<and> (\<forall>j e' c'.
        j > i
        \<and> d j = Some(pair e' c')
        \<longrightarrow> parserHF_conf_history c = parserHF_conf_history c')"

definition parserHF_marked_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHF_conf)derivation
  \<Rightarrow> 'event list set"
  where
    "parserHF_marked_effect G d \<equiv>
  {w. \<exists>i e c.
      d i = Some (pair e c)
      \<and> w = parserHF_conf_history c
      \<and> c \<in> parserHF_marking_configurations G}"

definition parserHF_unmarked_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHF_conf)derivation
  \<Rightarrow> 'event list set"
  where
    "parserHF_unmarked_effect G d \<equiv>
  {w. \<exists>i e c.
      d i = Some (pair e c)
      \<and> parserHF_conf_history c = w}"

definition parserHF_get_destinations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHF_conf)derivation_configuration
  \<Rightarrow> ('stack, 'event) parser_destinations set"
  where
    "parserHF_get_destinations G der_conf \<equiv>
  case der_conf of pair e c \<Rightarrow>
    state ` set (parserHF_conf_stack c)
    \<union> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {rule e'})"

lemma parserHF_inst_AX_initial_configuration_belongs: "
  (\<forall>G. valid_parser G \<longrightarrow> parserHF_initial_configurations G \<subseteq> parserHF_configurations G)"
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: parserHF_initial_configurations_def)
  done

lemma parserHF_inst_AX_step_relation_preserves_belongs: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1 e c2. parserHF_step_relation G c1 e c2 \<longrightarrow> c1 \<in> parserHF_configurations G \<longrightarrow> e \<in> parser_step_labels G \<and> c2 \<in> parserHF_configurations G))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(simp add: parser_step_labels_def parserHF_step_relation_def)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(simp add: parserHF_configurations_def)
  apply(clarsimp)
  apply(rename_tac G e c2 f h l)(*strict*)
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G e c2 f h x)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G e c2 f h x parserHF_conf_fixeda parserHF_conf_historya parserHF_conf_stacka)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e f h x)(*strict*)
  apply(simp add: parser_step_labels_def)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G e f h x)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac G e f h x)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G e f h x)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac G e f h x)(*strict*)
  apply(subgoal_tac "set (rule_rpush e) \<subseteq> parser_events G")
   apply(rename_tac G e f h x)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac G e f h x)(*strict*)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G e f h x)(*strict*)
   apply(metis set_drop_subset subset_trans)
  apply(rename_tac G e f h x)(*strict*)
  apply(subgoal_tac "set (rule_rpop e) \<subseteq> parser_events G")
   apply(rename_tac G e f h x)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G e f h x xa k w xc)(*strict*)
   apply(rule_tac
      A="set (kPrefix k (w @ [parser_bottom G]))"
      in set_mp)
    apply(rename_tac G e f h x xa k w xc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G e f h x xa k w xc)(*strict*)
   apply(rule set_kPrefix_subset)
   apply(clarsimp)
   apply(simp add: valid_parser_def)
   apply(rule_tac
      B="parser_events G - {parser_bottom G}"
      in subset_trans)
    apply(rename_tac G e f h x xa k w xc)(*strict*)
    apply(force)
   apply(rename_tac G e f h x xa k w xc)(*strict*)
   apply(force)
  apply(rename_tac G e f h x)(*strict*)
  apply(subgoal_tac "set (drop (length f) (butlast_if_match (rule_rpop e) (parser_bottom G))) \<subseteq> set (rule_rpop e)")
   apply(rename_tac G e f h x)(*strict*)
   prefer 2
   apply(rule_tac
      B="set(butlast_if_match (rule_rpop e) (parser_bottom G))"
      in subset_trans)
    apply(rename_tac G e f h x)(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac G e f h x)(*strict*)
   apply(rule_tac
      B="set(rule_rpop e)"
      in subset_trans)
    apply(rename_tac G e f h x)(*strict*)
    apply(rule set_butlast_if_match_is_subset)
   apply(rename_tac G e f h x)(*strict*)
   apply(force)
  apply(rename_tac G e f h x)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G e f h x)(*strict*)
   apply(force)
  apply(rename_tac G e f h x)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G e f h x)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(case_tac "(\<exists>x. x @ rule_rpush e = rule_rpop e)")
    apply(rename_tac G e f h x)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f h x xa k w)(*strict*)
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(case_tac "k-length w")
     apply(rename_tac G e f h x xa k w)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
      apply(rename_tac G e f h x xa k w)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "parser_bottom G \<notin> set (drop (length f) (take k w))")
       apply(rename_tac G e f h x xa k w)(*strict*)
       apply(force)
      apply(rename_tac G e f h x xa k w)(*strict*)
      apply(rule_tac
      B="set(take k w)"
      in nset_mp)
       apply(rename_tac G e f h x xa k w)(*strict*)
       apply(rule set_drop_subset)
      apply(rename_tac G e f h x xa k w)(*strict*)
      apply(rule_tac
      B="set w"
      in nset_mp)
       apply(rename_tac G e f h x xa k w)(*strict*)
       apply(rule set_take_subset)
      apply(rename_tac G e f h x xa k w)(*strict*)
      apply(rule_tac
      A="parser_events G"
      in not_in_diff)
      apply(force)
     apply(rename_tac G e f h x xa k w)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(rule_tac
      B="set w"
      in nset_mp)
      apply(rename_tac G e f h x xa k w)(*strict*)
      apply(rule set_take_subset)
     apply(rename_tac G e f h x xa k w)(*strict*)
     apply(rule_tac
      A="parser_events G"
      in not_in_diff)
     apply(force)
    apply(rename_tac G e f h x xa k w nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f h x xa k w nat xb)(*strict*)
    apply(subgoal_tac "butlast_if_match (w @ [parser_bottom G]) (parser_bottom G) = w")
     apply(rename_tac G e f h x xa k w nat xb)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<notin> set (drop (length f) w)")
      apply(rename_tac G e f h x xa k w nat xb)(*strict*)
      apply(force)
     apply(rename_tac G e f h x xa k w nat xb)(*strict*)
     apply(rule_tac
      B="set w"
      in nset_mp)
      apply(rename_tac G e f h x xa k w nat xb)(*strict*)
      apply(rule set_drop_subset)
     apply(rename_tac G e f h x xa k w nat xb)(*strict*)
     apply(rule_tac
      A="parser_events G"
      in not_in_diff)
     apply(force)
    apply(rename_tac G e f h x xa k w nat xb)(*strict*)
    apply(rule butlast_if_match_direct)
    apply(force)
   apply(rename_tac G e f h x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G e f h x)(*strict*)
  apply(rule propSym)
  apply(subgoal_tac "\<exists>w. rule_rpop e = w @ (rule_rpush e)")
   apply(rename_tac G e f h x)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G e f h x k w xb)(*strict*)
   apply(simp add: kPrefix_def)
   apply(rule_tac
      x="xb"
      in exI)
   apply(force)
  apply(rename_tac G e f h x)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e f h x w)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G e f h x w)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G e f h x w)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e h x w c wa)(*strict*)
    apply(subgoal_tac "prefix w wa \<or> prefix wa w")
     apply(rename_tac G e h x w c wa)(*strict*)
     apply(erule disjE)
      apply(rename_tac G e h x w c wa)(*strict*)
      apply(simp add: prefix_def)
      apply(clarsimp)
     apply(rename_tac G e h x w c wa)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac G e h x c wa ca)(*strict*)
     apply(case_tac ca)
      apply(rename_tac G e h x c wa ca)(*strict*)
      apply(clarsimp)
     apply(rename_tac G e h x c wa ca a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac G e h x w c wa)(*strict*)
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac G e f h x w)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e f h x w c)(*strict*)
   apply(subgoal_tac "drop (length w + length (rule_rpush e)) f = []")
    apply(rename_tac G e f h x w c)(*strict*)
    apply(clarsimp)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac G e f h x w c k wa)(*strict*)
    apply(case_tac e)
    apply(rename_tac G e f h x w c k wa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(clarsimp)
    apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length wa")
     apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<notin> set rule_rpush")
      apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
      apply(force)
     apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
     apply(rule_tac
      B="set(w @ rule_rpush)"
      in nset_mp)
      apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
     apply(rule_tac
      B="set(take k wa)"
      in nset_mp)
      apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
      apply(simp (no_asm_simp))
     apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
     apply(rule_tac
      B="set wa"
      in nset_mp)
      apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
      apply(rule set_take_subset)
     apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush)(*strict*)
     apply(rule_tac
      A="parser_events G"
      in not_in_diff)
     apply(force)
    apply(rename_tac G f h x w c k wa rule_lpop rule_lpush rule_rpush nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G f h x w c k rule_lpop rule_lpush nat xa)(*strict*)
    apply(case_tac c)
     apply(rename_tac G f h x w c k rule_lpop rule_lpush nat xa)(*strict*)
     apply(clarsimp)
    apply(rename_tac G f h x w c k rule_lpop rule_lpush nat xa a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac G f h x w c k rule_lpop rule_lpush nat xa a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G f h x w c k rule_lpop rule_lpush nat xa a list)(*strict*)
    apply(thin_tac "c=a#list")
    apply(clarsimp)
    apply(rename_tac G f h x w k rule_lpop rule_lpush nat xa w')(*strict*)
    apply(subgoal_tac "parser_bottom G \<notin> set xa")
     apply(rename_tac G f h x w k rule_lpop rule_lpush nat xa w')(*strict*)
     apply(force)
    apply(rename_tac G f h x w k rule_lpop rule_lpush nat xa w')(*strict*)
    apply(rule_tac
      A="parser_events G"
      in not_in_diff)
    apply(force)
   apply(rename_tac G e f h x w c)(*strict*)
   apply(rule drop_all)
   apply(rule_tac
      j="length(w@rule_rpush e)"
      in le_trans)
    apply(rename_tac G e f h x w c)(*strict*)
    apply(rule_tac
      t="w@rule_rpush e"
      and s="f@c"
      in ssubst)
     apply(rename_tac G e f h x w c)(*strict*)
     apply(force)
    apply(rename_tac G e f h x w c)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac G e f h x w c)(*strict*)
   apply(force)
  apply(rename_tac G e f h x w)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G e f h x w)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<in> set f")
    apply(rename_tac G e f h x w)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e h x w wa)(*strict*)
    apply(case_tac "length w + length (rule_rpush e) - length wa")
     apply(rename_tac G e h x w wa)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<in> set wa")
      apply(rename_tac G e h x w wa)(*strict*)
      apply(force)
     apply(rename_tac G e h x w wa)(*strict*)
     apply(rule_tac
      A="set (drop (length w + length (rule_rpush e)) wa)"
      in set_mp)
      apply(rename_tac G e h x w wa)(*strict*)
      apply(rule set_drop_subset)
     apply(rename_tac G e h x w wa)(*strict*)
     apply(force)
    apply(rename_tac G e h x w wa nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e f h x w)(*strict*)
   apply(rule_tac
      A="set (drop (length w + length (rule_rpush e)) f)"
      in set_mp)
    apply(rename_tac G e f h x w)(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac G e f h x w)(*strict*)
   apply(force)
  apply(rename_tac G e f h x w)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G e f x w c)(*strict*)
  apply(case_tac "parser_bottom G \<in> set f")
   apply(rename_tac G e f x w c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e x w c wa)(*strict*)
   apply(rule_tac
      t="butlast_if_match (wa @ [parser_bottom G]) (parser_bottom G)"
      and s="wa"
      in ssubst)
    apply(rename_tac G e x w c wa)(*strict*)
    apply(rule butlast_if_match_direct)
    apply(force)
   apply(rename_tac G e x w c wa)(*strict*)
   apply(case_tac "length w + length (rule_rpush e) - length wa")
    apply(rename_tac G e x w c wa)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="butlast_if_match (rule_rpush e @ drop (length w + length (rule_rpush e)) wa @ [parser_bottom G]) (parser_bottom G)"
      and s="rule_rpush e @ drop (length w + length (rule_rpush e)) wa"
      in ssubst)
     apply(rename_tac G e x w c wa)(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac G e x w c wa)(*strict*)
    apply(erule disjE)
     apply(rename_tac G e x w c wa)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac G e x w c wa ca)(*strict*)
     apply(rule_tac
      t="drop (Suc (length wa)) (butlast_if_match (w @ rule_rpush e) (parser_bottom G))"
      and s="[]"
      in ssubst)
      apply(rename_tac G e x w c wa ca)(*strict*)
      apply(rule drop_all)
      apply(rule_tac
      j="length(w@rule_rpush e)"
      in le_trans)
       apply(rename_tac G e x w c wa ca)(*strict*)
       apply(rule butlast_if_match_length_le)
      apply(rename_tac G e x w c wa ca)(*strict*)
      apply(force)
     apply(rename_tac G e x w c wa ca)(*strict*)
     apply(clarsimp)
     apply(case_tac ca)
      apply(rename_tac G e x w c wa ca)(*strict*)
      apply(clarsimp)
      apply(rename_tac G e x w c wa)(*strict*)
      apply(rule_tac
      t="drop (length w + length (rule_rpush e)) wa"
      and s="[]"
      in ssubst)
       apply(rename_tac G e x w c wa)(*strict*)
       apply(rule drop_all)
       apply(rule_tac
      j="length(w@rule_rpush e)"
      in le_trans)
        apply(rename_tac G e x w c wa)(*strict*)
        apply(force)
       apply(rename_tac G e x w c wa)(*strict*)
       apply(simp (no_asm))
      apply(rename_tac G e x w c wa)(*strict*)
      apply(clarsimp)
      apply(case_tac "rule_rpush e")
       apply(rename_tac G e x w c wa)(*strict*)
       apply(clarsimp)
      apply(rename_tac G e x w c wa a list)(*strict*)
      apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
       apply(rename_tac G e x w c wa a list)(*strict*)
       prefer 2
       apply(rule NonEmptyListHasTailElem)
       apply(force)
      apply(rename_tac G e x w c wa a list)(*strict*)
      apply(thin_tac "rule_rpush e=a#list")
      apply(clarsimp)
     apply(rename_tac G e x w c wa ca a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
      apply(rename_tac G e x w c wa ca a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac G e x w c wa ca a list)(*strict*)
     apply(thin_tac "ca=a#list")
     apply(clarsimp)
    apply(rename_tac G e x w c wa)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e x w c wa ca)(*strict*)
    apply(subgoal_tac "prefix (wa@[parser_bottom G]) w \<or> prefix w (wa@[parser_bottom G])")
     apply(rename_tac G e x w c wa ca)(*strict*)
     prefer 2
     apply(rule mutual_prefix_prefix)
     apply(force)
    apply(rename_tac G e x w c wa ca)(*strict*)
    apply(erule disjE)
     apply(rename_tac G e x w c wa ca)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
    apply(rename_tac G e x w c wa ca)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e x w c wa ca cb)(*strict*)
    apply(case_tac cb)
     apply(rename_tac G e x w c wa ca cb)(*strict*)
     apply(clarsimp)
    apply(rename_tac G e x w c wa ca cb a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
     apply(rename_tac G e x w c wa ca cb a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x w c wa ca cb a list)(*strict*)
    apply(thin_tac "cb=a#list")
    apply(clarsimp)
    apply(rename_tac G e x w c ca w')(*strict*)
    apply(subgoal_tac "parser_bottom G \<in> set (rule_rpush e)")
     apply(rename_tac G e x w c ca w')(*strict*)
     apply(force)
    apply(rename_tac G e x w c ca w')(*strict*)
    apply(rule_tac
      t="rule_rpush e"
      and s="w' @ parser_bottom G # ca"
      in ssubst)
     apply(rename_tac G e x w c ca w')(*strict*)
     apply(force)
    apply(rename_tac G e x w c ca w')(*strict*)
    apply(simp (no_asm))
   apply(rename_tac G e x w c wa nat)(*strict*)
   apply(clarsimp)
   apply(case_tac "parser_bottom G \<in> set (rule_rpush e)")
    apply(rename_tac G e x w c wa nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x w c wa nat wb)(*strict*)
    apply(rule_tac
      t="butlast_if_match (wb @ [parser_bottom G]) (parser_bottom G)"
      and s="wb"
      in ssubst)
     apply(rename_tac G e x w c wa nat wb)(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac G e x w c wa nat wb)(*strict*)
    apply(rule_tac
      t="butlast_if_match (w @ wb @ [parser_bottom G]) (parser_bottom G)"
      and s="w@wb"
      in ssubst)
     apply(rename_tac G e x w c wa nat wb)(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac G e x w c wa nat wb)(*strict*)
    apply(erule disjE)
     apply(rename_tac G e x w c wa nat wb)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac G e x w c wa nat wb ca)(*strict*)
     apply(case_tac ca)
      apply(rename_tac G e x w c wa nat wb ca)(*strict*)
      apply(clarsimp)
     apply(rename_tac G e x w c wa nat wb ca a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
      apply(rename_tac G e x w c wa nat wb ca a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac G e x w c wa nat wb ca a list)(*strict*)
     apply(thin_tac "ca=a#list")
     apply(clarsimp)
    apply(rename_tac G e x w c wa nat wb)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e x w c wa nat wb ca)(*strict*)
    apply(case_tac ca)
     apply(rename_tac G e x w c wa nat wb ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac G e x w c wa nat wb ca a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
     apply(rename_tac G e x w c wa nat wb ca a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x w c wa nat wb ca a list)(*strict*)
    apply(thin_tac "ca=a#list")
    apply(clarsimp)
    apply(rename_tac G e x w c wa nat wb w')(*strict*)
    apply(subgoal_tac "prefix (wa@[parser_bottom G]) w \<or> prefix w (wa@[parser_bottom G])")
     apply(rename_tac G e x w c wa nat wb w')(*strict*)
     prefer 2
     apply(rule mutual_prefix_prefix)
     apply(force)
    apply(rename_tac G e x w c wa nat wb w')(*strict*)
    apply(erule disjE)
     apply(rename_tac G e x w c wa nat wb w')(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
    apply(rename_tac G e x w c wa nat wb w')(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e x w c wa nat wb w' ca)(*strict*)
    apply(case_tac ca)
     apply(rename_tac G e x w c wa nat wb w' ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac G e x w c wa nat wb w' ca a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
     apply(rename_tac G e x w c wa nat wb w' ca a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x w c wa nat wb w' ca a list)(*strict*)
    apply(thin_tac "ca=a#list")
    apply(clarsimp)
   apply(rename_tac G e x w c wa nat)(*strict*)
   apply(rule_tac
      t="butlast_if_match (rule_rpush e) (parser_bottom G)"
      and s="rule_rpush e"
      in ssubst)
    apply(rename_tac G e x w c wa nat)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(force)
   apply(rename_tac G e x w c wa nat)(*strict*)
   apply(case_tac "rule_rpush e")
    apply(rename_tac G e x w c wa nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e x w c wa nat a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
    apply(rename_tac G e x w c wa nat a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e x w c wa nat a list)(*strict*)
   apply(thin_tac "rule_rpush e=a#list")
   apply(clarsimp)
   apply(rename_tac G e x w c wa nat w' x')(*strict*)
   apply(rule_tac
      t="butlast_if_match (w @ w' @ [x']) (parser_bottom G)"
      and s="w @ w' @ [x']"
      in ssubst)
    apply(rename_tac G e x w c wa nat w' x')(*strict*)
    apply(rule butlast_if_match_direct2)
     apply(rename_tac G e x w c wa nat w' x')(*strict*)
     apply(force)
    apply(rename_tac G e x w c wa nat w' x')(*strict*)
    apply(force)
   apply(rename_tac G e x w c wa nat w' x')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat+length wa=length w + length w'")
    apply(rename_tac G e x w c wa nat w' x')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G e x w c wa nat w' x')(*strict*)
   apply(erule disjE)
    apply(rename_tac G e x w c wa nat w' x')(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e x w c wa nat w' x' ca)(*strict*)
    apply(subgoal_tac "prefix (wa@[parser_bottom G]) w \<or> prefix w (wa@[parser_bottom G])")
     apply(rename_tac G e x w c wa nat w' x' ca)(*strict*)
     prefer 2
     apply(rule mutual_prefix_prefix)
     apply(force)
    apply(rename_tac G e x w c wa nat w' x' ca)(*strict*)
    apply(erule disjE)
     apply(rename_tac G e x w c wa nat w' x' ca)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
    apply(rename_tac G e x w c wa nat w' x' ca)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e x w c wa nat w' x' ca cb)(*strict*)
    apply(case_tac cb)
     apply(rename_tac G e x w c wa nat w' x' ca cb)(*strict*)
     apply(clarsimp)
    apply(rename_tac G e x w c wa nat w' x' ca cb a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
     apply(rename_tac G e x w c wa nat w' x' ca cb a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x w c wa nat w' x' ca cb a list)(*strict*)
    apply(thin_tac "cb=a#list")
    apply(clarsimp)
    apply(rename_tac G e x w c nat w' x' ca w'a)(*strict*)
    apply(case_tac ca)
     apply(rename_tac G e x w c nat w' x' ca w'a)(*strict*)
     apply(clarsimp)
    apply(rename_tac G e x w c nat w' x' ca w'a a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
     apply(rename_tac G e x w c nat w' x' ca w'a a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x w c nat w' x' ca w'a a list)(*strict*)
    apply(thin_tac "ca=a#list")
    apply(clarsimp)
   apply(rename_tac G e x w c wa nat w' x')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e x w c wa nat w' x' ca)(*strict*)
   apply(case_tac ca)
    apply(rename_tac G e x w c wa nat w' x' ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e x w c wa nat w' x' ca a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
    apply(rename_tac G e x w c wa nat w' x' ca a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e x w c wa nat w' x' ca a list)(*strict*)
   apply(thin_tac "ca=a#list")
   apply(clarsimp)
  apply(rename_tac G e f x w c)(*strict*)
  apply(rule_tac
      t="butlast_if_match f (parser_bottom G)"
      and s="f"
      in ssubst)
   apply(rename_tac G e f x w c)(*strict*)
   apply(rule butlast_if_match_direct2_prime)
   apply(force)
  apply(rename_tac G e f x w c)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac G e f x w c)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e x w c ca)(*strict*)
   apply(case_tac ca)
    apply(rename_tac G e x w c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x w c)(*strict*)
    apply(case_tac "rule_rpush e")
     apply(rename_tac G e x w c)(*strict*)
     apply(clarsimp)
     apply(rename_tac G e x c)(*strict*)
     apply(rule_tac
      t="butlast_if_match [] (parser_bottom G)"
      and s="[]"
      in ssubst)
      apply(rename_tac G e x c)(*strict*)
      apply(rule butlast_if_match_direct2_prime)
      apply(force)
     apply(rename_tac G e x c)(*strict*)
     apply(clarsimp)
    apply(rename_tac G e x w c a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
     apply(rename_tac G e x w c a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x w c a list)(*strict*)
    apply(thin_tac "rule_rpush e=a#list")
    apply(clarsimp)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(rule_tac
      t="butlast_if_match (w' @ [x']) (parser_bottom G)"
      and s="w'@[x']"
      in ssubst)
     apply(rename_tac G e x w c w' x')(*strict*)
     apply(rule butlast_if_match_direct2)
      apply(rename_tac G e x w c w' x')(*strict*)
      apply(force)
     apply(rename_tac G e x w c w' x')(*strict*)
     apply(force)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(rule_tac
      t="butlast_if_match (w@w' @ [x']) (parser_bottom G)"
      and s="w@w'@[x']"
      in ssubst)
     apply(rename_tac G e x w c w' x')(*strict*)
     apply(rule butlast_if_match_direct2)
      apply(rename_tac G e x w c w' x')(*strict*)
      apply(force)
     apply(rename_tac G e x w c w' x')(*strict*)
     apply(force)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(clarsimp)
   apply(rename_tac G e x w c ca a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
    apply(rename_tac G e x w c ca a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e x w c ca a list)(*strict*)
   apply(thin_tac "ca=a#list")
   apply(clarsimp)
   apply(rename_tac G e x w c w' x')(*strict*)
   apply(rule_tac
      t="butlast_if_match (rule_rpush e @ w' @ [x']) (parser_bottom G)"
      and s="(rule_rpush e @ w' @ [x'])"
      in ssubst)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(rule butlast_if_match_direct2)
     apply(rename_tac G e x w c w' x')(*strict*)
     apply(force)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(force)
   apply(rename_tac G e x w c w' x')(*strict*)
   apply(rule_tac
      t="drop (Suc (length w + (length (rule_rpush e) + length w'))) (butlast_if_match (w @ rule_rpush e) (parser_bottom G))"
      and s="[]"
      in ssubst)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(rule drop_all)
    apply(rule_tac
      j="length ((w @ rule_rpush e))"
      in le_trans)
     apply(rename_tac G e x w c w' x')(*strict*)
     apply(rule butlast_if_match_length_le)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(force)
   apply(rename_tac G e x w c w' x')(*strict*)
   apply(force)
  apply(rename_tac G e f x w c)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G e f x w c ca)(*strict*)
  apply(rule_tac
      t="drop (length w + length (rule_rpush e)) f"
      and s="[]"
      in ssubst)
   apply(rename_tac G e f x w c ca)(*strict*)
   apply(rule drop_all)
   apply(rule_tac
      t="length w + length (rule_rpush e)"
      and s="length (w @ rule_rpush e)"
      in ssubst)
    apply(rename_tac G e f x w c ca)(*strict*)
    apply(force)
   apply(rename_tac G e f x w c ca)(*strict*)
   apply(rule_tac
      t="w @ rule_rpush e"
      and s="f@ca"
      in ssubst)
    apply(rename_tac G e f x w c ca)(*strict*)
    apply(force)
   apply(rename_tac G e f x w c ca)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac G e f x w c ca)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="drop (length f) (butlast_if_match (w @ rule_rpush e) (parser_bottom G))"
      and s="butlast_if_match ca (parser_bottom G)"
      in ssubst)
   apply(rename_tac G e f x w c ca)(*strict*)
   apply(rule_tac
      t="w @ rule_rpush e"
      and s="f@ca"
      in ssubst)
    apply(rename_tac G e f x w c ca)(*strict*)
    apply(force)
   apply(rename_tac G e f x w c ca)(*strict*)
   apply(rule drop_butlast_if_match_distrib)
  apply(rename_tac G e f x w c ca)(*strict*)
  apply(case_tac ca)
   apply(rename_tac G e f x w c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e x w c)(*strict*)
   apply(rule_tac
      t="butlast_if_match [] (parser_bottom G)"
      and s="[]"
      in ssubst)
    apply(rename_tac G e x w c)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(force)
   apply(rename_tac G e x w c)(*strict*)
   apply(clarsimp)
   apply(case_tac "rule_rpush e")
    apply(rename_tac G e x w c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x c)(*strict*)
    apply(rule_tac
      t="butlast_if_match [] (parser_bottom G)"
      and s="[]"
      in ssubst)
     apply(rename_tac G e x c)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(force)
    apply(rename_tac G e x c)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e x w c a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
    apply(rename_tac G e x w c a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e x w c a list)(*strict*)
   apply(thin_tac "rule_rpush e=a#list")
   apply(clarsimp)
   apply(rename_tac G e x w c w' x')(*strict*)
   apply(rule_tac
      t="butlast_if_match (w' @ [x']) (parser_bottom G)"
      and s="w'@[x']"
      in ssubst)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(rule butlast_if_match_direct2)
     apply(rename_tac G e x w c w' x')(*strict*)
     apply(force)
    apply(rename_tac G e x w c w' x')(*strict*)
    apply(force)
   apply(rename_tac G e x w c w' x')(*strict*)
   apply(force)
  apply(rename_tac G e f x w c ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac G e f x w c ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e f x w c ca a list)(*strict*)
  apply(thin_tac "ca=a#list")
  apply(clarsimp)
  apply(rename_tac G e f x w c w' x')(*strict*)
  apply(case_tac "rule_rpush e")
   apply(rename_tac G e f x w c w' x')(*strict*)
   apply(clarsimp)
   apply(rename_tac G e f x c w' x')(*strict*)
   apply(rule_tac
      t="butlast_if_match [] (parser_bottom G)"
      and s="[]"
      in ssubst)
    apply(rename_tac G e f x c w' x')(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(force)
   apply(rename_tac G e f x c w' x')(*strict*)
   apply(clarsimp)
  apply(rename_tac G e f x w c w' x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
   apply(rename_tac G e f x w c w' x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e f x w c w' x' a list)(*strict*)
  apply(thin_tac "rule_rpush e=a#list")
  apply(clarsimp)
  apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
  apply(rule_tac
      x="c@w"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="f @ butlast_if_match (w' @ [x'a]) (parser_bottom G)"
      and s="butlast_if_match (f @ w' @ [x'a]) (parser_bottom G)"
      in ssubst)
   apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
   apply (metis butlast_if_match_pull_out_prime)
  apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
  apply(rule_tac
      t="w @ butlast_if_match (w'a @ [x'a]) (parser_bottom G)"
      and s="butlast_if_match (w @ w'a @ [x'a]) (parser_bottom G)"
      in ssubst)
   apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
   apply (metis butlast_if_match_pull_out dropPrecise drop_Nil not_Cons_self)
  apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
  apply(rule_tac
      t="f @ w' @ [x'a]"
      and s="(f @ w')@ [x'a]"
      in ssubst)
   apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
   apply(force)
  apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
  apply(rule_tac
      t="f @ w'"
      and s="w @ w'a"
      in ssubst)
   apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
   apply(force)
  apply(rename_tac G e f x w c w' w'a x'a)(*strict*)
  apply(force)
  done

interpretation "parserHF" : loc_autHF_0
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs)
  done

lemma parserHF_inst_AX_effect_inclusion1: "
  (\<forall>M f. parserHF_marking_condition M f \<longrightarrow> parserHF_marked_effect M f \<subseteq> parserHF_unmarked_effect M f)"
  apply(clarsimp)
  apply(rename_tac M f x)(*strict*)
  apply(simp add: parserHF_unmarked_effect_def parserHF_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M f i e c)(*strict*)
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
  done

lemma parserHF_ins_lang_sound: "
  (\<forall>M. valid_parser M \<longrightarrow> parserHF.unmarked_language M \<subseteq> parser_markers M)"
  apply(clarsimp)
  apply(rename_tac M x)(*strict*)
  apply(simp add: parserHF.unmarked_language_def parserHF_unmarked_effect_def parser_markers_def)
  apply(clarsimp)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(subgoal_tac "c \<in> parserHF_configurations M")
   apply(rename_tac M xa d i e c)(*strict*)
   apply(simp add: parserHF_configurations_def)
   apply(clarsimp)
   apply(rename_tac M xa d i e f h l)(*strict*)
   apply(force)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(rule parserHF.belongs_configurations)
   apply(rename_tac M xa d i e c)(*strict*)
   apply(rule parserHF.derivation_initial_belongs)
    apply(rename_tac M xa d i e c)(*strict*)
    apply(force)
   apply(rename_tac M xa d i e c)(*strict*)
   apply(force)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(force)
  done

lemma parserHF_inst_AX_marking_condition_implies_existence_of_effect: "
  (\<forall>M. valid_parser M \<longrightarrow> (\<forall>f. parserHF.derivation_initial M f \<longrightarrow> parserHF_marking_condition M f \<longrightarrow> parserHF_marked_effect M f \<noteq> {}))"
  apply(simp add: parserHF_marking_condition_def parserHF_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M f i e c)(*strict*)
  apply(force)
  done

lemma parserHF_inst_AX_unmarked_effect_persists: "
  (\<forall>G. valid_parser G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial parserHF_initial_configurations
               parserHF_step_relation G d \<longrightarrow>
              (\<forall>n. parserHF_unmarked_effect G (derivation_take d n)
                   \<subseteq> parserHF_unmarked_effect G d)))"
  apply(clarsimp)
  apply(rename_tac G d n xa)(*strict*)
  apply(simp add: parserHF_unmarked_effect_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac G d n i e c)(*strict*)
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
  apply(case_tac "i\<le>n")
   apply(rename_tac G d n i e c)(*strict*)
   apply(force)
  apply(rename_tac G d n i e c)(*strict*)
  apply(force)
  done

lemma parserHF_inst_ATS_axioms: "
  ATS_Language_axioms valid_parser parserHF_initial_configurations
     parserHF_step_relation parser_markers parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect"
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: parserHF_inst_AX_effect_inclusion1 parserHF_ins_lang_sound parserHF_inst_AX_marking_condition_implies_existence_of_effect parserHF_inst_AX_unmarked_effect_persists )
  done

interpretation "parserHF" : loc_autHF_1
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHF_inst_ATS_axioms )
  done

definition parserHF_set_history :: "
  ('stack, 'event) parserHF_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserHF_conf"
  where
    "parserHF_set_history c h \<equiv>
  c \<lparr>parserHF_conf_history := h\<rparr>"

lemma parserHF_inst_AX_initial_history_empty: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHF_initial_configurations G \<longrightarrow> parserHF_conf_history c = []))"
  apply(simp add: parserHF_initial_configurations_def)
  done

lemma parserHF_inst_AX_steps_extend_history: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHF_configurations G \<longrightarrow> (\<forall>e c'. parserHF_step_relation G c e c' \<longrightarrow> (\<exists>hf\<in> parser_markers G. parserHF_conf_history c' = parserHF_conf_history c @ hf))))"
  apply(clarsimp)
  apply(rename_tac G c e c')(*strict*)
  apply(subgoal_tac "SSe \<in> parser_step_labels SSG \<and> SSc2 \<in> parserHF_configurations SSG" for SSe SSc2 SSG)
   apply(rename_tac G c e c')(*strict*)
   prefer 2
   apply(rule parserHF.AX_step_relation_preserves_belongs)
     apply(rename_tac G c e c')(*strict*)
     apply(force)
    apply(rename_tac G c e c')(*strict*)
    apply(force)
   apply(rename_tac G c e c')(*strict*)
   apply(force)
  apply(rename_tac G c e c')(*strict*)
  apply(clarsimp)
  apply(simp add: parserHF_step_relation_def parser_markers_def parser_step_labels_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x xa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c e c' x xa)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac G c e c' x xa)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x xa k w xc)(*strict*)
  apply(rule_tac
      A="set (drop (length (parserHF_conf_fixed c)) (butlast_if_match (kPrefix k (w @ [parser_bottom G])) (parser_bottom G)))"
      in set_mp)
   apply(rename_tac G c e c' x xa k w xc)(*strict*)
   apply(rule_tac
      B="set ((butlast_if_match (kPrefix k (w @ [parser_bottom G])) (parser_bottom G)))"
      in subset_trans)
    apply(rename_tac G c e c' x xa k w xc)(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac G c e c' x xa k w xc)(*strict*)
   apply(rule_tac
      B="set (((kPrefix k (w @ [parser_bottom G]))))"
      in subset_trans)
    apply(rename_tac G c e c' x xa k w xc)(*strict*)
    apply(rule set_butlast_if_match_is_subset)
   apply(rename_tac G c e c' x xa k w xc)(*strict*)
   apply(rule set_kPrefix_subset)
   apply(clarsimp)
   apply(simp add: valid_parser_def)
   apply(blast)
  apply(rename_tac G c e c' x xa k w xc)(*strict*)
  apply(force)
  done

lemma parserHF_inst_AX_empty_history_is_history: "
  (\<forall>G. valid_parser G \<longrightarrow> [] \<in> parser_markers G)"
  apply(simp add: parser_markers_def)
  done

lemma parserHF_inst_AX_set_get_history: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHF_configurations G \<longrightarrow> parserHF_set_history c (parserHF_conf_history c) = c))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserHF_set_history_def)
  done

lemma parserHF_inst_AX_get_set_history: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHF_configurations G \<longrightarrow> (\<forall>h. h \<in> parser_markers G \<longrightarrow> parserHF_conf_history (parserHF_set_history c h) = h)))"
  apply(clarsimp)
  apply(rename_tac G c h)(*strict*)
  apply(simp add: parserHF_set_history_def)
  done

lemma parserHF_inst_AX_join_history_fragments_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>hf1. hf1 \<in> parser_markers G \<longrightarrow> (\<forall>hf2. hf2 \<in> parser_markers G \<longrightarrow> hf1 @ hf2 \<in> parser_markers G)))"
  apply(clarsimp)
  apply(rename_tac G hf1 hf2)(*strict*)
  apply(simp add: parser_markers_def)
  done

lemma parserHF_inst_AX_get_history_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHF_configurations G \<longrightarrow> parserHF_conf_history c \<in> parser_markers G))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parser_markers_def parserHF_configurations_def)
  apply(clarsimp)
  apply(rename_tac G x f h l)(*strict*)
  apply(force)
  done

lemma parserHF_inst_AX_mutual_prefix: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>hf1. hf1 \<in> parser_markers G \<longrightarrow> (\<forall>hf2. hf2 \<in> parser_markers G \<longrightarrow> (\<forall>hf3. hf3 \<in> parser_markers G \<longrightarrow> (\<forall>hf4. hf4 \<in> parser_markers G \<longrightarrow> hf1 @ hf2 = hf3 @ hf4 \<longrightarrow> (\<exists>hf\<in> parser_markers G. hf1 @ hf = hf3) \<or> (\<exists>hf\<in> parser_markers G. hf3 @ hf = hf1))))))"
  apply(clarsimp)
  apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
  apply(simp add: parser_markers_def parserHF_configurations_def)
  apply(subgoal_tac "prefix hf1 hf3 \<or> prefix hf3 hf1")
   apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
  apply(erule disjE)
   apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G hf2 hf3 c)(*strict*)
  apply(force)
  done

lemma parserHF_inst_ATS_History_axioms: "
  ATS_History_axioms valid_parser parserHF_configurations
     parserHF_initial_configurations parserHF_step_relation parser_markers
     parser_markers parser_empty_history parser_empty_history_fragment
     parserHF_set_history (@) (@) parserHF_conf_history"
  apply(simp add: ATS_History_axioms_def)
  apply(simp add: parserHF_inst_AX_initial_history_empty parserHF_inst_AX_steps_extend_history parserHF_inst_AX_empty_history_is_history parserHF_inst_AX_set_get_history parserHF_inst_AX_get_set_history parserHF_inst_AX_join_history_fragments_closed parserHF_inst_AX_get_history_closed parserHF_inst_AX_mutual_prefix )
  done

interpretation "parserHF" : loc_autHF_2
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* set_history *)
  "parserHF_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "parserHF_conf_history"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHF_inst_ATS_axioms parserHF_inst_ATS_History_axioms )
  done

lemma parserHF_inst_lang_finite: "
  (\<forall>G. valid_parser G \<longrightarrow> parserHF.finite_marked_language G = parserHF.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserHF.finite_marked_language_def parserHF.marked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: parserHF.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: parserHF_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(rule parserHF.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d i e c)(*strict*)
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
   apply(simp add: derivation_take_def)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(simp add: parserHF_marking_condition_def)
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
   apply(rename_tac G d i e c ia ea ca)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma parserHF_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_parser G \<longrightarrow> parserHF.finite_unmarked_language G = parserHF.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserHF.finite_unmarked_language_def parserHF.unmarked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: parserHF.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: parserHF_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(rule parserHF.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d i e c)(*strict*)
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
   apply(simp add: derivation_take_def)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

definition parserHF_get_fixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHF_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "parserHF_get_fixed_scheduler_DB G d n \<equiv>
  parserHF_conf_fixed (the (get_configuration (d n)))"

lemma parserHF_inst_AX_fixed_scheduler_extendable_translates_backwards: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserHF_configurations G \<longrightarrow> (\<forall>e c2. parserHF_step_relation G c1 e c2 \<longrightarrow> \<not> parserHF_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> parserHF_conf_fixed c1 \<sqsupseteq> [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c1 e c2)(*strict*)
   prefer 2
   apply(simp add: parserHF_step_relation_def valid_parser_def)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(subgoal_tac "c2 \<in> parserHF_configurations G")
   apply(rename_tac G c1 e c2)(*strict*)
   prefer 2
   apply(rule parserHF.AX_step_relation_preserves_belongsC)
     apply(rename_tac G c1 e c2)(*strict*)
     apply(force)
    apply(rename_tac G c1 e c2)(*strict*)
    apply(force)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(force)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(simp add: valid_parser_step_label_def suffix_def parserHF_configurations_def parserHF_step_relation_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G e c k w xa ca cb xb)(*strict*)
  apply(case_tac "length (kPrefix k (w @ [parser_bottom G])) - length c")
   apply(rename_tac G e c k w xa ca cb xb)(*strict*)
   apply(clarsimp)
  apply(rename_tac G e c k w xa ca cb xb nat)(*strict*)
  apply(clarsimp)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac G e c k w xa ca cb xb nat)(*strict*)
   prefer 2
   apply(rename_tac G e c k w xa ca cb xb nat nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e c k w xa ca cb xb nat nata x)(*strict*)
   apply(erule_tac
      x="x"
      in allE)
   apply(force)
  apply(rename_tac G e c k w xa ca cb xb nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "min (length w) k = k")
   apply(rename_tac G e c k w xa ca cb xb nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e c k w xa ca cb xb nat)(*strict*)
  apply(clarsimp)
  apply(thin_tac "min (length w) k = k")
  apply(erule disjE)
   apply(rename_tac G e c k w xa ca cb xb nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
   apply(case_tac cc)
    apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e c k w xa ca cb xb nat x)(*strict*)
    apply(erule_tac
      x="x"
      in allE)
    apply(force)
   apply(rename_tac G e c k w xa ca cb xb nat cc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cc = w' @ [x']")
    apply(rename_tac G e c k w xa ca cb xb nat cc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e c k w xa ca cb xb nat cc a list)(*strict*)
   apply(thin_tac "cc = a # list")
   apply(clarsimp)
  apply(rename_tac G e c k w xa ca cb xb nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
  apply(subgoal_tac "parser_bottom G \<in> set w")
   apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
   apply(subgoal_tac "parser_bottom G \<notin> set w")
    apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
    apply(force)
   apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
   apply(rule_tac
      A="parser_events G"
      in not_in_diff)
   apply(force)
  apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
  apply(rule_tac
      A="set(take k w)"
      in set_mp)
   apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
   apply(rule set_take_subset)
  apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
  apply(rule_tac
      t="take k w"
      and s="c @ [parser_bottom G] @ cc"
      in ssubst)
   apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
   apply(force)
  apply(rename_tac G e c k w xa ca cb xb nat cc)(*strict*)
  apply(simp (no_asm))
  done

lemma parserHF_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHF.derivation G d \<longrightarrow> parserHF.belongs G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserHF_get_fixed_scheduler_DB G d n \<in> parser_fixed_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserHF_get_fixed_scheduler_DB_def)
  apply(simp add: parser_fixed_schedulers_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "b \<in> parserHF_configurations G")
   apply(rename_tac G d n option b)(*strict*)
   prefer 2
   apply (metis parserHF.belongs_configurations)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: parserHF_configurations_def parser_schedulers_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G d n option f h l)(*strict*)
  apply(case_tac "parser_bottom G \<in> set f")
   apply(rename_tac G d n option f h l)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d n option h l w)(*strict*)
   apply(rule_tac
      x="w @ [parser_bottom G]"
      in exI)
   apply(clarsimp)
  apply(rename_tac G d n option f h l)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="f @ [parser_bottom G]"
      in exI)
  apply(clarsimp)
  done

lemma parserHF_inst_AX_get_fixed_scheduler_DB_restrict: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>x n. x \<le> n \<longrightarrow> (\<forall>d1. parserHF.derivation G d1 \<longrightarrow> (\<forall>d2. parserHF_get_fixed_scheduler_DB G (derivation_append d1 d2 n) x = parserHF_get_fixed_scheduler_DB G d1 x)))"
  apply(clarsimp)
  apply(rename_tac G x n d1 d2)(*strict*)
  apply(simp add: derivation_append_def parserHF_get_fixed_scheduler_DB_def)
  done

lemma parserHF_inst_ATS_SchedF_SB_axioms: "
  ATS_SchedF_SB_axioms valid_parser parserHF_configurations
     parserHF_step_relation parser_fixed_scheduler_extendable
     parserHF_conf_fixed"
  apply(simp add: ATS_SchedF_SB_axioms_def)
  apply(simp add: parserHF_inst_AX_fixed_scheduler_extendable_translates_backwards )
  done

interpretation "parserHF" : loc_autHF_3
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* set_history *)
  "parserHF_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "parserHF_conf_history"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* get_fixed_scheduler *)
  "parserHF_conf_fixed"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHF_inst_ATS_axioms parserHF_inst_ATS_History_axioms parserHF_inst_ATS_SchedF_SB_axioms )
  done

lemma parserHF_inst_AX_schedF_db_extendable_translates_backwards: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d1. parserHF.derivation G d1 \<longrightarrow> parserHF.belongs G d1 \<longrightarrow> (\<forall>n x. (\<exists>y. d1 (n + x) = Some y) \<longrightarrow> \<not> parserHF_get_fixed_scheduler_DB G d1 (n + x) \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> parserHF_get_fixed_scheduler_DB G d1 n \<sqsupseteq> [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G d1 n x y)(*strict*)
  apply(simp add: parserHF_get_fixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. d1 n= Some (pair e c)")
   apply(rename_tac G d1 n x y)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d1 n x y e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac y)
   apply(rename_tac G d1 n x y e c option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d1 n x e c option b)(*strict*)
   apply(subgoal_tac "\<not> parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G]")
    apply(rename_tac G d1 n x e c option b)(*strict*)
    prefer 2
    apply(fold parser_fixed_scheduler_extendable_def)
    apply(rule parserHF.fixed_scheduler_extendable_translates_backwards_lift)
          apply(rename_tac G d1 n x e c option b)(*strict*)
          apply(force)
         apply(rename_tac G d1 n x e c option b)(*strict*)
         apply(force)
        apply(rename_tac G d1 n x e c option b)(*strict*)
        apply (metis parserHF.belongs_configurations)
       apply(rename_tac G d1 n x e c option b)(*strict*)
       apply(force)
      apply(rename_tac G d1 n x e c option b)(*strict*)
      apply(force)
     apply(rename_tac G d1 n x e c option b)(*strict*)
     apply(force)
    apply(rename_tac G d1 n x e c option b)(*strict*)
    apply(force)
   apply(rename_tac G d1 n x e c option b)(*strict*)
   apply(force)
  apply(rename_tac G d1 n x y)(*strict*)
  apply(rule_tac
      m="n+x"
      in parserHF.pre_some_position_is_some_position)
    apply(rename_tac G d1 n x y)(*strict*)
    apply(force)
   apply(rename_tac G d1 n x y)(*strict*)
   apply(force)
  apply(rename_tac G d1 n x y)(*strict*)
  apply(force)
  done

lemma parserHF_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHF.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> parserHF_get_fixed_scheduler_DB G d n = parserHF_conf_fixed c))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserHF_get_fixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  done

lemma parserHF_inst_AX_history_no_mod_after_nonextendable_fixed_sched: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>c. parserHF_conf_fixed c \<sqsupseteq> [parser_bottom G] \<longrightarrow> c \<in> parserHF_configurations G \<longrightarrow> (\<forall>e c'. parserHF_step_relation G c e c' \<longrightarrow> parserHF_conf_history c = parserHF_conf_history c'))"
  apply(clarsimp)
  apply(rename_tac G c e c')(*strict*)
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac G c e c' x ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G c e c' x ca cb)(*strict*)
   apply (metis append_length_inc drop_entire_butlast_if_match drop_eq_Nil length_Suc)
  apply(rename_tac G c e c' x ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c e c' x ca cb)(*strict*)
  apply(subgoal_tac "cb=[]")
   apply(rename_tac G c e c' x ca cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G c e c' x ca)(*strict*)
   apply (metis butlast_if_match_length_le length_Suc)
  apply(rename_tac G c e c' x ca cb)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c e c' x ca cb)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac G c e c' x ca cb)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x ca cb k w xb)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length w")
   apply(rename_tac G c e c' x ca cb k w xb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<in> set w")
    apply(rename_tac G c e c' x ca cb k w xb)(*strict*)
    apply(force)
   apply(rename_tac G c e c' x ca cb k w xb)(*strict*)
   apply (metis Cons_eq_appendI append_Nil append_eq_appendI append_self_conv butlast_if_match_direct butlast_if_match_direct2_prime in_set_takeD kPrefix_def list.simps(2) take_append_prime)
  apply(rename_tac G c e c' x ca cb k w xb nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c e c' x ca cb k w xb nat xa)(*strict*)
  apply(case_tac cb)
   apply(rename_tac G c e c' x ca cb k w xb nat xa)(*strict*)
   apply(force)
  apply(rename_tac G c e c' x ca cb k w xb nat xa a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
   apply(rename_tac G c e c' x ca cb k w xb nat xa a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G c e c' x ca cb k w xb nat xa a list)(*strict*)
  apply(thin_tac "cb=a#list")
  apply(clarsimp)
  done

lemma parserHF_inst_ATS_SchedF_DB_axioms: "
  ATS_SchedF_DB_axioms valid_parser parserHF_configurations
     parser_step_labels parserHF_step_relation parser_fixed_schedulers
     parser_fixed_scheduler_extendable parserHF_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_DB_axioms_def)
  apply(simp add: parserHF_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers parserHF_inst_AX_fixed_scheduler_extendable_translates_backwards parserHF_inst_AX_get_fixed_scheduler_DB_restrict parserHF_inst_AX_schedF_db_extendable_translates_backwards )
  done

lemma parserHF_inst_ATS_SchedF_SDB_axioms: "
  ATS_SchedF_SDB_axioms valid_parser parserHF_initial_configurations parserHF_step_relation parserHF_conf_fixed parserHF_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_SDB_axioms_def)
  apply(simp add: parserHF_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler )
  done

lemma parserHF_inst_ATS_determHIST_SB_axioms: "
  ATS_determHIST_SB_axioms valid_parser parserHF_configurations
     parserHF_step_relation parserHF_conf_history
     parser_fixed_scheduler_extendable parserHF_conf_fixed"
  apply(simp add: ATS_determHIST_SB_axioms_def)
  apply(simp add: parserHF_inst_AX_history_no_mod_after_nonextendable_fixed_sched )
  done

interpretation "parserHF" : loc_autHF_6
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* set_history *)
  "parserHF_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "parserHF_conf_history"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* get_fixed_scheduler *)
  "parserHF_conf_fixed"
  (* get_fixed_scheduler_DB *)
  "parserHF_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHF_inst_ATS_axioms parserHF_inst_ATS_History_axioms parserHF_inst_ATS_SchedF_SB_axioms parserHF_inst_ATS_SchedF_DB_axioms parserHF_inst_ATS_SchedF_SDB_axioms parserHF_inst_ATS_determHIST_SB_axioms )
  done

lemma parserHF_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_parser
     parserHF_initial_configurations parserHF_step_relation
     parserHF_marking_condition parserHF_marked_effect
     parserHF_unmarked_effect"
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(simp add: parserHF_inst_lang_finite parserHF_inst_AX_unmarked_language_finite )
  done

interpretation "parserHF" : loc_autHF_7
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* set_history *)
  "parserHF_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "parserHF_conf_history"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* get_fixed_scheduler *)
  "parserHF_conf_fixed"
  (* get_fixed_scheduler_DB *)
  "parserHF_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHF_inst_ATS_axioms parserHF_inst_ATS_History_axioms parserHF_inst_ATS_SchedF_SB_axioms parserHF_inst_ATS_SchedF_DB_axioms parserHF_inst_ATS_SchedF_SDB_axioms parserHF_inst_ATS_determHIST_SB_axioms parserHF_inst_ATS_Language_by_Finite_Derivations_axioms )
  done

lemma parserHF_inst_AX_is_forward_target_deterministic_correspond_SB: "
  \<forall>G. valid_parser G \<longrightarrow> parserHF.is_forward_target_deterministic_accessible G = ATS_determHIST_SB.is_forward_target_deterministicHist_SB_long parserHF_initial_configurations parserHF_step_relation parser_markers (@) (@) parserHF_conf_history parser_fixed_scheduler_extendable parserHF_conf_fixed G"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rule parserHF.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHF.is_forward_target_deterministic_accessible_def)
  apply(simp add: parserHF.is_forward_target_deterministicHist_SB_long_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac G c c1 c2 e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(erule_tac
      x="c1"
      in allE)
  apply(erule_tac
      x="c2"
      in allE)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in allE)
  apply(clarsimp)
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  done

lemma parserHF_inst_ATS_HistoryCT_SB_axioms: "
  ATS_HistoryCT_SB_axioms valid_parser parserHF_initial_configurations parserHF_step_relation parser_markers (@) (@) parserHF_conf_history parser_fixed_scheduler_extendable parserHF_conf_fixed"
  apply(simp add: ATS_HistoryCT_SB_axioms_def)
  apply(simp add: parserHF_inst_AX_is_forward_target_deterministic_correspond_SB )
  done

interpretation "parserHF" : loc_autHF_8
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* set_history *)
  "parserHF_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "parserHF_conf_history"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* get_fixed_scheduler *)
  "parserHF_conf_fixed"
  (* get_fixed_scheduler_DB *)
  "parserHF_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHF_inst_ATS_axioms parserHF_inst_ATS_History_axioms parserHF_inst_ATS_SchedF_SB_axioms parserHF_inst_ATS_SchedF_DB_axioms parserHF_inst_ATS_SchedF_SDB_axioms parserHF_inst_ATS_determHIST_SB_axioms parserHF_inst_ATS_Language_by_Finite_Derivations_axioms parserHF_inst_ATS_HistoryCT_SB_axioms )
  done

lemma parserHF_inst_AX_is_forward_target_deterministic_correspond_DB: "
  \<forall>G. valid_parser G \<longrightarrow> parserHF.is_forward_target_deterministic_accessible G = ATS_determHIST_DB.is_forward_target_deterministicHist_DB_long parserHF_initial_configurations parserHF_step_relation parser_markers (@) (@) parserHF_conf_history parser_fixed_scheduler_extendable parserHF_get_fixed_scheduler_DB G"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rule parserHF.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_DB_long)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHF.is_forward_target_deterministic_accessible_def)
  apply(simp add: parserHF.is_forward_target_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  done

lemma parserHF_inst_ATS_HistoryCT_DB_axioms: "
  ATS_HistoryCT_DB_axioms valid_parser parserHF_initial_configurations parserHF_step_relation parser_markers (@) (@) parserHF_conf_history parser_fixed_scheduler_extendable parserHF_get_fixed_scheduler_DB"
  apply(simp add: ATS_HistoryCT_DB_axioms_def)
  apply(simp add: parserHF_inst_AX_is_forward_target_deterministic_correspond_DB )
  done

interpretation "parserHF" : loc_autHF_9
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* set_history *)
  "parserHF_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "parserHF_conf_history"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* get_fixed_scheduler *)
  "parserHF_conf_fixed"
  (* get_fixed_scheduler_DB *)
  "parserHF_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHF_inst_ATS_axioms parserHF_inst_ATS_History_axioms parserHF_inst_ATS_SchedF_SB_axioms parserHF_inst_ATS_SchedF_DB_axioms parserHF_inst_ATS_SchedF_SDB_axioms parserHF_inst_ATS_determHIST_SB_axioms parserHF_inst_ATS_Language_by_Finite_Derivations_axioms parserHF_inst_ATS_HistoryCT_SB_axioms parserHF_inst_ATS_HistoryCT_DB_axioms )
  done

lemma parserHF_inst_AX_BF_BraSBRest_DetHSB_LaOp: "
  \<forall>M. valid_parser M \<longrightarrow>
        ATS_determHIST_SB.is_forward_deterministicHist_SB
         parserHF_initial_configurations parserHF_step_relation
         parser_markers (@) (@) parserHF_conf_history
         parser_fixed_scheduler_extendable parserHF_conf_fixed M \<longrightarrow>
        nonblockingness_language
         (ATS_Language0.unmarked_language parserHF_initial_configurations
           parserHF_step_relation parserHF_unmarked_effect M)
         (ATS_Language0.marked_language parserHF_initial_configurations
           parserHF_step_relation parserHF_marking_condition
           parserHF_marked_effect M) \<longrightarrow>
        ATS_SchedF_SB.Nonblockingness_branching_restricted parserHF_configurations
         parserHF_initial_configurations parser_step_labels
         parserHF_step_relation parserHF_marking_condition
         parser_fixed_scheduler_extendable parserHF_conf_fixed M"
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: parserHF.Nonblockingness_branching_restricted_def)
  apply(clarsimp)
  apply(rename_tac M dh n)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
   apply(rename_tac M dh n)(*strict*)
   prefer 2
   apply(rule_tac
      M="M"
      in parserHF.some_position_has_details_before_max_dom)
     apply(rename_tac M dh n)(*strict*)
     apply (metis parserHF.derivation_initial_is_derivation)
    apply(rename_tac M dh n)(*strict*)
    apply(force)
   apply(rename_tac M dh n)(*strict*)
   apply(force)
  apply(rename_tac M dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "parserHF_conf_history c \<in> prefix_closure (parserHF.marked_language M)")
   apply(rename_tac M dh n e c)(*strict*)
   prefer 2
   apply(simp add: nonblockingness_language_def)
   apply(rename_tac M dh n e c)(*strict*)
   apply(rule_tac
      A=" parserHF.unmarked_language M"
      in set_mp)
    apply(rename_tac M dh n e c)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c)(*strict*)
   apply(thin_tac " parserHF.unmarked_language M \<subseteq> (prefix_closure (parserHF.marked_language M))")
   apply(rename_tac M dh n e c)(*strict*)
   apply(simp add: parserHF.unmarked_language_def)
   apply(rule_tac
      x="dh"
      in exI)
   apply(clarsimp)
   apply(simp add: parserHF.derivation_initial_def)
   apply(simp add: parserHF_unmarked_effect_def)
   apply(clarsimp)
   apply(force)
  apply(rename_tac M dh n e c)(*strict*)
  apply(thin_tac "nonblockingness_language (parserHF.unmarked_language M) (parserHF.marked_language M)")
  apply(rename_tac M dh n e c)(*strict*)
  apply(simp add: prefix_closure_def parserHF.marked_language_def prefix_def)
  apply(clarsimp)
  apply(rename_tac M dh n e c d ca)(*strict*)
  apply(simp add: parserHF_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac M dh n e c d ca i ea cb)(*strict*)
  apply(subgoal_tac "\<exists>i e c. d i = Some (pair e c) \<and> c \<in> parserHF_marking_configurations M \<and> (\<forall>j e' c'. i < j \<and> d j = Some (pair e' c') \<longrightarrow> parserHF_conf_history c = parserHF_conf_history c' )")
   apply(rename_tac M dh n e c d ca i ea cb)(*strict*)
   prefer 2
   apply(simp add: parserHF_marking_condition_def)
  apply(rename_tac M dh n e c d ca i ea cb)(*strict*)
  apply(thin_tac "parserHF_marking_condition M d")
  apply(clarsimp)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(subgoal_tac "dh 0 = d 0")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   prefer 2
   apply(simp add: parserHF.derivation_initial_def)
   apply(case_tac "d 0")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc b)(*strict*)
   apply(case_tac "dh 0")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc b)(*strict*)
    apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc b a option ba)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc b ba)(*strict*)
   apply(simp add: parserHF_initial_configurations_def)
    (*
  what should dc be?
  ia \<le> i \<le> n : d@i ~ d@ia; d@ia ~~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; dc = []
  ia \<le> n \<le> i : d@i ~ d@ia; d@ia ~~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; dc = []
  n \<le> ia \<le> i : d@ia ~ d@ia \<Longrightarrow> dc = d (n\<dots>ia)
  i \<le> ia \<le> n : d@ia ~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; dc = []
  i \<le> n \<le> ia : d@n ~ dh@n; dc = d (n\<dots>ia)
  n \<le> i \<le> ia : d@n ~ dh@n; dc = d (n\<dots>ia)
  ia \<le> n \<Longrightarrow> dc = []
  n \<le> ia \<Longrightarrow> dc = d (n\<dots>ia)
*)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(case_tac "ia\<le>n")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule_tac
      x="der1 c"
      in exI)
   apply(rule_tac
      t="derivation_append dh (der1 c) n"
      and s="dh"
      in ssubst)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(rule ext)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc x)(*strict*)
    apply(simp add: derivation_append_def)
    apply(clarsimp)
    apply(simp add: der1_def)
    apply(case_tac "dh x")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc x)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
    apply(rule_tac
      m="x"
      and d="dh"
      in parserHF.no_some_beyond_maximum_of_domain)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
       apply(simp add: parserHF.derivation_initial_def)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc x a)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(rule parserHF.der1_is_derivation)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(rule parserHF.der1_belongs)
    apply(rule parserHF.belongs_configurations)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(rule parserHF.derivation_initial_belongs)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
      apply (metis)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(rule_tac
      x="0"
      in exI)
    apply(rule der1_maximum_of_domain)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(simp add: derivation_append_fit_def der1_def)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(simp add: parserHF_marking_condition_def)
    (*
  where does it accept continuously?
  ia \<le> i \<le> n : d@i ~ d@ia; d@ia ~~ dh@ia \<Longrightarrow> d@ia=dh@ia; @ia @i
  ia \<le> n \<le> i : d@i ~ d@ia; d@ia ~~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; @ia
  i \<le> ia \<le> n : d@ia ~ dh@ia \<Longrightarrow> dh@n ~ dh@ia; @ia
  *)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(rule_tac
      x="ia"
      in exI)
   apply(subgoal_tac "dh ia = d ia")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    prefer 2
    apply(subgoal_tac "\<exists>e c. dh ia = Some (pair e c)")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     prefer 2
     apply(rule parserHF.some_position_has_details_before_max_dom)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
       apply(simp add: parserHF.derivation_initial_def)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(erule exE)+
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(subgoal_tac "\<exists>ca'. parserHF_conf_history c @ ca' = parserHF_conf_history cc")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     prefer 2
     apply(case_tac "i\<le>ia")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      prefer 2
      apply(erule_tac
      x="i"
      in allE)
      apply(clarsimp)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(subgoal_tac "\<exists>ca'. parserHF_conf_history cb @ ca' = parserHF_conf_history cc")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(rule_tac
      x="ca @ ca'"
      in exI)
      apply(rule_tac
      t="parserHF_conf_history cc"
      and s="parserHF_conf_history cb @ ca'"
      in ssubst)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(rule_tac
      t="parserHF_conf_history cb"
      and s="parserHF_conf_history c @ ca"
      in ssubst)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(simp (no_asm))
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(subgoal_tac "\<exists>h\<in> parser_markers M. parserHF_conf_history cc = parserHF_conf_history cb @ h")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      prefer 2
      apply(rule_tac
      d="d"
      and n="i"
      and m="ia-i"
      in parserHF.steps_extend_history_derivation)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
          apply(simp add: valid_bounded_parser_def)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
         apply(simp add: parserHF.derivation_initial_def)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
        apply(simp add: parserHF_marking_configurations_def)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(clarsimp)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(erule exE)+
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
    apply(rule_tac
      ?d1.0="dh"
      and n="ia"
      and m="ia"
      and ?d2.0="d"
      and x="0"
      and y="0"
      in parserHF.is_forward_deterministicHist_derivations_coincide)
               apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
               apply(force)
              apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
              apply(simp add: parserHF.derivation_initial_def)
             apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
             apply(force)
            apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
            apply(force)
           apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
           apply(force)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply(force)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
     apply(simp add: get_configuration_def)
     apply(subgoal_tac "\<exists>h\<in> parser_markers M. parserHF_conf_history c = parserHF_conf_history cd @ h")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      prefer 2
      apply(rule_tac
      d="dh"
      and n="ia"
      and m="n-ia"
      in parserHF.steps_extend_history_derivation)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply(simp add: parserHF.derivation_initial_def)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
        apply(simp add: parserHF_marking_configurations_def)
        apply(rule parserHF.belongs_configurations)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply(rule parserHF.derivation_initial_belongs)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply(force)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
     apply(erule bexE)+
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
     apply(subgoal_tac "cb \<in> parserHF_configurations M")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      prefer 2
      apply(rule_tac
      d="d"
      in parserHF.belongs_configurations)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(rule parserHF.derivation_initial_belongs)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
     apply(case_tac "ia\<le>i")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(subgoal_tac "parserHF_conf_history cc = parserHF_conf_history cb")
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       prefer 2
       apply(case_tac "ia<i")
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
        apply(erule_tac
      x="i"
      in allE)
        apply(clarsimp)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      x="h@ca"
      in bexI)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(simp add: parser_markers_def)
      apply(simp add: parserHF_configurations_def)
      apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea ia eb cc ec "cd" h x f l)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
     apply(subgoal_tac "\<exists>h\<in> parser_markers M. parserHF_conf_history cc = parserHF_conf_history cb @ h")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      prefer 2
      apply(rule_tac
      d="d"
      and n="i"
      and m="ia-i"
      in parserHF.steps_extend_history_derivation)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
         apply(simp add: parserHF.derivation_initial_def)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
        apply(simp add: parserHF_marking_configurations_def)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
       apply(simp add: get_configuration_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h)(*strict*)
     apply(clarsimp)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h ha)(*strict*)
     apply(rule_tac
      x="h @ ca @ ha"
      in bexI)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h ha)(*strict*)
      apply(clarsimp)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca' h ha)(*strict*)
     apply(simp add: parser_markers_def)
     apply(simp add: parserHF_configurations_def)
     apply(clarsimp)
     apply(rename_tac M dh n e c d ca i ea ia eb cc ec "cd" h ha x f l)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
    apply(simp add: get_configuration_def)
    apply(fold parser_fixed_scheduler_extendable_def)
    apply(rule_tac
      ?d="dh"
      in parserHF.fixed_scheduler_extendable_translates_backwards_lift)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
         apply (metis parserHF.derivation_initial_is_derivation)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
        apply (metis parserHF.belongs_configurations parserHF.derivation_initial_belongs)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" ca')(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(subgoal_tac "\<exists>h\<in> parser_markers M. parserHF_conf_history c = parserHF_conf_history cc @ h")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and n="ia"
      and m="n-ia"
      in parserHF.steps_extend_history_derivation)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
       apply(simp add: parserHF.derivation_initial_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
      apply(simp add: parserHF_marking_configurations_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(erule bexE)+
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
   apply(subgoal_tac "h@ca=[]")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
    prefer 2
    apply(case_tac "ia\<le>i")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
     apply(case_tac "ia<i")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
      apply(erule_tac
      x="i"
      in allE)
      apply(clarsimp)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
     apply(clarsimp)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
    apply(subgoal_tac "\<exists>h\<in> parser_markers M. parserHF_conf_history cc = parserHF_conf_history cb @ h")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
     prefer 2
     apply(rule_tac
      d="d"
      and n="i"
      and m="ia-i"
      in parserHF.steps_extend_history_derivation)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
         apply(force)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
        apply(simp add: parserHF.derivation_initial_def)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
       apply(simp add: parserHF_marking_configurations_def)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
      apply(simp add: get_configuration_def)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
    apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc h)(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(erule_tac
      x="j"
      in allE)
   apply(clarsimp)
   apply(subgoal_tac "j\<le>n")
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      in parserHF.allPreMaxDomSome_prime)
      apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
      apply(simp add: parserHF.derivation_initial_def)
      apply(force)
     apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(subgoal_tac "\<exists>h\<in> parser_markers M. parserHF_conf_history c = parserHF_conf_history c' @ h")
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and n="j"
      and m="n-j"
      in parserHF.steps_extend_history_derivation)
        apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
       apply(simp add: parserHF.derivation_initial_def)
      apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
      apply(simp add: parserHF_marking_configurations_def)
      apply(rule parserHF.belongs_configurations)
       apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
       apply(rule parserHF.derivation_initial_belongs)
        apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(subgoal_tac "\<exists>h\<in> parser_markers M. parserHF_conf_history c' = parserHF_conf_history cc @ h")
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and n="ia"
      and m="j-ia"
      in parserHF.steps_extend_history_derivation)
        apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
       apply(simp add: parserHF.derivation_initial_def)
      apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
      apply(simp add: parserHF_marking_configurations_def)
     apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
   apply(case_tac "d j")
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c')(*strict*)
    apply(clarify)
    apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' h ha)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' a)(*strict*)
   apply(clarify)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' a h ha)(*strict*)
   apply(case_tac a)
   apply(rename_tac M dh n e c d i ea cb ia eb cc j e' c' a h ha option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(subgoal_tac "ia>n")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(thin_tac "\<not> ia \<le> n")
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   prefer 2
   apply(rule_tac
      m="ia"
      in parserHF.pre_some_position_is_some_position)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(subgoal_tac "cd \<in> parserHF_configurations M")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      in parserHF.belongs_configurations)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(rule parserHF.derivation_initial_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(subgoal_tac "c \<in> parserHF_configurations M")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   prefer 2
   apply(rule_tac
      d="dh"
      in parserHF.belongs_configurations)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(rule parserHF.derivation_initial_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(force)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(subgoal_tac "d n = dh n")
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   prefer 2
   apply(rule sym)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(rule_tac
      ?d1.0="dh"
      and n="n"
      and m="ia"
      and ?d2.0="d"
      and x="0"
      and y="0"
      in parserHF.is_forward_deterministicHist_derivations_coincide)
              apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
              apply(force)
             apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
             apply(simp add: parserHF.derivation_initial_def)
            apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
            apply(force)
           apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
           apply(force)
          apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
          apply(force)
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
         apply(simp add: parserHF.derivation_initial_def)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
        apply(case_tac "d 0")
         apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
         apply(clarsimp)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" a)(*strict*)
        apply(clarsimp)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
       apply(case_tac "dh 0")
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
        apply(clarsimp)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" a)(*strict*)
       apply(clarsimp)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    prefer 2
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac "ia<i")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(erule_tac
      x="i"
      in allE)
    apply(clarsimp)
    apply(rule_tac
      x="ca"
      in bexI)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(subgoal_tac "cb \<in> parserHF_configurations M")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(subgoal_tac "cc \<in> parserHF_configurations M")
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply(simp add: parserHF_configurations_def parser_markers_def)
      apply(clarsimp)
      apply(rename_tac M dh n e d ca i ea ia eb ec x f fa fb fc h ha l la lb lc)(*strict*)
      apply(rule_tac
      A="set ca"
      in set_mp)
       apply(rename_tac M dh n e d ca i ea ia eb ec x f fa fb fc h ha l la lb lc)(*strict*)
       apply(force)
      apply(rename_tac M dh n e d ca i ea ia eb ec x f fa fb fc h ha l la lb lc)(*strict*)
      apply(force)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply (metis parserHF.belongs_configurations parserHF.derivation_initial_belongs)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply (metis parserHF.belongs_configurations parserHF.derivation_initial_belongs)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(subgoal_tac "i\<le>ia")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>hf\<in> parser_markers M. parserHF_conf_history cc = parserHF_conf_history cb @ hf")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    prefer 2
    apply(rule_tac
      d="d"
      and n="i"
      and m="ia-i"
      in parserHF.steps_extend_history_derivation)
        apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
        apply(force)
       apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
       apply(force)
      apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
      apply (metis parserHF.belongs_configurations parserHF.derivation_initial_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(simp add: get_configuration_def)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(simp add: get_configuration_def)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(clarsimp)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
   apply(rule_tac
      x="ca@hf"
      in bexI)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
   apply(subgoal_tac "cb \<in> parserHF_configurations M")
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
    apply(subgoal_tac "cc \<in> parserHF_configurations M")
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
     apply(simp add: parserHF_configurations_def parser_markers_def)
     apply(clarsimp)
     apply(rename_tac M dh n e d ca i ea ia eb ec hf x f fa fb fc h ha l la lb lc)(*strict*)
     apply(rule_tac
      A="set ca"
      in set_mp)
      apply(rename_tac M dh n e d ca i ea ia eb ec hf x f fa fb fc h ha l la lb lc)(*strict*)
      apply(force)
     apply(rename_tac M dh n e d ca i ea ia eb ec hf x f fa fb fc h ha l la lb lc)(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
    apply (metis parserHF.belongs_configurations parserHF.derivation_initial_belongs)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd" hf)(*strict*)
   apply (metis parserHF.belongs_configurations parserHF.derivation_initial_belongs)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule_tac
      x="derivation_drop (derivation_take d ia) n"
      in exI)
  apply(rule conjI)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(rule_tac
      m="ia-n"
      in parserHF.derivation_drop_preserves_derivation_prime)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(rule parserHF.derivation_take_preserves_derivation)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(rule parserHF.derivation_drop_preserves_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(rule parserHF.derivation_take_preserves_derivation)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(rule parserHF.derivation_take_preserves_belongs)
    apply(rule parserHF.derivation_initial_belongs)
     apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
     apply(force)
    apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
    apply(force)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(rule_tac
      x="ia-n"
      in exI)
   apply(simp add: maximum_of_domain_def derivation_drop_def derivation_take_def)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule conjI)
   apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: derivation_append_fit_def derivation_drop_def derivation_take_def)
  apply(rename_tac M dh n e c d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(simp add: parserHF_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac M dh n d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(rule_tac
      x="ia"
      in exI)
  apply(rule_tac
      x="eb"
      in exI)
  apply(rule_tac
      x="cc"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac M dh n d ca i ea cb ia eb cc ec "cd")(*strict*)
   apply(simp add: derivation_append_def derivation_drop_def derivation_take_def)
  apply(rename_tac M dh n d ca i ea cb ia eb cc ec "cd")(*strict*)
  apply(clarsimp)
  apply(rename_tac M dh n d ca i ea cb ia eb cc ec "cd" j e' c')(*strict*)
  apply(simp add: derivation_append_def derivation_drop_def derivation_take_def)
  done

lemma parserHF_inst_BF_BraSBRest_DetHSB_LaOp_axioms: "
  BF_BraSBRest_DetHSB_LaOp_axioms valid_parser parserHF_configurations
     parserHF_initial_configurations parser_step_labels
     parserHF_step_relation parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect parser_markers (@)
     (@) parserHF_conf_history parser_fixed_scheduler_extendable
     parserHF_conf_fixed"
  apply(simp add: BF_BraSBRest_DetHSB_LaOp_axioms_def)
  apply(rule parserHF_inst_AX_BF_BraSBRest_DetHSB_LaOp)
  done

lemma parserHF_inst_BF_BraSBRest_DetHDB_LaOp_axioms: "
  BF_BraSBRest_DetHDB_LaOp_axioms valid_parser parserHF_configurations
     parserHF_initial_configurations parser_step_labels
     parserHF_step_relation parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect parser_markers (@)
     (@) parserHF_conf_history parser_fixed_scheduler_extendable
     parserHF_get_fixed_scheduler_DB parserHF_conf_fixed"
  apply(simp add: BF_BraSBRest_DetHDB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "parserHF.is_forward_deterministicHist_SB M")
   apply(rename_tac M)(*strict*)
   apply (metis parserHF_inst_AX_BF_BraSBRest_DetHSB_LaOp)
  apply(rename_tac M)(*strict*)
  apply(thin_tac "nonblockingness_language (parserHF.unmarked_language M) (parserHF.marked_language M)")
  apply(rename_tac M)(*strict*)
  apply (metis parserHF.is_forward_deterministic_correspond_DB_SB)
  done

lemma parserHF_inst_BF_BraDBRest_DetHSB_LaOp_axioms: "
  BF_BraDBRest_DetHSB_LaOp_axioms valid_parser parserHF_configurations
     parserHF_initial_configurations parser_step_labels
     parserHF_step_relation parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect parser_markers (@)
     (@) parserHF_conf_history parser_fixed_scheduler_extendable
     parserHF_conf_fixed parserHF_get_fixed_scheduler_DB"
  apply(simp add: BF_BraDBRest_DetHSB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(rule_tac
      t="ATS_SchedF_DB.Nonblockingness_branching_restricted_DB
          parserHF_configurations parserHF_initial_configurations
          parser_step_labels parserHF_step_relation
          parserHF_marking_condition parser_fixed_scheduler_extendable
          parserHF_get_fixed_scheduler_DB M"
      and s="parserHF.Nonblockingness_branching_restricted M"
      in subst)
   apply(rename_tac M)(*strict*)
   apply(rule parserHF.Nonblockingness_branching_SB_DB_restricted)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_BraSBRest_DetHDB_LaOp_axioms valid_parser parserHF_configurations
     parserHF_initial_configurations parser_step_labels
     parserHF_step_relation parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect parser_markers (@)
     (@) parserHF_conf_history parser_fixed_scheduler_extendable
     parserHF_get_fixed_scheduler_DB parserHF_conf_fixed")
   apply(rename_tac M)(*strict*)
   apply(simp add: BF_BraSBRest_DetHDB_LaOp_axioms_def)
   apply(erule_tac
      x="M"
      in allE)
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply (metis parserHF.is_forward_deterministic_correspond_DB_SB)
   apply(rename_tac M)(*strict*)
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(rule parserHF_inst_BF_BraSBRest_DetHDB_LaOp_axioms)
  done

lemma parserHF_inst_BF_BraDBRest_DetHDB_LaOp_axioms: "
  BF_BraDBRest_DetHDB_LaOp_axioms valid_parser parserHF_configurations
     parserHF_initial_configurations parser_step_labels
     parserHF_step_relation parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect parser_markers (@)
     (@) parserHF_conf_history parser_fixed_scheduler_extendable
     parserHF_get_fixed_scheduler_DB"
  apply(simp add: BF_BraDBRest_DetHDB_LaOp_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(subgoal_tac "BF_BraDBRest_DetHSB_LaOp_axioms valid_parser parserHF_configurations
     parserHF_initial_configurations parser_step_labels
     parserHF_step_relation parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect parser_markers (@)
     (@) parserHF_conf_history parser_fixed_scheduler_extendable
     parserHF_conf_fixed parserHF_get_fixed_scheduler_DB")
   apply(rename_tac M)(*strict*)
   apply(simp add: BF_BraDBRest_DetHSB_LaOp_axioms_def)
   apply(erule_tac
      x="M"
      in allE)
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply (metis parserHF.is_forward_deterministic_correspond_DB_SB)
   apply(rename_tac M)(*strict*)
   apply(erule impE)
    apply(rename_tac M)(*strict*)
    apply(force)
   apply(rename_tac M)(*strict*)
   apply(force)
  apply(rename_tac M)(*strict*)
  apply(rule parserHF_inst_BF_BraDBRest_DetHSB_LaOp_axioms)
  done

lemma parserHF_inst_BF_Bra_OpLa_axioms: "
  BF_Bra_OpLa_axioms valid_parser parserHF_configurations
     parserHF_initial_configurations parser_step_labels
     parserHF_step_relation parserHF_marking_condition
     parserHF_marked_effect parserHF_unmarked_effect"
  apply(simp add: BF_Bra_OpLa_axioms_def)
  apply(clarsimp)
  apply(rename_tac M)(*strict*)
  apply(simp add: nonblockingness_language_def)
  apply(clarsimp)
  apply(rename_tac M xa)(*strict*)
  apply(simp add: prefix_closure_def prefix_def)
  apply(simp add: parserHF.unmarked_language_def)
  apply(clarsimp)
  apply(rename_tac M xa d)(*strict*)
  apply(simp add: parserHF.Nonblockingness_branching_def)
  apply(simp add: parserHF_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac M d i e c)(*strict*)
  apply(erule_tac
      x="derivation_take d i"
      in allE)
  apply(erule impE)
   apply(rename_tac M d i e c)(*strict*)
   apply(rename_tac M d i e c)(*strict*)
   apply(rule parserHF.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac M d i e c)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(erule impE)
   apply(rename_tac M d i e c)(*strict*)
   apply(rule maximum_of_domain_derivation_take)
   apply(force)
  apply(rename_tac M d i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac M d i e c dc x)(*strict*)
  apply(simp add: parserHF_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
  apply(rule_tac
      x="parserHF_conf_history ca"
      in exI)
  apply(rule conjI)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(simp add: parserHF.marked_language_def)
   apply(rule_tac
      x="derivation_append (derivation_take d i) dc i"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(rule parserHF.derivation_append_preserves_derivation_initial)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(force)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(rule parserHF.derivation_take_preserves_derivation_initial)
     apply(force)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(rule parserHF.derivation_append_preserves_derivation)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(rule parserHF.derivation_take_preserves_derivation)
      apply(force)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(force)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(simp add: derivation_take_def)
    apply(simp add: derivation_append_fit_def)
    apply(case_tac "dc 0")
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(force)
    apply(rename_tac M d i e c dc x ia ea ca a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac M d i e c dc x ia ea ca a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac M d i e c dc x ia ea ca option b)(*strict*)
    apply(case_tac option)
     apply(rename_tac M d i e c dc x ia ea ca option b)(*strict*)
     apply(clarsimp)
    apply(rename_tac M d i e c dc x ia ea ca option b a)(*strict*)
    apply(clarsimp)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(simp add: parserHF_marked_effect_def)
    apply(rule_tac
      x="ia"
      in exI)
    apply(rule_tac
      x="ea"
      in exI)
    apply(rule_tac
      x="ca"
      in exI)
    apply(clarsimp)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(simp add: parserHF.derivation_initial_def)
   apply(simp add: parserHF_marking_condition_def)
   apply(rule_tac
      x="ia"
      in exI)
   apply(rule_tac
      x="ea"
      in exI)
   apply(rule_tac
      x="ca"
      in exI)
   apply(clarsimp)
  apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
  apply(case_tac "ia<i")
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
   apply(erule_tac
      x="i"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule_tac
      x="c"
      in allE)
   apply(clarsimp)
   apply(simp add: derivation_append_def derivation_take_def)
  apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
  apply(subgoal_tac "\<exists>h\<in> parser_markers M. parserHF_conf_history SSc' = parserHF_conf_history SSc @ h" for SSc' SSc)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   prefer 2
   apply(rule_tac
      d="derivation_append (derivation_take d i) dc i"
      and n="i"
      and m="ia-i"
      in parserHF.steps_extend_history_derivation)
       apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
       apply(force)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(simp add: parserHF.derivation_initial_def)
      apply(rule parserHF.derivation_append_preserves_derivation)
        apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
        apply(rule parserHF.derivation_take_preserves_derivation)
        apply(force)
       apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
       apply(force)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(simp add: derivation_take_def derivation_append_fit_def)
      apply(case_tac "dc 0")
       apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
       apply(force)
      apply(rename_tac M d i e c dc x ia ea ca a)(*strict*)
      apply(clarsimp)
      apply(case_tac a)
      apply(rename_tac M d i e c dc x ia ea ca a option b)(*strict*)
      apply(clarsimp)
      apply(rename_tac M d i e c dc x ia ea ca option b)(*strict*)
      apply(case_tac option)
       apply(rename_tac M d i e c dc x ia ea ca option b)(*strict*)
       apply(clarsimp)
      apply(rename_tac M d i e c dc x ia ea ca option b a)(*strict*)
      apply(clarsimp)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     prefer 2
     apply(simp add: get_configuration_def derivation_append_def derivation_take_def)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(rule parserHF.belongs_configurations)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(rule parserHF.derivation_initial_belongs)
      apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
      apply(force)
     apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
     apply(force)
    apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
    apply(force)
   apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
   apply(simp add: get_configuration_def derivation_append_def derivation_take_def)
  apply(rename_tac M d i e c dc x ia ea ca)(*strict*)
  apply(force)
  done

interpretation "parserHF" : loc_autHF_10
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserHF_configurations"
  (* initial_configurations *)
  "parserHF_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserHF_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserHF_marking_condition"
  (* marked_effect *)
  "parserHF_marked_effect"
  (* unmarked_effect *)
  "parserHF_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserHF_get_destinations"
  (* histories *)
  "parser_markers"
  (* history_fragments *)
  "parser_markers"
  (* empty_history *)
  "parser_empty_history"
  (* empty_history_fragment *)
  "parser_empty_history_fragment"
  (* set_history *)
  "parserHF_set_history"
  (* extend_history *)
  "append"
  (* join_history_fragments *)
  "append"
  (* get_history *)
  "parserHF_conf_history"
  (* fixed_schedulers *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable *)
  "parser_fixed_scheduler_extendable"
  (* get_fixed_scheduler *)
  "parserHF_conf_fixed"
  (* get_fixed_scheduler_DB *)
  "parserHF_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHF_inst_AX_initial_configuration_belongs parserHF_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHF_inst_ATS_axioms parserHF_inst_ATS_History_axioms parserHF_inst_ATS_SchedF_SB_axioms parserHF_inst_ATS_SchedF_DB_axioms parserHF_inst_ATS_SchedF_SDB_axioms parserHF_inst_ATS_determHIST_SB_axioms parserHF_inst_ATS_Language_by_Finite_Derivations_axioms parserHF_inst_ATS_HistoryCT_SB_axioms parserHF_inst_ATS_HistoryCT_DB_axioms parserHF_inst_BF_BraSBRest_DetHDB_LaOp_axioms parserHF_inst_BF_BraSBRest_DetHSB_LaOp_axioms parserHF_inst_BF_BraDBRest_DetHSB_LaOp_axioms parserHF_inst_BF_BraDBRest_DetHDB_LaOp_axioms parserHF_inst_BF_Bra_OpLa_axioms )
  done

lemma parserHF_history_prefix_makes_prefix: "
  w1 \<in> parser_markers G
  \<Longrightarrow> ATS_History.history_fragment_prefixes parser_markers (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w2
  \<Longrightarrow> w1 \<sqsubseteq> w2"
  apply(simp add: parserHF.history_fragment_prefixes_def)
  apply(simp add: prefix_def)
  apply(subgoal_tac "w1 \<in> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}")
   prefer 2
   apply(clarsimp)
   apply(simp add: parser_markers_def)
  apply(subgoal_tac "w1 \<in> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}")
   prefer 2
   apply(force)
  apply(thin_tac "{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1} \<subseteq> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}")
  apply(thin_tac "w1 \<in> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}")
  apply(force)
  done

lemma parserHF_history_prefix_makes_prefix_mutual: "
  w1 \<in> parser_markers G
  \<Longrightarrow> w2 \<in> parser_markers G
  \<Longrightarrow> ATS_History.history_fragment_prefixes parser_markers (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<or> ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w1
  \<Longrightarrow> prefix w1 w2 \<or> prefix w2 w1"
  apply(erule disjE)
   apply(rule disjI1)
   apply(rule parserHF_history_prefix_makes_prefix)
    apply(force)
   apply(force)
  apply(rule disjI2)
  apply(rule parserHF_history_prefix_makes_prefix)
   apply(force)
  apply(force)
  done

lemma parserHF_is_forward_target_deterministicHist_DB_long: "
  valid_parser G
  \<Longrightarrow> parserHF.is_forward_target_deterministicHist_DB_long G"
  apply(simp add: parserHF.is_forward_target_deterministicHist_DB_long_def)
  apply(clarsimp)
  apply(rename_tac c d n c1 c2 e w1 w2)(*strict*)
  apply(simp add: parserHF_step_relation_def)
  apply(clarsimp)
  done

lemmas parserHF_interpretations =
  parser_interpretations
  parserHF_inst_AX_initial_configuration_belongs
  parserHF_inst_AX_step_relation_preserves_belongs
  parserHF_inst_ATS_axioms
  parserHF_inst_ATS_History_axioms
  parserHF_inst_ATS_SchedF_SB_axioms
  parserHF_inst_ATS_SchedF_DB_axioms
  parserHF_inst_ATS_SchedF_SDB_axioms
  parserHF_inst_ATS_determHIST_SB_axioms
  parserHF_inst_ATS_Language_by_Finite_Derivations_axioms
  parserHF_inst_ATS_HistoryCT_SB_axioms
  parserHF_inst_ATS_HistoryCT_DB_axioms
  parserHF_inst_BF_BraSBRest_DetHDB_LaOp_axioms
  parserHF_inst_BF_BraSBRest_DetHSB_LaOp_axioms
  parserHF_inst_BF_BraDBRest_DetHSB_LaOp_axioms
  parserHF_inst_BF_BraDBRest_DetHDB_LaOp_axioms
  parserHF_inst_BF_Bra_OpLa_axioms

end
