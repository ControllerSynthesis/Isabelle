section {*I\_kparser\_HFS*}
theory
  I_kparser_HFS

imports
  I_kparser_base

begin

record ('stack, 'event) parserHFS_conf =
  parserHFS_conf_fixed :: "'event list"
  parserHFS_conf_history :: "'event list"
  parserHFS_conf_stack :: "'stack list"
  parserHFS_conf_scheduler :: "'event list"

definition parserHFS_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHFS_conf set"
  where
    "parserHFS_configurations G \<equiv>
  {\<lparr>parserHFS_conf_fixed = f,
    parserHFS_conf_history = h,
    parserHFS_conf_stack = l,
    parserHFS_conf_scheduler = r\<rparr>
    | f h l r.
    set l \<subseteq> parser_nonterms G
    \<and> prefix f r
    \<and> suffix h (butlast_if_match f (parser_bottom G))
    \<and> set r \<subseteq> parser_events G
    \<and> set h \<subseteq> parser_events G
    \<and> parser_bottom G \<notin> set h
    \<and> (\<exists>w. r = w @ [parser_bottom G]
            \<and> parser_bottom G \<notin> set w)}"

definition parserHFS_configurations_ALT :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHFS_conf set"
  where
    "parserHFS_configurations_ALT G \<equiv>
  {\<lparr>parserHFS_conf_fixed = f,
    parserHFS_conf_history = h,
    parserHFS_conf_stack = l,
    parserHFS_conf_scheduler = r\<rparr>
    | f h l r.
    set l \<subseteq> parser_nonterms G
    \<and> prefix f r
    \<and> suffix h (butlast_if_match f (parser_bottom G))
    \<and> set h \<subseteq> parser_events G
    \<and> parser_bottom G \<notin> set h
    \<and> r \<in> parser_schedulers G}"

lemma parserHFS_configurations_ALT_vs_parserHFS_configurations: "
  valid_parser G
  \<Longrightarrow> parserHFS_configurations_ALT G = parserHFS_configurations G"
  apply(simp add: parser_schedulers_def parserHFS_configurations_def parserHFS_configurations_ALT_def)
  apply(rule antisym)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac f h l v)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma parserHFS_configurations_characterization: "
  valid_parser G
  \<Longrightarrow> \<lparr>parserHFS_conf_fixed=f, parserHFS_conf_history=h, parserHFS_conf_stack = l, parserHFS_conf_scheduler=r\<rparr> \<in> parserHFS_configurations G
  \<Longrightarrow> (\<exists>f'. parser_bottom G\<notin>(set f') \<and> f=f'@[parser_bottom G] \<and> (\<exists>h'. h=h'@f') \<and> (r=f)) \<or> (parser_bottom G \<notin> set f \<and> (\<exists>r'. r=f@r'@[parser_bottom G]))"
  apply(case_tac "parser_bottom G \<in> set f")
   apply(rule disjI1)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: prefix_def suffix_def)
   apply(clarsimp)
   apply(rename_tac w c ca)(*strict*)
   apply(case_tac c)
    apply(rename_tac w c ca)(*strict*)
    prefer 2
    apply(rename_tac w c ca a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac w c ca a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac w c ca a list)(*strict*)
    apply(thin_tac "c=a#list")
    apply(clarsimp)
   apply(rename_tac w c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac w ca)(*strict*)
   apply(rule_tac
      t="butlast_if_match (w @ [parser_bottom G]) (parser_bottom G)"
      and s="w"
      in ssubst)
    apply(rename_tac w ca)(*strict*)
    apply(rule butlast_if_match_direct)
    apply(force)
   apply(rename_tac w ca)(*strict*)
   apply(force)
  apply(rule disjI2)
  apply(clarsimp)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac w c ca)(*strict*)
  apply(case_tac c)
   apply(rename_tac w c ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac w c ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac w c ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w c ca a list)(*strict*)
  apply(thin_tac "c=a#list")
  apply(clarsimp)
  done

definition parserHFS_step_relation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHFS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHFS_conf
 \<Rightarrow> bool"
  where
    "parserHFS_step_relation M c1 p c2 \<equiv>
  p \<in> parser_rules M \<and> ((\<exists>x. parserHFS_conf_stack c1 = x @ (rule_lpop p) \<and> parserHFS_conf_stack c2=x@(rule_lpush p)) \<and> (\<exists>x. parserHFS_conf_scheduler c1=(rule_rpop p)@x \<and> parserHFS_conf_scheduler c2=(rule_rpush p)@x \<and> (\<exists>y. parserHFS_conf_scheduler c2 = y @ [parser_bottom M]) \<and> parserHFS_conf_history c2=parserHFS_conf_history c1@(drop (length(parserHFS_conf_fixed c1)) (butlast_if_match (rule_rpop p) (parser_bottom M))) \<and> parserHFS_conf_fixed c2 = (rule_rpush p) @ (drop (length (rule_rpop p)) (parserHFS_conf_fixed c1))))"

definition parserHFS_step_relation_ALT :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHFS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserHFS_conf
 \<Rightarrow> bool"
  where
    "parserHFS_step_relation_ALT G c1 e c2 \<equiv>
  e \<in> parser_rules G
  \<and> (\<exists>x. parserHFS_conf_stack c1 = x @ rule_lpop e
         \<and> parserHFS_conf_stack c2 = x @ rule_lpush e)
  \<and> (\<exists>x. parserHFS_conf_scheduler c1 = rule_rpop e @ x
         \<and> parserHFS_conf_scheduler c2 = rule_rpush e @ x)
  \<and> (\<exists>y. parserHFS_conf_scheduler c2 = y @ [parser_bottom G])
  \<and> parserHFS_conf_history c2
      = parserHFS_conf_history c1
        @ drop
            (length(parserHFS_conf_fixed c1))
            (butlast_if_match (rule_rpop e) (parser_bottom G))
  \<and> parserHFS_conf_fixed c2
      = rule_rpush e
        @ drop
            (length (rule_rpop e))
            (parserHFS_conf_fixed c1)"

lemma parserHFS_step_relation_ALT_vs_parserHFS_step_relation: "
  parserHFS_step_relation_ALT M c1 p c2
  = parserHFS_step_relation M c1 p c2"
  apply(simp add: parserHFS_step_relation_ALT_def parserHFS_step_relation_def)
  apply(force)
  done

definition parserHFS_initial_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHFS_conf set"
  where
    "parserHFS_initial_configurations G \<equiv>
  {c. parserHFS_conf_history c = []
      \<and> parserHFS_conf_fixed c = []
      \<and> parserHFS_conf_stack c = [parser_initial G]}
  \<inter> parserHFS_configurations G"

definition parserHFS_marking_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserHFS_conf set"
  where
    "parserHFS_marking_configurations G \<equiv>
  {c. \<exists>f \<in> parser_marking G. \<exists>w.
      parserHFS_conf_stack c = w @ [f]
      \<and> parserHFS_conf_scheduler c = [parser_bottom G]}
  \<inter> parserHFS_configurations G"

definition parserHFS_marking_condition :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf)derivation
  \<Rightarrow> bool"
  where
    "parserHFS_marking_condition G d \<equiv>
  \<exists>i e c.
    d i = Some (pair e c)
    \<and> c \<in> parserHFS_marking_configurations G"

definition parserHFS_marked_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf)derivation
  \<Rightarrow> 'event list set"
  where
    "parserHFS_marked_effect G d =
  {w. \<exists>i e c.
      d i = Some (pair e c)
      \<and> w = parserHFS_conf_history c
      \<and> c \<in> parserHFS_marking_configurations G}"

definition parserHFS_unmarked_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf)derivation
  \<Rightarrow> 'event list set"
  where
    "parserHFS_unmarked_effect G d \<equiv>
  {w. \<exists>i e c.
      d i = Some (pair e c)
      \<and> parserHFS_conf_history c = w}"

definition parserHFS_get_destinations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf)derivation_configuration
  \<Rightarrow> ('stack, 'event) parser_destinations set"
  where
    "parserHFS_get_destinations G der_conf \<equiv>
  case der_conf of pair e c \<Rightarrow>
    state ` set (parserHFS_conf_stack c)
    \<union> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {rule e'})"

lemma parserHFS_fdeterm_rpops_mutual_prefix: "
  c\<in> parserHFS_configurations G
  \<Longrightarrow> c1\<in> parserHFS_configurations G
  \<Longrightarrow> c2\<in> parserHFS_configurations G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> prefix (rule_rpop e1) (rule_rpop e2) \<or> prefix (rule_rpop e2) (rule_rpop e1)"
  apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac f h x xa xb xc y ya w)(*strict*)
  apply(case_tac c)
  apply(rename_tac f h x xa xb xc y ya w parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
  apply(case_tac c1)
  apply(rename_tac f h x xa xb xc y ya w parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(case_tac c2)
  apply(rename_tac f h x xa xb xc y ya w parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera parserHFS_conf_fixedb parserHFS_conf_historyb parserHFS_conf_stackb parserHFS_conf_schedulerb)(*strict*)
  apply(clarsimp)
  apply(rename_tac f h x xa xb xc y ya w)(*strict*)
  apply(case_tac e1)
  apply(rename_tac f h x xa xb xc y ya w rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(case_tac e2)
  apply(rename_tac f h x xa xb xc y ya w rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(rename_tac f h x xa xb xc y ya w rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac f x xa xb xc y ya w rule_lpop rule_rpop rule_lpush rule_rpush rule_lpopa rule_rpopa rule_lpusha rule_rpusha c ca cb cc "cd" ce)(*strict*)
  apply(thin_tac "\<lparr>rule_lpop = rule_lpop, rule_rpop = rule_rpop, rule_lpush = rule_lpush, rule_rpush = rule_rpush\<rparr> \<in> parser_rules G")
  apply(thin_tac "\<lparr>rule_lpop = rule_lpopa, rule_rpop = rule_rpopa, rule_lpush = rule_lpusha, rule_rpush = rule_rpusha\<rparr> \<in> parser_rules G")
  apply(thin_tac "set rule_lpusha \<subseteq> parser_nonterms G")
  apply(thin_tac "set (drop (length f) (butlast_if_match rule_rpop (parser_bottom G))) \<subseteq> parser_events G")
  apply(thin_tac "set (drop (length f) (butlast_if_match rule_rpopa (parser_bottom G))) \<subseteq> parser_events G")
  apply(thin_tac "parser_bottom G \<notin> set (drop (length f) (butlast_if_match rule_rpop (parser_bottom G)))")
  apply(thin_tac "parser_bottom G \<notin> set (drop (length f) (butlast_if_match rule_rpopa (parser_bottom G)))")
  apply(thin_tac "set rule_lpopa \<subseteq> parser_nonterms G")
  apply(thin_tac "set rule_lpush \<subseteq> parser_nonterms G")
  apply(thin_tac "set (butlast_if_match f (parser_bottom G)) \<subseteq> parser_events G")
  apply(thin_tac "parser_bottom G \<notin> set cc")
  apply(thin_tac "parser_bottom G \<notin> set (butlast_if_match f (parser_bottom G))")
  apply(thin_tac "x @ rule_lpop = xb @ rule_lpopa")
  apply(clarsimp)
  apply(rename_tac f x xa xb xc y ya w rule_rpop rule_rpush rule_rpopa rule_rpusha c ca cb cc "cd" ce)(*strict*)
  apply(rename_tac r1 r2 r3 r4 c ca cb cc ccx ce)
  apply(rename_tac f x xa xb xc y ya w r1 r2 r3 r4 c ca cb cc ccx ce)(*strict*)
  apply(subgoal_tac "prefix r1 r3 \<or> prefix r3 r1")
   apply(rename_tac f x xa xb xc y ya w r1 r2 r3 r4 c ca cb cc ccx ce)(*strict*)
   apply(erule disjE)
    apply(rename_tac f x xa xb xc y ya w r1 r2 r3 r4 c ca cb cc ccx ce)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac f x xa xb xc y ya w r1 r2 r3 r4 c ca cb cc ccx ce)(*strict*)
   apply(simp add: prefix_def)
  apply(rename_tac f x xa xb xc y ya w r1 r2 r3 r4 c ca cb cc ccx ce)(*strict*)
  apply(rule mutual_prefix_prefix)
  apply(force)
  done

definition parserHFS_string_state :: "
  ('stack, 'event) parserHFS_conf
  \<Rightarrow> 'event list"
  where
    "parserHFS_string_state c \<equiv>
  parserHFS_conf_scheduler c"

lemma parserHFS_inst_AX_initial_configuration_belongs: "
  (\<forall>G. valid_parser G \<longrightarrow> parserHFS_initial_configurations G \<subseteq> parserHFS_configurations G)"
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: parserHFS_initial_configurations_def)
  done

lemma parserHFS_inst_AX_step_relation_preserves_belongs: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1 e c2. parserHFS_step_relation G c1 e c2 \<longrightarrow> c1 \<in> parserHFS_configurations G \<longrightarrow> e \<in> parser_step_labels G \<and> c2 \<in> parserHFS_configurations G))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(simp add: parser_step_labels_def parserHFS_step_relation_def)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G e c2 f h l w)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G e c2 f h w x xa y)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G e c2 f h w x xa y parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e f h w x xa y)(*strict*)
  apply(simp add: parser_step_labels_def)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G e f h w x xa y)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac G e f h w x xa y)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G e f h w x xa y)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac G e f h w x xa y)(*strict*)
  apply(subgoal_tac "set (rule_rpush e) \<subseteq> parser_events G")
   apply(rename_tac G e f h w x xa y)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac G e f h w x xa y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "set xa \<subseteq> parser_events G")
   apply(rename_tac G e f h w x xa y)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
   apply(rule_tac
      B="set (rule_rpop e @ xa)"
      in subset_trans)
    apply(rename_tac G e f h w x xa y)(*strict*)
    apply(force)
   apply(rename_tac G e f h w x xa y)(*strict*)
   apply(rule_tac
      t="rule_rpop e @ xa"
      and s="w @ [parser_bottom G]"
      in ssubst)
    apply(rename_tac G e f h w x xa y)(*strict*)
    apply(force)
   apply(rename_tac G e f h w x xa y)(*strict*)
   apply(thin_tac "w @ [parser_bottom G] = rule_rpop e @ xa")
   apply(force)
  apply(rename_tac G e f h w x xa y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "set (drop (length f) (butlast_if_match (rule_rpop e) (parser_bottom G))) \<subseteq> parser_events G")
   apply(rename_tac G e f h w x xa y)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
   apply(rule_tac
      B="set(butlast_if_match (rule_rpop e) (parser_bottom G))"
      in subset_trans)
    apply(rename_tac G e f h w x xa y)(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac G e f h w x xa y)(*strict*)
   apply(rule_tac
      B="set(rule_rpop e)"
      in subset_trans)
    apply(rename_tac G e f h w x xa y)(*strict*)
    apply(rule set_butlast_if_match_is_subset)
   apply(rename_tac G e f h w x xa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
   apply(simp add: kPrefix_def)
   apply(erule disjE)
    apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
    apply(rule_tac
      A="set wa"
      in set_mp)
     apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
     apply(rule_tac
      B="parser_events G - {parser_bottom G}"
      in subset_trans)
      apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
      apply(force)
     apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
     apply(force)
    apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
    apply(rule_tac
      A="set(take k wa)"
      in set_mp)
     apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
    apply(force)
   apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
   apply(rule_tac
      A="set (take (k - length wa) [parser_bottom G])"
      in set_mp)
    apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
    apply(rule_tac
      B="set ([parser_bottom G])"
      in subset_trans)
     apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
    apply(force)
   apply(rename_tac G e f h w x xa y xb k wa xd)(*strict*)
   apply(force)
  apply(rename_tac G e f h w x xa y)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "(\<exists>w. rule_rpush e @ xa = w @ [parser_bottom G] \<and> parser_bottom G \<notin> set w)")
   apply(rename_tac G e f h w x xa y)(*strict*)
   prefer 2
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G e f h w x xa y k wa xc)(*strict*)
   apply(case_tac "(\<exists>x. x @ [parser_bottom G] = kPrefix k (wa @ [parser_bottom G]))")
    apply(rename_tac G e f h w x xa y k wa xc)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f h w x xa y k wa xc xb xd)(*strict*)
    apply(case_tac xa)
     apply(rename_tac G e f h w x xa y k wa xc xb xd)(*strict*)
     apply(clarsimp)
     apply(rename_tac G e f h w x y k wa xc xb xd)(*strict*)
     apply(rule_tac
      x="xb"
      in exI)
     apply(clarsimp)
     apply(simp add: kPrefix_def)
     apply(case_tac "k-length wa")
      apply(rename_tac G e f h w x y k wa xc xb xd)(*strict*)
      apply(clarsimp)
      apply(case_tac "take k wa")
       apply(rename_tac G e f h w x y k wa xc xb xd)(*strict*)
       apply(force)
      apply(rename_tac G e f h w x y k wa xc xb xd a list)(*strict*)
      apply(subgoal_tac "\<exists>w' x'. take k wa = w' @ [x']")
       apply(rename_tac G e f h w x y k wa xc xb xd a list)(*strict*)
       prefer 2
       apply(rule NonEmptyListHasTailElem)
       apply(force)
      apply(rename_tac G e f h w x y k wa xc xb xd a list)(*strict*)
      apply(thin_tac "take k wa = a # list")
      apply(clarsimp)
      apply(rename_tac G e f h x y k wa xc xb w')(*strict*)
      apply(subgoal_tac "xc@xb@ [parser_bottom G]=w'@ [parser_bottom G]")
       apply(rename_tac G e f h x y k wa xc xb w')(*strict*)
       prefer 2
       apply(simp (no_asm_simp))
      apply(rename_tac G e f h x y k wa xc xb w')(*strict*)
      apply(subgoal_tac "xc@xb=w'")
       apply(rename_tac G e f h x y k wa xc xb w')(*strict*)
       prefer 2
       apply(thin_tac "xb @ [parser_bottom G] = rule_rpush e")
       apply(thin_tac "xc @ rule_rpush e = w' @ [parser_bottom G]")
       apply(force)
      apply(rename_tac G e f h x y k wa xc xb w')(*strict*)
      apply(clarify)
      apply(rule_tac
      v="xc"
      and w="xb"
      and a="parser_bottom G"
      in set_append_contra2)
       apply(rename_tac G e f h x y k wa xc xb w')(*strict*)
       apply(force)
      apply(rename_tac G e f h x y k wa xc xb w')(*strict*)
      apply(force)
     apply(rename_tac G e f h w x y k wa xc xb xd nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac G e f h x y k wa xc xb nat)(*strict*)
     apply(case_tac "rule_rpush e")
      apply(rename_tac G e f h x y k wa xc xb nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac G e f h x y k wa xc xb nat a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
      apply(rename_tac G e f h x y k wa xc xb nat a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac G e f h x y k wa xc xb nat a list)(*strict*)
     apply(thin_tac "rule_rpush e = a # list")
     apply(clarsimp)
    apply(rename_tac G e f h w x xa y k wa xc xb xd a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
     apply(rename_tac G e f h w x xa y k wa xc xb xd a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e f h w x xa y k wa xc xb xd a list)(*strict*)
    apply(thin_tac "xa = a # list")
    apply(clarsimp)
    apply(rename_tac G e f h x k wa xc xb xd w')(*strict*)
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(case_tac "k-length wa")
     apply(rename_tac G e f h x k wa xc xb xd w')(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<in> set (take k wa)")
      apply(rename_tac G e f h x k wa xc xb xd w')(*strict*)
      apply(force)
     apply(rename_tac G e f h x k wa xc xb xd w')(*strict*)
     apply(rule_tac
      t="take k wa"
      and s="xd @ [parser_bottom G]"
      in ssubst)
      apply(rename_tac G e f h x k wa xc xb xd w')(*strict*)
      apply(force)
     apply(rename_tac G e f h x k wa xc xb xd w')(*strict*)
     apply(simp (no_asm))
    apply(rename_tac G e f h x k wa xc xb xd w' nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e f h w x xa y k wa xc)(*strict*)
   apply(clarsimp)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length wa")
    apply(rename_tac G e f h w x xa y k wa xc)(*strict*)
    prefer 2
    apply(rename_tac G e f h w x xa y k wa xc nat)(*strict*)
    apply(force)
   apply(rename_tac G e f h w x xa y k wa xc)(*strict*)
   apply(clarsimp)
   apply(case_tac xa)
    apply(rename_tac G e f h w x xa y k wa xc)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e f h w x xa y k wa xc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac G e f h w x xa y k wa xc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e f h w x xa y k wa xc a list)(*strict*)
   apply(thin_tac "xa = a # list")
   apply(clarsimp)
   apply(rename_tac G e f h x k wa xc w')(*strict*)
   apply(subgoal_tac "parser_bottom G \<in> set (take k wa)")
    apply(rename_tac G e f h x k wa xc w')(*strict*)
    apply(force)
   apply(rename_tac G e f h x k wa xc w')(*strict*)
   apply(rule_tac
      A="set(xc @ rule_rpush e)"
      in set_mp)
    apply(rename_tac G e f h x k wa xc w')(*strict*)
    apply(force)
   apply(rename_tac G e f h x k wa xc w')(*strict*)
   apply(simp (no_asm))
   apply(force)
  apply(rename_tac G e f h w x xa y)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e f h w x xa wa)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G e f h w x xa wa c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G e f h w x xa wa c)(*strict*)
   apply(subgoal_tac "prefix f (rule_rpop e) \<or> prefix (rule_rpop e) f")
    apply(rename_tac G e f h w x xa wa c)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac G e f h w x xa wa c)(*strict*)
   apply(erule disjE)
    apply(rename_tac G e f h w x xa wa c)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e f h w x xa wa c ca)(*strict*)
    apply(case_tac e)
    apply(rename_tac G e f h w x xa wa c ca rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(clarsimp)
    apply(rename_tac G f h w x xa wa ca rule_lpop rule_lpush rule_rpush)(*strict*)
    apply(force)
   apply(rename_tac G e f h w x xa wa c)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e h w x wa c ca)(*strict*)
   apply(case_tac e)
   apply(rename_tac G e h w x wa c ca rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(clarsimp)
   apply(rename_tac G h w x wa c ca rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
   apply(force)
  apply(rename_tac G e f h w x xa wa c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G e f h w x xa wa c)(*strict*)
   apply(simp add: suffix_def)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G e f w x xa wa c ca k wb xc)(*strict*)
   apply(case_tac xa)
    apply(rename_tac G e f w x xa wa c ca k wb xc)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f w x wa c ca k wb xc)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length wb")
     apply(rename_tac G e f w x wa c ca k wb xc)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<in> set wb")
      apply(rename_tac G e f w x wa c ca k wb xc)(*strict*)
      apply(force)
     apply(rename_tac G e f w x wa c ca k wb xc)(*strict*)
     apply(rule_tac
      A="set (take k wb)"
      in set_mp)
      apply(rename_tac G e f w x wa c ca k wb xc)(*strict*)
      apply(rule set_take_subset)
     apply(rename_tac G e f w x wa c ca k wb xc)(*strict*)
     apply(rule_tac
      t="take k wb"
      and s="xc @ wa @ [parser_bottom G]"
      in ssubst)
      apply(rename_tac G e f w x wa c ca k wb xc)(*strict*)
      apply(force)
     apply(rename_tac G e f w x wa c ca k wb xc)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac G e f w x wa c ca k wb xc nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f x wa c ca k xc nat)(*strict*)
    apply(subgoal_tac "k=Suc nat+length xc+length wa")
     apply(rename_tac G e f x wa c ca k xc nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G e f x wa c ca k xc nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f x wa c ca xc nat)(*strict*)
    apply(rule_tac
      t="min (length xc + length wa) (Suc (nat + length xc + length wa))"
      and s="(length xc + length wa)"
      in ssubst)
     apply(rename_tac G e f x wa c ca xc nat)(*strict*)
     apply(force)
    apply(rename_tac G e f x wa c ca xc nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f x wa c ca xc)(*strict*)
    apply(rule_tac
      t="drop (Suc (length xc + length wa)) f"
      and s="[]"
      in ssubst)
     apply(rename_tac G e f x wa c ca xc)(*strict*)
     apply(rule drop_all)
     apply(rule_tac
      j="length (f@c)"
      in le_trans)
      apply(rename_tac G e f x wa c ca xc)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac G e f x wa c ca xc)(*strict*)
     apply(force)
    apply(rename_tac G e f x wa c ca xc)(*strict*)
    apply(rule_tac
      t="butlast_if_match (wa @ [parser_bottom G]) (parser_bottom G)"
      and s="wa"
      in ssubst)
     apply(rename_tac G e f x wa c ca xc)(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac G e f x wa c ca xc)(*strict*)
    apply(rule_tac
      t=" butlast_if_match (xc @ wa @ [parser_bottom G]) (parser_bottom G)"
      and s="xc @ wa"
      in ssubst)
     apply(rename_tac G e f x wa c ca xc)(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac G e f x wa c ca xc)(*strict*)
    apply(case_tac c)
     apply(rename_tac G e f x wa c ca xc)(*strict*)
     apply(clarsimp)
     apply(rename_tac G e x wa ca xc)(*strict*)
     apply(rule_tac
      t="butlast_if_match (xc @ wa @ [parser_bottom G]) (parser_bottom G)"
      and s="xc@wa"
      in ssubst)
      apply(rename_tac G e x wa ca xc)(*strict*)
      apply(rule butlast_if_match_direct)
      apply(force)
     apply(rename_tac G e x wa ca xc)(*strict*)
     apply(force)
    apply(rename_tac G e f x wa c ca xc a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac G e f x wa c ca xc a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e f x wa c ca xc a list)(*strict*)
    apply(thin_tac "c=a#list")
    apply(clarsimp)
    apply(rename_tac G e f x wa ca xc w')(*strict*)
    apply(subgoal_tac "prefix f xc \<or> prefix xc f")
     apply(rename_tac G e f x wa ca xc w')(*strict*)
     prefer 2
     apply(rule mutual_prefix_prefix)
     apply(force)
    apply(rename_tac G e f x wa ca xc w')(*strict*)
    apply(erule disjE)
     apply(rename_tac G e f x wa ca xc w')(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
    apply(rename_tac G e f x wa ca xc w')(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e x ca xc w' c)(*strict*)
    apply(case_tac c)
     apply(rename_tac G e x ca xc w' c)(*strict*)
     apply(force)
    apply(rename_tac G e x ca xc w' c a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
     apply(rename_tac G e x ca xc w' c a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x ca xc w' c a list)(*strict*)
    apply(thin_tac "c=a#list")
    apply(clarsimp)
    apply(rename_tac G e x ca xc w' w'a x')(*strict*)
    apply(case_tac "x'=parser_bottom G")
     apply(rename_tac G e x ca xc w' w'a x')(*strict*)
     apply(clarsimp)
    apply(rename_tac G e x ca xc w' w'a x')(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="butlast_if_match (xc @ w'a @ [x']) (parser_bottom G)"
      and s="xc @ w'a @ [x']"
      in ssubst)
     apply(rename_tac G e x ca xc w' w'a x')(*strict*)
     apply(rule butlast_if_match_direct2)
      apply(rename_tac G e x ca xc w' w'a x')(*strict*)
      apply(force)
     apply(rename_tac G e x ca xc w' w'a x')(*strict*)
     apply(force)
    apply(rename_tac G e x ca xc w' w'a x')(*strict*)
    apply(clarsimp)
   apply(rename_tac G e f w x xa wa c ca k wb xc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac G e f w x xa wa c ca k wb xc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e f w x xa wa c ca k wb xc a list)(*strict*)
   apply(thin_tac "xa=a#list")
   apply(clarsimp)
   apply(rename_tac G e f x c ca k wb xc w')(*strict*)
   apply(case_tac c)
    apply(rename_tac G e f x c ca k wb xc w')(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x ca k wb xc w')(*strict*)
    apply(rule_tac
      t="butlast_if_match (kPrefix k (wb @ [parser_bottom G]) @ w' @ [parser_bottom G]) (parser_bottom G)"
      and s="kPrefix k (wb @ [parser_bottom G]) @ w'"
      in ssubst)
     apply(rename_tac G e x ca k wb xc w')(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac G e x ca k wb xc w')(*strict*)
    apply(rule_tac
      t="drop (Suc (length (kPrefix k (wb @ [parser_bottom G])) + length w')) (butlast_if_match (kPrefix k (wb @ [parser_bottom G])) (parser_bottom G))"
      and s="[]"
      in ssubst)
     apply(rename_tac G e x ca k wb xc w')(*strict*)
     apply(rule drop_all)
     apply(rule_tac
      j="length (kPrefix k (wb @ [parser_bottom G]))"
      in le_trans)
      apply(rename_tac G e x ca k wb xc w')(*strict*)
      apply(rule butlast_if_match_length_le)
     apply(rename_tac G e x ca k wb xc w')(*strict*)
     apply(force)
    apply(rename_tac G e x ca k wb xc w')(*strict*)
    apply(rule_tac
      t="butlast_if_match (rule_rpush e @ w' @ [parser_bottom G]) (parser_bottom G)"
      and s="rule_rpush e @ w'"
      in ssubst)
     apply(rename_tac G e x ca k wb xc w')(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac G e x ca k wb xc w')(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="ca@xc"
      in exI)
    apply(force)
   apply(rename_tac G e f x c ca k wb xc w' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac G e f x c ca k wb xc w' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e f x c ca k wb xc w' a list)(*strict*)
   apply(thin_tac "c=a#list")
   apply(clarsimp)
   apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length wb")
    apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
    prefer 2
    apply(rename_tac G e f x ca k wb xc w' w'a nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="butlast_if_match (take k wb) (parser_bottom G)"
      and s="take k wb"
      in ssubst)
    apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(force)
   apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
   apply(rule_tac
      t="min (length wb) k"
      and s="k"
      in ssubst)
    apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
    apply(force)
   apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
   apply(subgoal_tac "prefix f (take k wb) \<or> prefix (take k wb) f")
    apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
   apply(erule disjE)
    apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
    apply(rule_tac
      t="butlast_if_match f (parser_bottom G)"
      and s="f"
      in ssubst)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(rule_tac
      B="set(f@c)"
      in nset_mp)
      apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(rule_tac
      t="f@c"
      and s="take k wb"
      in ssubst)
      apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
      apply(force)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(force)
    apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
    apply(rule_tac
      t="drop (length f) (take k wb)"
      and s="c"
      in ssubst)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(rule_tac
      t="take k wb"
      and s="f@c"
      in ssubst)
      apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
      apply(force)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
    apply(subgoal_tac "drop k f = []")
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     prefer 2
     apply(rule drop_all)
     apply(rule_tac
      j="length (take k wb)"
      in le_trans)
      apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
      apply(rule_tac
      j="length (f@c)"
      in le_trans)
       apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
       apply(simp (no_asm))
      apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
      apply(force)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(force)
    apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="butlast_if_match (rule_rpush e) (parser_bottom G)"
      and s="rule_rpush e"
      in ssubst)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(rule_tac
      B="set(xc @ rule_rpush e)"
      in nset_mp)
      apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(rule_tac
      t="xc @ rule_rpush e"
      and s="take k wb"
      in ssubst)
      apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
      apply(force)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(force)
    apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
    apply(rule_tac
      t="f@c"
      and s="take k wb"
      in ssubst)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(force)
    apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
    apply(rule_tac
      t="take k wb"
      and s="xc @ rule_rpush e"
      in ssubst)
     apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
     apply(force)
    apply(rename_tac G e f x ca k wb xc w' w'a c)(*strict*)
    apply(rule_tac
      x="ca@xc"
      in exI)
    apply(force)
   apply(rename_tac G e f x ca k wb xc w' w'a)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G e x ca k wb xc w'a c)(*strict*)
   apply(case_tac c)
    apply(rename_tac G e x ca k wb xc w'a c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x ca k wb xc w'a)(*strict*)
    apply(rule_tac
      t="butlast_if_match (take k wb) (parser_bottom G)"
      and s="take k wb"
      in ssubst)
     apply(rename_tac G e x ca k wb xc w'a)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(force)
    apply(rename_tac G e x ca k wb xc w'a)(*strict*)
    apply(rule_tac
      t="butlast_if_match (rule_rpush e) (parser_bottom G)"
      and s="rule_rpush e"
      in ssubst)
     apply(rename_tac G e x ca k wb xc w'a)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(rule_tac
      B="set(xc @ rule_rpush e)"
      in nset_mp)
      apply(rename_tac G e x ca k wb xc w'a)(*strict*)
      apply(simp (no_asm))
     apply(rename_tac G e x ca k wb xc w'a)(*strict*)
     apply(rule_tac
      t="xc @ rule_rpush e"
      and s="take k wb"
      in ssubst)
      apply(rename_tac G e x ca k wb xc w'a)(*strict*)
      apply(force)
     apply(rename_tac G e x ca k wb xc w'a)(*strict*)
     apply(force)
    apply(rename_tac G e x ca k wb xc w'a)(*strict*)
    apply(rule_tac
      x="ca@xc"
      in exI)
    apply(force)
   apply(rename_tac G e x ca k wb xc w'a c a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
    apply(rename_tac G e x ca k wb xc w'a c a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e x ca k wb xc w'a c a list)(*strict*)
   apply(thin_tac "c=a#list")
   apply(clarsimp)
   apply(rename_tac G e x ca k wb xc w'a w' x')(*strict*)
   apply(rule_tac
      t="butlast_if_match (take k wb @ w' @ [x']) (parser_bottom G)"
      and s="take k wb @ w' @ [x']"
      in ssubst)
    apply(rename_tac G e x ca k wb xc w'a w' x')(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(force)
   apply(rename_tac G e x ca k wb xc w'a w' x')(*strict*)
   apply(rule_tac
      t="butlast_if_match (rule_rpush e @ w' @ [x']) (parser_bottom G)"
      and s="rule_rpush e @ w' @ [x']"
      in ssubst)
    apply(rename_tac G e x ca k wb xc w'a w' x')(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(force)
   apply(rename_tac G e x ca k wb xc w'a w' x')(*strict*)
   apply(rule_tac
      x="ca@xc"
      in exI)
   apply(force)
  apply(rename_tac G e f h w x xa wa c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parser_bottom G \<in> set ((butlast_if_match (rule_rpop e) (parser_bottom G)))")
   apply(rename_tac G e f h w x xa wa c)(*strict*)
   prefer 2
   apply(rule_tac
      A="set (drop (length f) (butlast_if_match (rule_rpop e) (parser_bottom G)))"
      in set_mp)
    apply(rename_tac G e f h w x xa wa c)(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac G e f h w x xa wa c)(*strict*)
   apply(force)
  apply(rename_tac G e f h w x xa wa c)(*strict*)
  apply(case_tac "rule_rpop e")
   apply(rename_tac G e f h w x xa wa c)(*strict*)
   apply(unfold butlast_if_match_def)
   apply(force)
  apply(rename_tac G e f h w x xa wa c a list)(*strict*)
  apply(subgoal_tac " parser_bottom G \<in> set (drop (length f) (if last (rule_rpop e) = parser_bottom G then butlast (rule_rpop e) else rule_rpop e))")
   apply(rename_tac G e f h w x xa wa c a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e f h w x xa wa c a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. rule_rpop e = w' @ [x']")
   apply(rename_tac G e f h w x xa wa c a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e f h w x xa wa c a list)(*strict*)
  apply(thin_tac "rule_rpop e=a#list")
  apply(thin_tac "parser_bottom G \<in> set (case rule_rpop e of [] \<Rightarrow> [] | x # y \<Rightarrow> if last (rule_rpop e) = parser_bottom G then butlast (rule_rpop e) else rule_rpop e)")
  apply(rename_tac G e f h w x xa wa c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e f h w x xa wa c w' x')(*strict*)
  apply(subgoal_tac "parser_bottom G \<in> set ((if x' = parser_bottom G then butlast (rule_rpop e) else rule_rpop e))")
   apply(rename_tac G e f h w x xa wa c w' x')(*strict*)
   prefer 2
   apply(rule_tac
      A="set (drop (length f) (if x' = parser_bottom G then butlast (rule_rpop e) else rule_rpop e))"
      in set_mp)
    apply(rename_tac G e f h w x xa wa c w' x')(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac G e f h w x xa wa c w' x')(*strict*)
   apply(force)
  apply(rename_tac G e f h w x xa wa c w' x')(*strict*)
  apply(thin_tac "set (drop (length f) (case w' @ [x'] of [] \<Rightarrow> [] | x # y \<Rightarrow> if last (rule_rpop e) = parser_bottom G then butlast (rule_rpop e) else rule_rpop e)) \<subseteq> parser_events G")
  apply(rename_tac G e f h w x xa wa c w' x')(*strict*)
  apply(thin_tac "parser_bottom G \<in> set (drop (length f) (case w' @ [x'] of [] \<Rightarrow> [] | x # y \<Rightarrow> if last (rule_rpop e) = parser_bottom G then butlast (rule_rpop e) else rule_rpop e))")
  apply(rename_tac G e f h w x xa wa c w' x')(*strict*)
  apply(thin_tac "parser_bottom G \<in> set (drop (length f) (if x' = parser_bottom G then butlast (rule_rpop e) else rule_rpop e))")
  apply(rename_tac G e f h w x xa wa c w' x')(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G e f h w x xa wa c w' x' k wb xc)(*strict*)
  apply(case_tac "x'=parser_bottom G")
   apply(rename_tac G e f h w x xa wa c w' x' k wb xc)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e f h w x xa wa c w' k wb xc xb)(*strict*)
   apply(rule butlast_only_tail_contra)
    apply(rename_tac G e f h w x xa wa c w' k wb xc xb)(*strict*)
    apply(force)
   apply(rename_tac G e f h w x xa wa c w' k wb xc xb)(*strict*)
   apply(force)
  apply(rename_tac G e f h w x xa wa c w' x' k wb xc)(*strict*)
  apply(clarsimp)
  apply(case_tac e)
  apply(rename_tac G e f h w x xa wa c w' x' k wb xc rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f h w x xa wa c w' x' k wb xc rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length wb")
   apply(rename_tac G f h w x xa wa c w' x' k wb xc rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<notin> set (take k wb)")
    apply(rename_tac G f h w x xa wa c w' x' k wb xc rule_lpop rule_lpush rule_rpush)(*strict*)
    apply(force)
   apply(rename_tac G f h w x xa wa c w' x' k wb xc rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(rule_tac
      B="set wb"
      in nset_mp)
    apply(rename_tac G f h w x xa wa c w' x' k wb xc rule_lpop rule_lpush rule_rpush)(*strict*)
    apply(rule set_take_subset)
   apply(rename_tac G f h w x xa wa c w' x' k wb xc rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(force)
  apply(rename_tac G f h w x xa wa c w' x' k wb xc rule_lpop rule_lpush rule_rpush nat)(*strict*)
  apply(clarsimp)
  done

interpretation "parserHFS" : loc_autHFS_0
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs)
  done

lemma parserHFS_inst_AX_effect_inclusion1: "
  (\<forall>M f. parserHFS_marking_condition M f \<longrightarrow> parserHFS_marked_effect M f \<subseteq> parserHFS_unmarked_effect M f)"
  apply(clarsimp)
  apply(rename_tac M f x)(*strict*)
  apply(simp add: parserHFS_unmarked_effect_def parserHFS_marked_effect_def)
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

lemma parserHFS_ins_lang_sound: "
  (\<forall>M. valid_parser M \<longrightarrow> parserHFS.unmarked_language M \<subseteq> parser_markers M)"
  apply(clarsimp)
  apply(rename_tac M x)(*strict*)
  apply(simp add: parserHFS.unmarked_language_def parserHFS_unmarked_effect_def parser_markers_def)
  apply(clarsimp)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(subgoal_tac "c \<in> parserHFS_configurations M")
   apply(rename_tac M xa d i e c)(*strict*)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac M xa d i e f h l w)(*strict*)
   apply(force)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(rule parserHFS.belongs_configurations)
   apply(rename_tac M xa d i e c)(*strict*)
   apply(rule parserHFS.derivation_initial_belongs)
    apply(rename_tac M xa d i e c)(*strict*)
    apply(force)
   apply(rename_tac M xa d i e c)(*strict*)
   apply(force)
  apply(rename_tac M xa d i e c)(*strict*)
  apply(force)
  done

lemma parserHFS_inst_AX_marking_condition_implies_existence_of_effect: "
  (\<forall>M. valid_parser M \<longrightarrow> (\<forall>f. parserHFS.derivation_initial M f \<longrightarrow> parserHFS_marking_condition M f \<longrightarrow> parserHFS_marked_effect M f \<noteq> {}))"
  apply(simp add: parserHFS_marking_condition_def parserHFS_marked_effect_def)
  done

lemma parserHFS_inst_AX_unmarked_effect_persists: "
  (\<forall>G. valid_parser G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial parserHFS_initial_configurations
               parserHFS_step_relation G d \<longrightarrow>
              (\<forall>n. parserHFS_unmarked_effect G (derivation_take d n)
                   \<subseteq> parserHFS_unmarked_effect G d)))"
  apply(clarsimp)
  apply(rename_tac G d n xa)(*strict*)
  apply(simp add: parserHFS_unmarked_effect_def derivation_take_def)
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

lemma parserHFS_inst_ATS_axioms: "
  ATS_Language_axioms valid_parser parserHFS_initial_configurations
     parserHFS_step_relation parser_markers parserHFS_marking_condition
     parserHFS_marked_effect parserHFS_unmarked_effect "
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: parserHFS_inst_AX_effect_inclusion1 parserHFS_ins_lang_sound parserHFS_inst_AX_marking_condition_implies_existence_of_effect parserHFS_inst_AX_unmarked_effect_persists )
  done

interpretation "parserHFS" : loc_autHFS_1
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs)
  apply(simp add: parserHFS_inst_ATS_axioms )
  done

definition parserHFS_set_history :: "
  ('stack, 'event) parserHFS_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserHFS_conf"
  where
    "parserHFS_set_history c h \<equiv>
  c \<lparr>parserHFS_conf_history := h\<rparr>"

lemma parserHFS_inst_AX_initial_history_empty: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_initial_configurations G \<longrightarrow> parserHFS_conf_history c = []))"
  apply(simp add: parserHFS_initial_configurations_def)
  done

lemma parserHFS_inst_AX_steps_extend_history: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> (\<forall>e c'. parserHFS_step_relation G c e c' \<longrightarrow> (\<exists>hf\<in> parser_markers G. parserHFS_conf_history c' = parserHFS_conf_history c @ hf))))"
  apply(clarsimp)
  apply(rename_tac G c e c')(*strict*)
  apply(subgoal_tac "SSe \<in> parser_step_labels SSG \<and> SSc2 \<in> parserHFS_configurations SSG" for SSe SSc2 SSG)
   apply(rename_tac G c e c')(*strict*)
   prefer 2
   apply(rule parserHFS.AX_step_relation_preserves_belongs)
     apply(rename_tac G c e c')(*strict*)
     apply(force)
    apply(rename_tac G c e c')(*strict*)
    apply(force)
   apply(rename_tac G c e c')(*strict*)
   apply(force)
  apply(rename_tac G c e c')(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_step_relation_def parser_markers_def parser_step_labels_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x xa y xb)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c e c' x xa y xb)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac G c e c' x xa y xb)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
  apply(rule_tac
      A="set (drop (length (parserHFS_conf_fixed c)) (butlast_if_match (kPrefix k (w @ [parser_bottom G])) (parser_bottom G)))"
      in set_mp)
   apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
   apply(rule_tac
      B="set (butlast_if_match (kPrefix k (w @ [parser_bottom G])) (parser_bottom G))"
      in subset_trans)
    apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
   apply(rule_tac
      B="set (kPrefix k (w @ [parser_bottom G]))"
      in subset_trans)
    apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
    apply(rule set_butlast_if_match_is_subset)
   apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
   apply(rule_tac
      B="set ((w @ [parser_bottom G]))"
      in subset_trans)
    apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
    apply(simp only: kPrefix_def)
    apply(rule set_take_subset)
   apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
    apply(simp add: valid_parser_def)
   apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
   apply(force)
  apply(rename_tac G c e c' x xa y xb k w xd)(*strict*)
  apply(force)
  done

lemma parser_inst_AX_empty_history_is_history: "
  (\<forall>G. valid_parser G \<longrightarrow> [] \<in> parser_markers G)"
  apply(simp add: parser_markers_def)
  done

lemma parserHFS_inst_AX_set_get_history: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_history c (parserHFS_conf_history c) = c))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserHFS_set_history_def)
  done

lemma parserHFS_inst_AX_get_set_history: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> (\<forall>h. h \<in> parser_markers G \<longrightarrow> parserHFS_conf_history (parserHFS_set_history c h) = h)))"
  apply(clarsimp)
  apply(rename_tac G c h)(*strict*)
  apply(simp add: parserHFS_set_history_def)
  done

lemma parserHFS_inst_AX_join_history_fragments_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>hf1. hf1 \<in> parser_markers G \<longrightarrow> (\<forall>hf2. hf2 \<in> parser_markers G \<longrightarrow> hf1 @ hf2 \<in> parser_markers G)))"
  apply(clarsimp)
  apply(rename_tac G hf1 hf2)(*strict*)
  apply(simp add: parser_markers_def)
  done

lemma parserHFS_inst_AX_get_history_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> parserHFS_conf_history c \<in> parser_markers G))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parser_markers_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G x f h l w)(*strict*)
  apply(force)
  done

lemma parserHFS_inst_AX_mutual_prefix: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>hf1. hf1 \<in> parser_markers G \<longrightarrow> (\<forall>hf2. hf2 \<in> parser_markers G \<longrightarrow> (\<forall>hf3. hf3 \<in> parser_markers G \<longrightarrow> (\<forall>hf4. hf4 \<in> parser_markers G \<longrightarrow> hf1 @ hf2 = hf3 @ hf4 \<longrightarrow> (\<exists>hf\<in> parser_markers G. hf1 @ hf = hf3) \<or> (\<exists>hf\<in> parser_markers G. hf3 @ hf = hf1))))))"
  apply(clarsimp)
  apply(rename_tac G hf1 hf2 hf3 hf4)(*strict*)
  apply(simp add: parser_markers_def parserHFS_configurations_def)
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

lemma parserHFS_inst_ATS_History_axioms: "
  ATS_History_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parserHFS_step_relation parser_markers
     parser_markers parser_empty_history parser_empty_history_fragment
     parserHFS_set_history (@) (@) parserHFS_conf_history"
  apply(simp add: ATS_History_axioms_def)
  apply(simp add: parserHFS_inst_AX_initial_history_empty parserHFS_inst_AX_steps_extend_history parser_inst_AX_empty_history_is_history parserHFS_inst_AX_set_get_history parserHFS_inst_AX_get_set_history parserHFS_inst_AX_join_history_fragments_closed parserHFS_inst_AX_get_history_closed parserHFS_inst_AX_mutual_prefix )
  done

interpretation "parserHFS" : loc_autHFS_2
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs parserHFS_inst_ATS_axioms )
  apply(simp add: parserHFS_inst_ATS_History_axioms )
  done

lemma parserHFS_configurations_entire_pop_implies_prefix_fixed: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c1 e c2
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> \<exists>X. X@[parser_bottom G]=rule_rpop e
  \<Longrightarrow> prefix (parserHFS_conf_fixed c1) (rule_rpop e)"
  apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac f X h x xa y w)(*strict*)
  apply(case_tac c1)
  apply(rename_tac f X h x xa y w parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(case_tac c2)
  apply(rename_tac f X h x xa y w parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historyaa parserHFS_conf_stackaa parserHFS_conf_scheduleraa)(*strict*)
  apply(case_tac e)
  apply(rename_tac f X h x xa y w parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historyaa parserHFS_conf_stackaa parserHFS_conf_scheduleraa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac f X h x xa y w rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(case_tac xa)
   apply(rename_tac f X h x xa y w rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(force)
  apply(rename_tac f X h x xa y w rule_lpop rule_lpush rule_rpush a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
   apply(rename_tac f X h x xa y w rule_lpop rule_lpush rule_rpush a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac f X h x xa y w rule_lpop rule_lpush rule_rpush a list)(*strict*)
  apply(thin_tac "xa=a#list")
  apply(clarsimp)
  done

lemma parserHFS_hist_EQ_EQ: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ w2
  \<Longrightarrow> e1 \<noteq> e2
  \<Longrightarrow> x \<sqsubseteq> w1
  \<Longrightarrow> set x \<subseteq> parser_events G
  \<Longrightarrow> \<not> x \<sqsubseteq> w2
  \<Longrightarrow> xa \<sqsubseteq> w2
  \<Longrightarrow> set xa \<subseteq> parser_events G
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> rule_rpop e1 \<sqsubseteq> rule_rpop e2 \<or> rule_rpop e2 \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> w1 \<noteq> w2
  \<Longrightarrow> w1 = drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e1) (parser_bottom G))
  \<Longrightarrow> w2 = drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e2) (parser_bottom G))
  \<Longrightarrow> butlast_if_match (rule_rpop e2) (parser_bottom G) \<sqsubseteq> rule_rpop e2
  \<Longrightarrow> butlast_if_match (rule_rpop e1) (parser_bottom G) \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> butlast_if_match (rule_rpop e1) (parser_bottom G) = (rule_rpop e1)
  \<Longrightarrow> butlast_if_match (rule_rpop e2) (parser_bottom G) = (rule_rpop e2)
  \<Longrightarrow> xa \<sqsubseteq> w1"
  apply(clarsimp)
  apply(erule disjE)
   apply(subgoal_tac "prefix (drop (length (parserHFS_conf_fixed c)) (rule_rpop e1)) (drop (length (parserHFS_conf_fixed c)) (rule_rpop e2))")
    apply(subgoal_tac "prefix x (drop (length (parserHFS_conf_fixed c)) (rule_rpop e2))")
     apply(force)
    apply(rule prefix_transitive)
     apply(force)
    apply(force)
   apply(rule drop_preserves_prefix)
   apply(force)
  apply(subgoal_tac "prefix (drop (length (parserHFS_conf_fixed c)) (rule_rpop e2)) (drop (length (parserHFS_conf_fixed c)) (rule_rpop e1))")
   apply(rule prefix_transitive)
    apply(force)
   apply(force)
  apply(rule drop_preserves_prefix)
  apply(force)
  done

lemma parserHFS_hist_EQ_NEQ: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ w2
  \<Longrightarrow> e1 \<noteq> e2
  \<Longrightarrow> x \<sqsubseteq> w1
  \<Longrightarrow> set x \<subseteq> parser_events G
  \<Longrightarrow> \<not> x \<sqsubseteq> w2
  \<Longrightarrow> xa \<sqsubseteq> w2
  \<Longrightarrow> set xa \<subseteq> parser_events G
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> rule_rpop e1 \<sqsubseteq> rule_rpop e2 \<or> rule_rpop e2 \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> w1 \<noteq> w2
  \<Longrightarrow> w1 = drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e1) (parser_bottom G))
  \<Longrightarrow> w2 = drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e2) (parser_bottom G))
  \<Longrightarrow> butlast_if_match (rule_rpop e2) (parser_bottom G) \<sqsubseteq> rule_rpop e2
  \<Longrightarrow> butlast_if_match (rule_rpop e1) (parser_bottom G) \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> butlast_if_match (rule_rpop e1) (parser_bottom G) = (rule_rpop e1)
  \<Longrightarrow> butlast_if_match (rule_rpop e2) (parser_bottom G) \<noteq> (rule_rpop e2)
  \<Longrightarrow> xa \<sqsubseteq> w1"
  apply(clarsimp)
  apply(erule disjE)
   apply(subgoal_tac "prefix (drop (length (parserHFS_conf_fixed c)) (rule_rpop e1)) (drop (length (parserHFS_conf_fixed c)) (rule_rpop e2))")
    prefer 2
    apply(rule drop_preserves_prefix)
    apply(force)
   apply(subgoal_tac "\<exists>X. X@[parser_bottom G]=rule_rpop e2")
    prefer 2
    apply(rule butlast_if_match_reduces)
    apply(force)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "prefix (parserHFS_conf_fixed c) (rule_rpop e2)")
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(rule parserHFS_configurations_entire_pop_implies_prefix_fixed)
       apply(rename_tac X)(*strict*)
       apply(force)
      apply(rename_tac X)(*strict*)
      apply(force)
     apply(rename_tac X)(*strict*)
     apply(force)
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "rule_rpop e1 \<noteq> rule_rpop e2")
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "\<exists>w. parserHFS_conf_fixed c @ w = rule_rpop e2")
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(rename_tac X w)(*strict*)
   apply(thin_tac "parserHFS_conf_fixed c \<sqsubseteq> rule_rpop e2")
   apply(subgoal_tac "drop (length (parserHFS_conf_fixed c)) (rule_rpop e2) = w")
    apply(rename_tac X w)(*strict*)
    prefer 2
    apply(rule_tac
      t="rule_rpop e2"
      and s="parserHFS_conf_fixed c @ w"
      in ssubst)
     apply(rename_tac X w)(*strict*)
     apply(force)
    apply(rename_tac X w)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac X w)(*strict*)
   apply(case_tac w)
    apply(rename_tac X w)(*strict*)
    apply(clarsimp)
    apply(rename_tac X)(*strict*)
    apply(subgoal_tac "xa=[]")
     apply(rename_tac X)(*strict*)
     apply(simp add: prefix_def)
    apply(rename_tac X)(*strict*)
    apply(subgoal_tac "drop (length (rule_rpop e2)) (butlast_if_match (rule_rpop e2) (parser_bottom G))=[]")
     apply(rename_tac X)(*strict*)
     apply(simp add: prefix_def)
    apply(rename_tac X)(*strict*)
    apply(clarsimp)
    apply(rule butlast_if_match_length_le)
   apply(rename_tac X w a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
    apply(rename_tac X w a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac X w a list)(*strict*)
   apply(thin_tac "w=a#list")
   apply(clarsimp)
   apply(rename_tac X w' x')(*strict*)
   apply(subgoal_tac "x'=parser_bottom G")
    apply(rename_tac X w' x')(*strict*)
    prefer 2
    apply(rule_tac
      t="x'"
      and s="last (rule_rpop e2)"
      in ssubst)
     apply(rename_tac X w' x')(*strict*)
     apply(rule_tac
      t="rule_rpop e2"
      and s="parserHFS_conf_fixed c @ w' @ [x']"
      in ssubst)
      apply(rename_tac X w' x')(*strict*)
      apply(force)
     apply(rename_tac X w' x')(*strict*)
     apply(simp (no_asm))
    apply(rename_tac X w' x')(*strict*)
    apply(rule_tac
      t="parser_bottom G"
      and s="last (rule_rpop e2)"
      in ssubst)
     apply(rename_tac X w' x')(*strict*)
     apply(rule_tac
      t="rule_rpop e2"
      and s="X @ [parser_bottom G]"
      in ssubst)
      apply(rename_tac X w' x')(*strict*)
      apply(force)
     apply(rename_tac X w' x')(*strict*)
     apply(simp (no_asm))
    apply(rename_tac X w' x')(*strict*)
    apply(force)
   apply(rename_tac X w' x')(*strict*)
   apply(clarsimp)
   apply(rename_tac X w')(*strict*)
   apply(subgoal_tac "parserHFS_conf_fixed c @ w'=X")
    apply(rename_tac X w')(*strict*)
    prefer 2
    apply(rule_tac
      v="[parser_bottom G]"
      in append_injr)
    apply(rule_tac
      t="X @ [parser_bottom G]"
      and s="rule_rpop e2"
      in ssubst)
     apply(rename_tac X w')(*strict*)
     apply(force)
    apply(rename_tac X w')(*strict*)
    apply(force)
   apply(rename_tac X w')(*strict*)
   apply(clarsimp)
   apply(rename_tac w')(*strict*)
   apply(rule prefix_transitive)
    apply(rename_tac w')(*strict*)
    apply(force)
   apply(rename_tac w')(*strict*)
   apply(rule_tac
      t="butlast_if_match (rule_rpop e2) (parser_bottom G)"
      and s="parserHFS_conf_fixed c @ w'"
      in ssubst)
    apply(rename_tac w')(*strict*)
    apply(rule butlast_if_match_direct)
    apply(force)
   apply(rename_tac w')(*strict*)
   apply(rule_tac
      t="drop (length (parserHFS_conf_fixed c)) (parserHFS_conf_fixed c @ w')"
      and s="w'"
      in ssubst)
    apply(rename_tac w')(*strict*)
    apply(force)
   apply(rename_tac w')(*strict*)
   apply(thin_tac "xa \<sqsubseteq> drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e2) (parser_bottom G))")
   apply(rename_tac w')(*strict*)
   apply(thin_tac "set xa \<subseteq> parser_events G")
   apply(subgoal_tac "\<not> prefix x w'")
    apply(rename_tac w')(*strict*)
    prefer 2
    apply(rule_tac
      t="w'"
      and s="drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e2) (parser_bottom G))"
      in ssubst)
     apply(rename_tac w')(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w')(*strict*)
    apply(rule_tac
      t="butlast_if_match (rule_rpop e2) (parser_bottom G)"
      and s="parserHFS_conf_fixed c @ w'"
      in ssubst)
     apply(rename_tac w')(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac w')(*strict*)
    apply(force)
   apply(rename_tac w')(*strict*)
   apply(case_tac "drop (length (parserHFS_conf_fixed c)) (rule_rpop e1) = (w' @ [parser_bottom G])")
    apply(rename_tac w')(*strict*)
    apply(clarsimp)
    apply(simp add: prefix_def)
   apply(rename_tac w')(*strict*)
   apply(subgoal_tac "prefix x w'")
    apply(rename_tac w')(*strict*)
    apply(force)
   apply(rename_tac w')(*strict*)
   apply(rule prefix_transitive)
    apply(rename_tac w')(*strict*)
    apply(force)
   apply(rename_tac w')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac w' ca caa cb cc)(*strict*)
   apply(case_tac "cc")
    apply(rename_tac w' ca caa cb cc)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' ca caa cb cc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cc = w' @ [x']")
    apply(rename_tac w' ca caa cb cc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac w' ca caa cb cc a list)(*strict*)
   apply(thin_tac "cc=a#list")
   apply(clarsimp)
  apply(subgoal_tac "prefix (drop (length (parserHFS_conf_fixed c)) (rule_rpop e2)) (drop (length (parserHFS_conf_fixed c)) (rule_rpop e1))")
   prefer 2
   apply(rule drop_preserves_prefix)
   apply(force)
  apply(subgoal_tac "\<exists>X. X@[parser_bottom G]=rule_rpop e2")
   prefer 2
   apply(rule butlast_if_match_reduces)
   apply(force)
  apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(subgoal_tac "prefix (parserHFS_conf_fixed c) (rule_rpop e2)")
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(rule parserHFS_configurations_entire_pop_implies_prefix_fixed)
      apply(rename_tac X)(*strict*)
      apply(force)
     apply(rename_tac X)(*strict*)
     apply(force)
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(subgoal_tac "rule_rpop e2 \<noteq> rule_rpop e1")
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(rule prefix_transitive)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(rule drop_preserves_prefix)
  apply(rule_tac
      y="rule_rpop e2"
      in prefix_transitive)
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(force)
  done

lemma parserHFS_hist_NEQ_EQ: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ w2
  \<Longrightarrow> e1 \<noteq> e2
  \<Longrightarrow> x \<sqsubseteq> w1
  \<Longrightarrow> set x \<subseteq> parser_events G
  \<Longrightarrow> \<not> x \<sqsubseteq> w2
  \<Longrightarrow> xa \<sqsubseteq> w2
  \<Longrightarrow> set xa \<subseteq> parser_events G
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> rule_rpop e1 \<sqsubseteq> rule_rpop e2 \<or> rule_rpop e2 \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> w1 \<noteq> w2
  \<Longrightarrow> w1 = drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e1) (parser_bottom G))
  \<Longrightarrow> w2 = drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e2) (parser_bottom G))
  \<Longrightarrow> butlast_if_match (rule_rpop e2) (parser_bottom G) \<sqsubseteq> rule_rpop e2
  \<Longrightarrow> butlast_if_match (rule_rpop e1) (parser_bottom G) \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> butlast_if_match (rule_rpop e1) (parser_bottom G) \<noteq> rule_rpop e1
  \<Longrightarrow> butlast_if_match (rule_rpop e2) (parser_bottom G) = rule_rpop e2
  \<Longrightarrow> xa \<sqsubseteq> w1"
  apply(clarsimp)
  apply(erule disjE)
   apply(subgoal_tac "prefix (drop (length (parserHFS_conf_fixed c)) (rule_rpop e1)) (drop (length (parserHFS_conf_fixed c)) (rule_rpop e2))")
    prefer 2
    apply(rule drop_preserves_prefix)
    apply(force)
   apply(subgoal_tac "\<exists>X. X@[parser_bottom G]=rule_rpop e1")
    prefer 2
    apply(rule butlast_if_match_reduces)
    apply(force)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "prefix (parserHFS_conf_fixed c) (rule_rpop e1)")
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(rule parserHFS_configurations_entire_pop_implies_prefix_fixed)
       apply(rename_tac X)(*strict*)
       apply(force)
      apply(rename_tac X)(*strict*)
      apply(force)
     apply(rename_tac X)(*strict*)
     apply(force)
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "rule_rpop e2 \<noteq> rule_rpop e1")
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "x \<sqsubseteq> drop (length (parserHFS_conf_fixed c)) (rule_rpop e2)")
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(rule prefix_transitive)
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(rule drop_preserves_prefix)
   apply(rule_tac
      y="rule_rpop e1"
      in prefix_transitive)
    apply(rename_tac X)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(subgoal_tac "prefix (drop (length (parserHFS_conf_fixed c)) (rule_rpop e2)) (drop (length (parserHFS_conf_fixed c)) (rule_rpop e1))")
   prefer 2
   apply(rule drop_preserves_prefix)
   apply(force)
  apply(subgoal_tac "\<exists>X. X@[parser_bottom G]=rule_rpop e1")
   prefer 2
   apply(rule butlast_if_match_reduces)
   apply(force)
  apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(subgoal_tac "prefix (parserHFS_conf_fixed c) (rule_rpop e1)")
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(rule parserHFS_configurations_entire_pop_implies_prefix_fixed)
      apply(rename_tac X)(*strict*)
      apply(force)
     apply(rename_tac X)(*strict*)
     apply(force)
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(subgoal_tac "rule_rpop e1 \<noteq> rule_rpop e2")
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHFS_conf_fixed c @ w = rule_rpop e1")
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
  apply(rename_tac X)(*strict*)
  apply(clarsimp)
  apply(rename_tac X w)(*strict*)
  apply(thin_tac "parserHFS_conf_fixed c \<sqsubseteq> rule_rpop e1")
  apply(subgoal_tac "drop (length (parserHFS_conf_fixed c)) (rule_rpop e1) = w")
   apply(rename_tac X w)(*strict*)
   prefer 2
   apply(rule_tac
      t="rule_rpop e1"
      and s="parserHFS_conf_fixed c @ w"
      in ssubst)
    apply(rename_tac X w)(*strict*)
    apply(force)
   apply(rename_tac X w)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac X w)(*strict*)
  apply(case_tac w)
   apply(rename_tac X w)(*strict*)
   apply(clarsimp)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "xa=[]")
    apply(rename_tac X)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac X)(*strict*)
   apply(subgoal_tac "drop (length (rule_rpop e1)) (butlast_if_match (rule_rpop e1) (parser_bottom G))=[]")
    apply(rename_tac X)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac X)(*strict*)
   apply(clarsimp)
   apply(rule butlast_if_match_length_le)
  apply(rename_tac X w a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac X w a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac X w a list)(*strict*)
  apply(thin_tac "w=a#list")
  apply(clarsimp)
  apply(rename_tac X w' x')(*strict*)
  apply(subgoal_tac "x'=parser_bottom G")
   apply(rename_tac X w' x')(*strict*)
   prefer 2
   apply(rule_tac
      t="x'"
      and s="last (rule_rpop e1)"
      in ssubst)
    apply(rename_tac X w' x')(*strict*)
    apply(rule_tac
      t="rule_rpop e1"
      and s="parserHFS_conf_fixed c @ w' @ [x']"
      in ssubst)
     apply(rename_tac X w' x')(*strict*)
     apply(force)
    apply(rename_tac X w' x')(*strict*)
    apply(simp (no_asm))
   apply(rename_tac X w' x')(*strict*)
   apply(rule_tac
      t="parser_bottom G"
      and s="last (rule_rpop e1)"
      in ssubst)
    apply(rename_tac X w' x')(*strict*)
    apply(rule_tac
      t="rule_rpop e1"
      and s="X @ [parser_bottom G]"
      in ssubst)
     apply(rename_tac X w' x')(*strict*)
     apply(force)
    apply(rename_tac X w' x')(*strict*)
    apply(simp (no_asm))
   apply(rename_tac X w' x')(*strict*)
   apply(force)
  apply(rename_tac X w' x')(*strict*)
  apply(clarsimp)
  apply(rename_tac X w')(*strict*)
  apply(subgoal_tac "parserHFS_conf_fixed c @ w'=X")
   apply(rename_tac X w')(*strict*)
   prefer 2
   apply(rule_tac
      v="[parser_bottom G]"
      in append_injr)
   apply(rule_tac
      t="X @ [parser_bottom G]"
      and s="rule_rpop e1"
      in ssubst)
    apply(rename_tac X w')(*strict*)
    apply(force)
   apply(rename_tac X w')(*strict*)
   apply(force)
  apply(rename_tac X w')(*strict*)
  apply(clarsimp)
  apply(rename_tac w')(*strict*)
  apply(rule prefix_transitive)
   apply(rename_tac w')(*strict*)
   apply(force)
  apply(rename_tac w')(*strict*)
  apply(thin_tac "xa \<sqsubseteq> drop (length (parserHFS_conf_fixed c)) (rule_rpop e2)")
  apply(thin_tac "set xa \<subseteq> parser_events G")
  apply(rule drop_preserves_prefix)
  apply(rule_tac
      t="butlast_if_match (rule_rpop e1) (parser_bottom G)"
      and s="parserHFS_conf_fixed c @ w'"
      in ssubst)
   apply(rename_tac w')(*strict*)
   apply(rule butlast_if_match_direct)
   apply(force)
  apply(rename_tac w')(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac w' ca caa cb cc)(*strict*)
  apply(case_tac cb)
   apply(rename_tac w' ca caa cb cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac w' ca caa cb cc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
   apply(rename_tac w' ca caa cb cc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w' ca caa cb cc a list)(*strict*)
  apply(thin_tac "cb=a#list")
  apply(clarsimp)
  apply(rename_tac w' ca caa cc w'a x')(*strict*)
  apply(rule_tac
      x="w'a"
      in exI)
  apply(rule_tac
      v="[x']"
      in append_injr)
  apply(rule_tac
      t="(rule_rpop e2 @ w'a) @ [x']"
      and s="rule_rpop e1"
      in ssubst)
   apply(rename_tac w' ca caa cc w'a x')(*strict*)
   apply(force)
  apply(rename_tac w' ca caa cc w'a x')(*strict*)
  apply(rule_tac
      t="rule_rpop e1"
      and s="parserHFS_conf_fixed c @ w' @ [parser_bottom G]"
      in ssubst)
   apply(rename_tac w' ca caa cc w'a x')(*strict*)
   apply(force)
  apply(rename_tac w' ca caa cc w'a x')(*strict*)
  apply(simp (no_asm))
  apply(rule_tac
      t="x'"
      and s="last (rule_rpop e1)"
      in ssubst)
   apply(rename_tac w' ca caa cc w'a x')(*strict*)
   apply(rule_tac
      t="rule_rpop e1"
      and s="rule_rpop e2 @ w'a @ [x']"
      in ssubst)
    apply(rename_tac w' ca caa cc w'a x')(*strict*)
    apply(force)
   apply(rename_tac w' ca caa cc w'a x')(*strict*)
   apply(simp (no_asm))
  apply(rename_tac w' ca caa cc w'a x')(*strict*)
  apply(rule_tac
      t="parser_bottom G"
      and s="last (rule_rpop e1)"
      in ssubst)
   apply(rename_tac w' ca caa cc w'a x')(*strict*)
   apply(rule_tac
      t="rule_rpop e1"
      and s="parserHFS_conf_fixed c @ w' @ [parser_bottom G]"
      in ssubst)
    apply(rename_tac w' ca caa cc w'a x')(*strict*)
    apply(force)
   apply(rename_tac w' ca caa cc w'a x')(*strict*)
   apply(simp (no_asm))
  apply(rename_tac w' ca caa cc w'a x')(*strict*)
  apply(force)
  done

lemma parserHFS_hist_NEQ_NEQ_prime_prime: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> X @ [parser_bottom G] = rule_rpop e1
  \<Longrightarrow> Xa @ [parser_bottom G] = rule_rpop e2
  \<Longrightarrow> rule_rpop e1 = rule_rpop e2"
  apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def prefix_def)
  apply(clarsimp)
  apply(rename_tac f h x xa xb xc c ca cb y ya w)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce)(*strict*)
  apply(case_tac "drop (length (rule_rpop e2)) f @ cb @ drop (length (rule_rpop e1)) f @ ca = []")
   apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce)(*strict*)
   apply(clarsimp)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce)(*strict*)
  apply(clarsimp)
  apply(case_tac "drop (length (rule_rpop e2)) f @ cb")
   apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce)(*strict*)
   apply(clarsimp)
   apply(rename_tac f x xa xb c ca y ya w cc "cd" ce)(*strict*)
   apply(case_tac "drop (length (rule_rpop e1)) f @ ca")
    apply(rename_tac f x xa xb c ca y ya w cc "cd" ce)(*strict*)
    apply(force)
   apply(rename_tac f x xa xb c ca y ya w cc "cd" ce a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. drop (length (rule_rpop e1)) f @ ca = w' @ [x']")
    apply(rename_tac f x xa xb c ca y ya w cc "cd" ce a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac f x xa xb c ca y ya w cc "cd" ce a list)(*strict*)
   apply(thin_tac "drop (length (rule_rpop e1)) f @ ca=a#list")
   apply(clarsimp)
   apply(rename_tac f x xb c ca ya w cc "cd" ce w')(*strict*)
   apply(case_tac e1)
   apply(rename_tac f x xb c ca ya w cc "cd" ce w' rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(case_tac e2)
   apply(rename_tac f x xb c ca ya w cc "cd" ce w' rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
   apply(clarsimp)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w' x'. drop (length (rule_rpop e2)) f @ cb = w' @ [x']")
   apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list)(*strict*)
  apply(thin_tac "drop (length (rule_rpop e2)) f @ cb=a#list")
  apply(clarsimp)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list w' x')(*strict*)
  apply(case_tac e1)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list w' x' rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(case_tac e2)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list w' x' rule_lpopa rule_rpopa rule_lpusha rule_rpusha rule_lpopaa rule_rpopaa rule_lpushaa rule_rpushaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list w' x' rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha)(*strict*)
  apply(case_tac xc)
   apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list w' x' rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha)(*strict*)
   apply(clarsimp)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list w' x' rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha aa lista)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xc = w' @ [x']")
   apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list w' x' rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha aa lista)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac f x xa xb xc c ca cb y ya w cc "cd" ce a list w' x' rule_lpop rule_lpush rule_rpush rule_lpopa rule_lpusha rule_rpusha aa lista)(*strict*)
  apply(thin_tac "xc=aa#lista")
  apply(clarsimp)
  done

lemma parserHFS_hist_NEQ_NEQ_prime: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ drop (length (parserHFS_conf_fixed c)) X
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ drop (length (parserHFS_conf_fixed c)) Xa
  \<Longrightarrow> e1 \<noteq> e2
  \<Longrightarrow> x \<sqsubseteq> drop (length (parserHFS_conf_fixed c)) X
  \<Longrightarrow> set x \<subseteq> parser_events G
  \<Longrightarrow> \<not> x \<sqsubseteq> drop (length (parserHFS_conf_fixed c)) Xa
  \<Longrightarrow> xa \<sqsubseteq> drop (length (parserHFS_conf_fixed c)) Xa
  \<Longrightarrow> set xa \<subseteq> parser_events G
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> rule_rpop e1 \<sqsubseteq> rule_rpop e2 \<or> rule_rpop e2 \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> drop (length (parserHFS_conf_fixed c)) X \<noteq> drop (length (parserHFS_conf_fixed c)) Xa
  \<Longrightarrow> Xa \<sqsubseteq> rule_rpop e2
  \<Longrightarrow> X \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> X \<noteq> rule_rpop e1
  \<Longrightarrow> Xa \<noteq> rule_rpop e2
  \<Longrightarrow> X @ [parser_bottom G] = rule_rpop e1
  \<Longrightarrow> parserHFS_conf_fixed c \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> rule_rpop e2 \<noteq> rule_rpop e1
  \<Longrightarrow> Xa @ [parser_bottom G] = rule_rpop e2
  \<Longrightarrow> parserHFS_conf_fixed c \<sqsubseteq> rule_rpop e2
  \<Longrightarrow> xa \<sqsubseteq> drop (length (parserHFS_conf_fixed c)) X"
  apply(rule prefix_transitive)
   apply(force)
  apply(subgoal_tac "\<exists>w. parserHFS_conf_fixed c @ w = rule_rpop e1")
   prefer 2
   apply(simp add: prefix_def)
  apply(subgoal_tac "\<exists>w. parserHFS_conf_fixed c @ w = rule_rpop e2")
   prefer 2
   apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac w wa)(*strict*)
  apply(thin_tac "parserHFS_conf_fixed c \<sqsubseteq> rule_rpop e2")
  apply(thin_tac "parserHFS_conf_fixed c \<sqsubseteq> rule_rpop e1")
  apply(subgoal_tac "rule_rpop e1 = rule_rpop e2")
   apply(rename_tac w wa)(*strict*)
   apply(force)
  apply(rename_tac w wa)(*strict*)
  apply(rule parserHFS_hist_NEQ_NEQ_prime_prime)
         apply(rename_tac w wa)(*strict*)
         apply(force)+
  done

lemma parserHFS_hist_NEQ_NEQ: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ w2
  \<Longrightarrow> e1 \<noteq> e2
  \<Longrightarrow> x \<sqsubseteq> w1
  \<Longrightarrow> set x \<subseteq> parser_events G
  \<Longrightarrow> \<not> x \<sqsubseteq> w2
  \<Longrightarrow> xa \<sqsubseteq> w2
  \<Longrightarrow> set xa \<subseteq> parser_events G
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> rule_rpop e1 \<sqsubseteq> rule_rpop e2 \<or> rule_rpop e2 \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> w1 \<noteq> w2
  \<Longrightarrow> w1 = drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e1) (parser_bottom G))
  \<Longrightarrow> w2 = drop (length (parserHFS_conf_fixed c)) (butlast_if_match (rule_rpop e2) (parser_bottom G))
  \<Longrightarrow> butlast_if_match (rule_rpop e2) (parser_bottom G) \<sqsubseteq> rule_rpop e2
  \<Longrightarrow> butlast_if_match (rule_rpop e1) (parser_bottom G) \<sqsubseteq> rule_rpop e1
  \<Longrightarrow> butlast_if_match (rule_rpop e1) (parser_bottom G) \<noteq> rule_rpop e1
  \<Longrightarrow> butlast_if_match (rule_rpop e2) (parser_bottom G) \<noteq> rule_rpop e2
  \<Longrightarrow> xa \<sqsubseteq> w1"
  apply(clarsimp)
  apply(subgoal_tac "\<exists>X. X@[parser_bottom G]=rule_rpop e1")
   prefer 2
   apply(rule butlast_if_match_reduces)
   apply(force)
  apply(clarsimp)
  apply(rename_tac X)(*strict*)
  apply(subgoal_tac "prefix (parserHFS_conf_fixed c) (rule_rpop e1)")
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(rule parserHFS_configurations_entire_pop_implies_prefix_fixed)
      apply(rename_tac X)(*strict*)
      apply(force)
     apply(rename_tac X)(*strict*)
     apply(force)
    apply(rename_tac X)(*strict*)
    apply(force)
   apply(rename_tac X)(*strict*)
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(subgoal_tac "rule_rpop e2 \<noteq> rule_rpop e1")
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(subgoal_tac "\<exists>X. X@[parser_bottom G]=rule_rpop e2")
   apply(rename_tac X)(*strict*)
   prefer 2
   apply(rule butlast_if_match_reduces)
   apply(force)
  apply(rename_tac X)(*strict*)
  apply(clarsimp)
  apply(rename_tac X Xa)(*strict*)
  apply(subgoal_tac "prefix (parserHFS_conf_fixed c) (rule_rpop e2)")
   apply(rename_tac X Xa)(*strict*)
   prefer 2
   apply(rule parserHFS_configurations_entire_pop_implies_prefix_fixed)
      apply(rename_tac X Xa)(*strict*)
      apply(force)
     apply(rename_tac X Xa)(*strict*)
     apply(force)
    apply(rename_tac X Xa)(*strict*)
    apply(force)
   apply(rename_tac X Xa)(*strict*)
   apply(force)
  apply(rename_tac X Xa)(*strict*)
  apply(rule_tac
      ?c1.0="c1"
      and ?c2.0="c2"
      in parserHFS_hist_NEQ_NEQ_prime)
                      apply(rename_tac X Xa)(*strict*)
                      apply(force)+
      apply(rename_tac X Xa)(*strict*)
      apply(rule_tac
      t="butlast_if_match (rule_rpop e1) (parser_bottom G)"
      and s="X"
      in ssubst)
       apply(rename_tac X Xa)(*strict*)
       apply(rule butlast_if_match_direct)
       apply(force)
      apply(rename_tac X Xa)(*strict*)
      apply(force)
     apply(rename_tac X Xa)(*strict*)
     apply(force)
    apply(rename_tac X Xa)(*strict*)
    apply(force)
   apply(rename_tac X Xa)(*strict*)
   apply(rule_tac
      t="butlast_if_match (rule_rpop e2) (parser_bottom G)"
      and s="Xa"
      in ssubst)
    apply(rename_tac X Xa)(*strict*)
    apply(rule butlast_if_match_direct)
    apply(force)
   apply(rename_tac X Xa)(*strict*)
   apply(force)
  apply(rename_tac X Xa)(*strict*)
  apply(force)
  done

lemma parserHFS_inst_AX_string_state_decreases: "
  \<forall>G. valid_parser G \<longrightarrow>
        (\<forall>c1. c1 \<in> parserHFS_configurations G \<longrightarrow>
              (\<forall>e c2. parserHFS_step_relation G c1 e c2 \<longrightarrow>
                      (\<exists>w. parserHFS_string_state c1 =
                           w @ parserHFS_string_state c2)))"
  apply(clarsimp)
  apply(rename_tac M c1 e c2)(*strict*)
  apply(simp add: parserHFS_string_state_def parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac M c1 e c2 x xa y)(*strict*)
  apply(subgoal_tac "valid_parser_step_label M e")
   apply(rename_tac M e c1 c2 x xa y)(*strict*)
   prefer 2
   apply(rename_tac M c1 e c2 x xa y)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac M e c1 c2 x xa y)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac M e c1 c2 x xa y k w xc)(*strict*)
  apply(rule_tac
      x="xc"
      in exI)
  apply(force)
  done

lemma parserHFS_inst_AX_marking_can_not_be_disabled: "
  (\<forall>G d. (\<exists>n. parserHFS_marking_condition G (derivation_take d n)) \<longrightarrow> parserHFS_marking_condition G d)"
  apply(clarsimp)
  apply(rename_tac G d n)(*strict*)
  apply(simp add: parserHFS_marking_condition_def derivation_take_def)
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
   apply(force)+
  done

lemma parserHFS_inst_AX_marked_effect_persists: "
  (\<forall>G d n. parserHFS_marked_effect G (derivation_take d n) \<subseteq> parserHFS_marked_effect G d)"
  apply(clarsimp)
  apply(rename_tac G d n x)(*strict*)
  apply(simp add: parserHFS_marked_effect_def derivation_take_def)
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
   apply(force)+
  done

lemma parserHFS_inst_lang_finite: "
  (\<forall>G. valid_parser G \<longrightarrow> parserHFS.finite_marked_language G = parserHFS.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserHFS.finite_marked_language_def parserHFS.marked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: parserHFS.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: parserHFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(rule parserHFS.derivation_take_preserves_derivation_initial)
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
   apply(simp add: parserHFS_marking_condition_def)
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

lemma parserHFS_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_parser G \<longrightarrow> parserHFS.finite_unmarked_language G = parserHFS.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserHFS.finite_unmarked_language_def parserHFS.unmarked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: parserHFS.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d i e c)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d i e c)(*strict*)
   apply(rule parserHFS.derivation_take_preserves_derivation_initial)
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

lemma parserHFS_inst_accept: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> parserHFS_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> parserHFS_marking_configurations G))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: parserHFS_marking_condition_def)
  done

lemma parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms: "
      ATS_Language_by_Finite_Derivations_axioms valid_parser
     parserHFS_initial_configurations parserHFS_step_relation
     parserHFS_marking_condition parserHFS_marked_effect
     parserHFS_unmarked_effect "
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(simp add: parserHFS_inst_lang_finite parserHFS_inst_AX_unmarked_language_finite )
  done

lemma parserHFS_inst_ATS_String_State_Modification_axioms: "
  ATS_String_State_Modification_axioms valid_parser parserHFS_configurations
     parserHFS_step_relation True parserHFS_string_state"
  apply(simp add: ATS_String_State_Modification_axioms_def)
  apply(simp add: parserHFS_inst_AX_string_state_decreases )
  done

interpretation "parserHFS" : loc_autHFS_3
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHFS_inst_ATS_axioms parserHFS_inst_ATS_History_axioms parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms parserHFS_inst_ATS_String_State_Modification_axioms )
  done

lemma parserHFS_inst_AX_fixed_scheduler_extendable_translates_backwards: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_configurations G \<longrightarrow> (\<forall>e c2. parserHFS_step_relation G c1 e c2 \<longrightarrow> \<not> parserHFS_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> parserHFS_conf_fixed c1 \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state c1 = w @ parserHFS_string_state c2")
   apply(rename_tac G c1 e c2)(*strict*)
   prefer 2
   apply(rule parserHFS.AX_string_state_decreases)
      apply(rename_tac G c1 e c2)(*strict*)
      apply(force)
     apply(rename_tac G c1 e c2)(*strict*)
     apply(force)
    apply(rename_tac G c1 e c2)(*strict*)
    apply(simp add: parser_step_labels_def parserHFS_step_relation_def)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(force)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c1 e c2 w)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c1 e c2 w)(*strict*)
   prefer 2
   apply(simp add: parserHFS_step_relation_def valid_parser_def)
  apply(rename_tac G c1 e c2 w)(*strict*)
  apply(subgoal_tac "c2 \<in> parserHFS_configurations G")
   apply(rename_tac G c1 e c2 w)(*strict*)
   prefer 2
   apply(rule parserHFS.AX_step_relation_preserves_belongsC)
     apply(rename_tac G c1 e c2 w)(*strict*)
     apply(force)
    apply(rename_tac G c1 e c2 w)(*strict*)
    apply(force)
   apply(rename_tac G c1 e c2 w)(*strict*)
   apply(force)
  apply(rename_tac G c1 e c2 w)(*strict*)
  apply(simp add: valid_parser_step_label_def suffix_def parserHFS_configurations_def parserHFS_string_state_def parserHFS_step_relation_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G e w c k wa xa xb ca cb cc "cd" y xc)(*strict*)
  apply(case_tac "(length (kPrefix k (wa @ [parser_bottom G])) - length c)")
   apply(rename_tac G e w c k wa xa xb ca cb cc "cd" y xc)(*strict*)
   apply(force)
  apply(rename_tac G e w c k wa xa xb ca cb cc "cd" y xc nat)(*strict*)
  apply(clarsimp)
  apply(case_tac xb)
   apply(rename_tac G e w c k wa xa xb ca cb cc "cd" y xc nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac G e w c k wa xa xb ca cb cc "cd" y xc nat a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
   apply(rename_tac G e w c k wa xa xb ca cb cc "cd" y xc nat a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e w c k wa xa xb ca cb cc "cd" y xc nat a list)(*strict*)
  apply(thin_tac "xb = a # list")
  apply(clarsimp)
  apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w')(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac "k-length wa")
   apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w')(*strict*)
   prefer 2
   apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w' nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w' nata x)(*strict*)
   apply(erule_tac
      x="x"
      in allE)
   apply(force)
  apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "min (length wa) k = k")
   apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w')(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w')(*strict*)
  apply(clarsimp)
  apply(thin_tac "min (length wa) k = k")
  apply(case_tac ca)
   apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w')(*strict*)
   apply(clarsimp)
  apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e w c k wa xa ca cc "cd" xc nat w' a list)(*strict*)
  apply(thin_tac "ca = a # list")
  apply(clarsimp)
  apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
  apply(subgoal_tac "parser_bottom G \<in> set (wa@w')")
   apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
   prefer 2
   apply(rule_tac
      A="set(take k wa@w')"
      in set_mp)
    apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a x)(*strict*)
    apply(rule_tac
      A="set(take k wa)"
      in set_mp)
     apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a x)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a x)(*strict*)
    apply(force)
   apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
   apply(rule_tac
      t="take k wa@w'"
      and s="c @ parser_bottom G # w'a"
      in ssubst)
    apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
    apply(force)
   apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
  apply(subgoal_tac "parser_bottom G \<notin> set (wa@w')")
   apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom G \<notin> set wa")
    apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
    apply(force)
   apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
   apply(rule_tac
      A="parser_events G"
      in not_in_diff)
   apply(force)
  apply(rename_tac G e w c k wa xa cc "cd" xc nat w' w'a)(*strict*)
  apply(force)
  done

definition parserHFS_set_unfixed_scheduler :: "
  ('stack, 'event) parserHFS_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserHFS_conf"
  where
    "parserHFS_set_unfixed_scheduler c sUF \<equiv>
  c \<lparr>parserHFS_conf_scheduler := parserHFS_conf_fixed c @ sUF\<rparr>"

definition parserHFS_get_unfixed_scheduler :: "
  ('stack, 'event) parserHFS_conf
  \<Rightarrow> 'event list"
  where
    "parserHFS_get_unfixed_scheduler c \<equiv>
  the (left_quotient_word (parserHFS_conf_fixed c) (parserHFS_conf_scheduler c))"

lemma parserHFS_inst_AX_set_unfixed_scheduler_set: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> (\<forall>sUF1. sUF1 \<in> parser_unfixed_schedulers G \<longrightarrow> (\<forall>sUF2. sUF2 \<in> parser_unfixed_schedulers G \<longrightarrow> parserHFS_set_unfixed_scheduler (parserHFS_set_unfixed_scheduler c sUF1) sUF2 = parserHFS_set_unfixed_scheduler c sUF2))))"
  apply(simp add: parserHFS_set_unfixed_scheduler_def)
  done

lemma parserHFS_inst_AX_get_set_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> parserHFS_get_unfixed_scheduler (parserHFS_set_unfixed_scheduler c sUF) = sUF)))"
  apply(simp add: parserHFS_get_unfixed_scheduler_def parserHFS_set_unfixed_scheduler_def)
  apply(simp add: left_quotient_word_def)
  done

lemma parserHFS_inst_schedUF_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> parserHFS_get_unfixed_scheduler c \<in> parser_unfixed_schedulers G))"
  apply(simp add: parserHFS_get_unfixed_scheduler_def parser_unfixed_schedulers_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G f h l w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G f h l w c)(*strict*)
  apply(rule_tac
      t="left_quotient_word f (w@[parser_bottom G])"
      and s="Some c"
      in ssubst)
   apply(rename_tac G f h l w c)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G f h l w c)(*strict*)
  apply(clarsimp)
  apply(simp add: suffix_closure_def parser_schedulers_def suffix_def)
  apply(case_tac c)
   apply(rename_tac G f h l w c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G l w ca)(*strict*)
   apply(rule_tac
      x="[]"
      in exI)
   apply(force)
  apply(rename_tac G f h l w c a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c = w' @ [x']")
   apply(rename_tac G f h l w c a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G f h l w c a list)(*strict*)
  apply(thin_tac "c = a # list")
  apply(clarsimp)
  apply(rename_tac G f l ca w')(*strict*)
  apply(rule_tac
      x="w'@[parser_bottom G]"
      in exI)
  apply(force)
  done

lemma parserHFS_inst_AX_set_unfixed_scheduler_get: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_configurations G \<longrightarrow> (\<forall>c2. c2 \<in> parserHFS_configurations G \<longrightarrow> (\<exists>sUF\<in> parser_unfixed_schedulers G. parserHFS_set_unfixed_scheduler c1 sUF = parserHFS_set_unfixed_scheduler c2 sUF) \<longrightarrow> parserHFS_set_unfixed_scheduler c1 (parserHFS_get_unfixed_scheduler c2) = c2)))"
  apply(clarsimp)
  apply(rename_tac G c1 c2 sUF)(*strict*)
  apply(simp add: parserHFS_set_unfixed_scheduler_def parserHFS_get_unfixed_scheduler_def parserHFS_configurations_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G sUF fa ha la c ca w wa)(*strict*)
  apply(rule_tac
      t="left_quotient_word fa (wa@[parser_bottom G])"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G sUF fa ha la c ca w wa)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(clarsimp)
  apply(rename_tac G sUF fa ha la c ca w wa)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_unfixed_is_reduced_by_single_step: "
  valid_parser G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> valid_parser_step_label G e
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> parserHFS_step_relation G c1 e c2
  \<Longrightarrow> parserHFS_get_unfixed_scheduler c1 \<sqsupseteq> parserHFS_get_unfixed_scheduler c2"
  apply(simp add: parserHFS_step_relation_def)
  apply(simp add: parserHFS_get_unfixed_scheduler_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac f h x xa y w)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac f h x xa y w c ca)(*strict*)
  apply(rule_tac
      t="left_quotient_word f (rule_rpop e @ xa)"
      and s="Some c"
      in ssubst)
   apply(rename_tac f h x xa y w c ca)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac f h x xa y w c ca)(*strict*)
  apply(rule_tac
      t="left_quotient_word (rule_rpush e @ drop (length (rule_rpop e)) f) (y @ [parser_bottom G])"
      and s="Some ca"
      in ssubst)
   apply(rename_tac f h x xa y w c ca)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac f h x xa y w c ca)(*strict*)
  apply(clarsimp)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac f x xa y w c ca cb cc)(*strict*)
  apply(case_tac xa)
   apply(rename_tac f x xa y w c ca cb cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac f x xa y w c ca cb cc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
   apply(rename_tac f x xa y w c ca cb cc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac f x xa y w c ca cb cc a list)(*strict*)
  apply(thin_tac "xa=a#list")
  apply(clarsimp)
  apply(rename_tac f x c ca cb cc w')(*strict*)
  apply(subgoal_tac "prefix f (rule_rpop e) \<or> prefix (rule_rpop e) f")
   apply(rename_tac f x c ca cb cc w')(*strict*)
   apply(erule disjE)
    apply(rename_tac f x c ca cb cc w')(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac x c ca cb cc w' "cd")(*strict*)
    apply(subgoal_tac "c=ca")
     apply(rename_tac x c ca cb cc w' "cd")(*strict*)
     apply(force)
    apply(rename_tac x c ca cb cc w' "cd")(*strict*)
    apply (metis dropPrecise)
   apply(rename_tac f x c ca cb cc w')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac f x c ca cb cc w' "cd")(*strict*)
   apply(subgoal_tac "drop (length (rule_rpop e)) f = []")
    apply(rename_tac f x c ca cb cc w' "cd")(*strict*)
    prefer 2
    apply(rule_tac
      t="rule_rpop e"
      and s="f@cd"
      in ssubst)
     apply(rename_tac f x c ca cb cc w' "cd")(*strict*)
     apply(force)
    apply(rename_tac f x c ca cb cc w' "cd")(*strict*)
    apply(simp (no_asm))
   apply(rename_tac f x c ca cb cc w' "cd")(*strict*)
   apply(clarsimp)
   apply(rename_tac f x c cb cc w' "cd")(*strict*)
   apply(subgoal_tac "butlast_if_match (rule_rpop e) (parser_bottom G) = rule_rpop e")
    apply(rename_tac f x c cb cc w' "cd")(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "drop (length f) (rule_rpop e) = cd")
     apply(rename_tac f x c cb cc w' "cd")(*strict*)
     apply(clarsimp)
     apply(rename_tac f x c cb cc w')(*strict*)
     apply(rule_tac
      x="drop (length f) (rule_rpop e)"
      in exI)
     apply (metis drop_append drop_distrib_append)
    apply(rename_tac f x c cb cc w' "cd")(*strict*)
    apply (metis dropPrecise)
   apply(rename_tac f x c cb cc w' "cd")(*strict*)
   apply (metis butlast_if_match_direct2_prime)
  apply(rename_tac f x c ca cb cc w')(*strict*)
  apply (metis mutual_prefix_prefix)
  done

lemma parserHFS_unfixed_is_reduced_by_steps: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> parserHFS.belongs G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> d m = Some (pair e' c')
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> suffix (parserHFS_get_unfixed_scheduler c) (parserHFS_get_unfixed_scheduler c')"
  apply(induct "m-n" arbitrary: n m e c e' c')
   apply(rename_tac n m e c e' c')(*strict*)
   apply(clarsimp)
   apply(rename_tac n e' c')(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac x n m e c e' c')(*strict*)
  apply(erule_tac
      x="Suc n"
      in meta_allE)
  apply(erule_tac
      x="m"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac x n m e c e' c')(*strict*)
   prefer 2
   apply(rule_tac
      m="m"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac x n m e c e' c')(*strict*)
     apply(force)
    apply(rename_tac x n m e c e' c')(*strict*)
    apply(force)
   apply(rename_tac x n m e c e' c')(*strict*)
   apply(force)
  apply(rename_tac x n m e c e' c')(*strict*)
  apply(clarsimp)
  apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
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
  apply(erule_tac meta_impE)
   apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
  apply(erule_tac meta_impE)
   apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
  apply(subgoal_tac "parserHFS_get_unfixed_scheduler c \<sqsupseteq> parserHFS_get_unfixed_scheduler c2")
   apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
   apply(simp add: suffix_def)
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
  apply(rule parserHFS_unfixed_is_reduced_by_single_step)
      apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
      apply(force)
     apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
     apply (metis parserHFS.belongs_configurations)
    apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
    prefer 2
    apply (metis parserHFS.belongs_configurations)
   apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
  apply(simp add: parserHFS_step_relation_def valid_parser_def)
  done

lemma parserHFS_inst_AX_unfixed_scheduler_right_quotient_split: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation G d \<longrightarrow> parserHFS.belongs G d \<longrightarrow> (\<forall>n e1 c1. d n = Some (pair e1 c1) \<longrightarrow> (\<forall>m e2 c2. d m = Some (pair e2 c2) \<longrightarrow> (\<forall>k e3 c3. d k = Some (pair e3 c3) \<longrightarrow> n \<le> m \<longrightarrow> m \<le> k \<longrightarrow> the (right_quotient_word (parserHFS_get_unfixed_scheduler c1) (parserHFS_get_unfixed_scheduler c3)) = the (right_quotient_word (parserHFS_get_unfixed_scheduler c1) (parserHFS_get_unfixed_scheduler c2)) @ the (right_quotient_word (parserHFS_get_unfixed_scheduler c2) (parserHFS_get_unfixed_scheduler c3))))))"
  apply(clarsimp)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
  apply(subgoal_tac "suffix (parserHFS_get_unfixed_scheduler c1) (parserHFS_get_unfixed_scheduler c2)")
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
   prefer 2
   apply(rule parserHFS_unfixed_is_reduced_by_steps)
        apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
        apply(force)
       apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
       apply(force)
      apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
      apply(force)
     apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
     apply(force)
    apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
    apply(force)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
  apply(subgoal_tac "suffix (parserHFS_get_unfixed_scheduler c2) (parserHFS_get_unfixed_scheduler c3)")
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
   prefer 2
   apply(rule parserHFS_unfixed_is_reduced_by_steps)
        apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
        apply(force)
       apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
       apply(force)
      apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
      apply(force)
     apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
     apply(force)
    apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
    apply(force)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
  apply(rule_tac
      t="right_quotient_word (c @ ca @ parserHFS_get_unfixed_scheduler c3) (parserHFS_get_unfixed_scheduler c3)"
      and s="Some(c@ca)"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
  apply(rule_tac
      t="right_quotient_word (c @ ca @ parserHFS_get_unfixed_scheduler c3) (ca@parserHFS_get_unfixed_scheduler c3)"
      and s="Some c"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
  apply(rule_tac
      t="right_quotient_word (ca @ parserHFS_get_unfixed_scheduler c3) (parserHFS_get_unfixed_scheduler c3)"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
  apply(clarsimp)
  done

definition parserHFS_get_scheduler :: "
  ('stack, 'event) parserHFS_conf
  \<Rightarrow> 'event list"
  where
    "parserHFS_get_scheduler c \<equiv>
  parserHFS_conf_scheduler c"

lemma parserHFS_inst_AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> parserHFS_get_scheduler c = parserHFS_conf_fixed c @ parserHFS_get_unfixed_scheduler c))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserHFS_configurations_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G f h l ca w)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_def)
  apply(rule_tac
      t="left_quotient_word f (w@[parser_bottom G])"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G f h l ca w)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G f h l ca w)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_get_scheduler_def)
  done

lemma parserHFS_inst_AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> parserHFS_get_unfixed_scheduler c \<sqsupseteq> [parser_bottom G] = (\<not> parserHFS_conf_fixed c \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: prefix_def suffix_def parserHFS_configurations_def parserHFS_get_unfixed_scheduler_def)
  apply(clarsimp)
  apply(rename_tac G f l ca cb w)(*strict*)
  apply(rule_tac
      t="left_quotient_word f (w @ [parser_bottom G])"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G f l ca cb w)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G f l ca cb w)(*strict*)
  apply(clarsimp)
  apply(case_tac ca)
   apply(rename_tac G f l ca cb w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f l ca cb w a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac G f l ca cb w a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G f l ca cb w a list)(*strict*)
  apply(thin_tac "ca = a # list")
  apply(clarsimp)
  done

lemma parserHFS_inst_AX_get_scheduler_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> parserHFS_get_scheduler c \<in> parser_schedulers G))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserHFS_get_scheduler_def parserHFS_configurations_def parser_schedulers_def prefix_def)
  apply(clarsimp)
  done

lemma parserHFS_inst_AX_not_extendable_fixed_scheduler_implies_empty_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> parserHFS_conf_fixed c \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHFS_get_unfixed_scheduler c = []))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G f h l w)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_def)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G f h l w c)(*strict*)
  apply (metis left_quotient_word_removes_right_addition_hlp List.butlast_append append_is_Nil_conv butlast_snoc last_in_set last_snoc not_Cons_self set_append_contra1 suffix_def option.sel)
  done

lemma parserHFS_inst_extendable_implies_notempty_unfixed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserHFS_configurations G \<longrightarrow> \<not> parserHFS_conf_fixed c \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHFS_get_unfixed_scheduler c \<noteq> []))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G f h l w)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_def)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac G f h l w c)(*strict*)
  apply (metis left_quotient_word_removes_right_addition_hlp List.butlast_append append_is_Nil_conv butlast_snoc not_Cons_self suffix_def option.sel)
  done

definition parserHFS_get_fixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "parserHFS_get_fixed_scheduler_DB G d n \<equiv>
  take
    (parser_fixed_input_length_recN d n)
    (parserHFS_get_scheduler
      (the (get_configuration (d n))))"

definition parserHFS_set_unfixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserHFS_conf"
  where
    "parserHFS_set_unfixed_scheduler_DB G d n sUF \<equiv>
  (the (get_configuration (d n)))
    \<lparr>parserHFS_conf_scheduler
      := parserHFS_get_fixed_scheduler_DB G d n @ sUF\<rparr>"

definition parserHFS_get_unfixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "parserHFS_get_unfixed_scheduler_DB G d n \<equiv>
  drop
    (parser_fixed_input_length_recN d n)
    (parserHFS_get_scheduler
      (the (get_configuration (d n))))"

lemma parserHFS_parser_fixed_input_length_recN_with_derivation_take: "
  i\<le>n
  \<Longrightarrow> parserHFS.derivation M d
  \<Longrightarrow> parser_fixed_input_length_recN (derivation_take d n) i = parser_fixed_input_length_recN d i"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc i)")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation M c1 e2 c2")
   apply(rename_tac i a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac i a)(*strict*)
     apply(force)
    apply(rename_tac i a)(*strict*)
    apply(force)
   apply(rename_tac i a)(*strict*)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_take_def)
  done

lemma parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> take (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler c) = parserHFS_conf_fixed c"
  apply(induct n arbitrary: d e c)
   apply(rename_tac d e c)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS.derivation_initial_def parserHFS_initial_configurations_def)
  apply(rename_tac n d e c)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="derivation_take d n"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac n d e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac n d e c)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac n d e c)(*strict*)
    apply(force)
   apply(rename_tac n d e c)(*strict*)
   apply(force)
  apply(rename_tac n d e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n d c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac n d c e1 e2 c1)(*strict*)
   apply(rule parserHFS.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac n d c e1 e2 c1)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac n d c e1 e2 c1)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac n d c e1 e2 c1)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n d c e1 e2 c1 x xa y)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac n d c e1 e2 c1 x xa y)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac n d c e1 e2 c1 x xa y k w xc)(*strict*)
   apply(case_tac c)
   apply(rename_tac n d c e1 e2 c1 x xa y k w xc parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
   apply(case_tac c1)
   apply(rename_tac n d c e1 e2 c1 x xa y k w xc parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historyaa parserHFS_conf_stackaa parserHFS_conf_scheduleraa)(*strict*)
   apply(clarsimp)
   apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN (derivation_take d n) n = parser_fixed_input_length_recN d n")
    apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
    apply(clarsimp)
    apply(case_tac "(parser_fixed_input_length_recN d n) - (length (kPrefix k (w @ [parser_bottom G])))")
     apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "max (parser_fixed_input_length_recN d n) (length (kPrefix k (w @ [parser_bottom G]))) = length (kPrefix k (w @ [parser_bottom G]))")
      apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "(length (kPrefix k (w @ [parser_bottom G])) - (length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2))) \<ge> length (rule_rpush e2)")
       apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
       apply(clarsimp)
      apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
      apply (metis diff_diff_cancel drop_length_append drop_prefix_closureise eq_imp_le length_drop)
     apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
     apply(force)
    apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya nat)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "max (parser_fixed_input_length_recN d n) (length (kPrefix k (w @ [parser_bottom G]))) = parser_fixed_input_length_recN d n")
     apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya nat)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(parser_fixed_input_length_recN d n - (length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2))) \<ge> length (rule_rpush e2)")
      apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya nat)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "(parser_fixed_input_length_recN d n - (length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2) + length (rule_rpush e2))) = Suc nat")
       apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya nat)(*strict*)
       apply(clarsimp)
      apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya nat)(*strict*)
      apply (metis diff_commute diff_diff_left le_add2 le_add_diff_inverse2 length_append add.commute nat_minus_add_max)
     apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya nat)(*strict*)
     apply (metis add_leE diff_diff_cancel dropPrecise drop_length_append le_diff_conv2 Lattices.linorder_class.max.cobounded2 length_append length_drop add.commute)
    apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya nat)(*strict*)
    apply(force)
   apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
   apply(rule parserHFS_parser_fixed_input_length_recN_with_derivation_take)
    apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
    apply(force)
   apply(rename_tac n d e1 e2 x xa y k w xc parserHFS_conf_historya)(*strict*)
   apply(simp add: parserHFS.derivation_initial_def)
   apply(force)
  apply(rename_tac n d c e1 e2 c1 x xa y)(*strict*)
  apply(simp add: valid_parser_def)
  done

lemma parserHFS_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> parserHFS_get_fixed_scheduler_DB G d n = parserHFS_conf_fixed c)))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def get_configuration_def parserHFS_get_scheduler_def)
  apply(rule parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler)
    apply(rename_tac G d n e c)(*strict*)
    apply(force)+
  done

lemma parserHFS_inst_AX_equal_up_to_unfixed_scheduler_implies_equal_fixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_configurations G \<longrightarrow> (\<forall>c2. c2 \<in> parserHFS_configurations G \<longrightarrow> parserHFS_set_unfixed_scheduler c1 (parserHFS_get_unfixed_scheduler c2) = c2 \<longrightarrow> parserHFS_conf_fixed c1 = parserHFS_conf_fixed c2)))"
  apply(simp add: parserHFS_set_unfixed_scheduler_def parserHFS_get_unfixed_scheduler_def)
  apply(clarsimp)
  apply(rename_tac G c1 c2)(*strict*)
  apply(case_tac c1)
  apply(rename_tac G c1 c2 parserHFS_conf_fixeda parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_schedulera)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G c1 c2 parserHFS_conf_fixeda parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduleraa)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> parserHFS.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> i \<le> j
  \<Longrightarrow> j \<le> n
  \<Longrightarrow> suffix (parserHFS_get_unfixed_scheduler_DB G d i) (parserHFS_get_unfixed_scheduler_DB G d j)"
  apply(induct "j-i" arbitrary: i j)
   apply(rename_tac i j)(*strict*)
   apply(clarsimp)
   apply(rename_tac i y)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac x i j)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i j y)(*strict*)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(erule_tac
      x="j"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i j y)(*strict*)
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i j y)(*strict*)
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(rule_tac
      b="parserHFS_get_unfixed_scheduler_DB G d (Suc i)"
      in suffix_trans)
   apply(rename_tac x i j y)(*strict*)
   defer
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(thin_tac "parserHFS_get_unfixed_scheduler_DB G d (Suc i) \<sqsupseteq> parserHFS_get_unfixed_scheduler_DB G d j")
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def suffix_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac x i j y)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac x i j y)(*strict*)
     apply(force)
    apply(rename_tac x i j y)(*strict*)
    apply(force)
   apply(rename_tac x i j y)(*strict*)
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i j y e1 e2 c1 c2)(*strict*)
  apply(simp add: parserHFS_get_scheduler_def get_configuration_def parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
  apply(subgoal_tac "length (rule_rpop e2) \<ge> length (rule_rpush e2)")
   apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya k w xd)(*strict*)
    apply(rule_tac
      j="length (xd @ rule_rpush e2)"
      in le_trans)
     apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya k w xd)(*strict*)
     apply (metis le_iff_add length_append add.commute)
    apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya k w xd)(*strict*)
    apply(force)
   apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
  apply(case_tac "(parser_fixed_input_length_recN d i) \<le> length (rule_rpop e2)")
   apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(subgoal_tac "max (parser_fixed_input_length_recN d i) (length (rule_rpop e2)) = parser_fixed_input_length_recN d i")
    apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i j y e1 e2 c1 c2 xa xb ya)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_inst_get_unfixed_scheduler_DB_constructs_right_quotient: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (\<forall>j. parserHFS_get_unfixed_scheduler_DB G d j \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>i\<le>j. j \<le> n \<longrightarrow> the (right_quotient_word (parserHFS_get_unfixed_scheduler_DB G d i) (parserHFS_get_unfixed_scheduler_DB G d j)) \<in> parser_scheduler_fragments G)))))"
  apply(clarsimp)
  apply(rename_tac G d n y j i)(*strict*)
  apply(subgoal_tac "suffix (parserHFS_get_unfixed_scheduler_DB G d i) (parserHFS_get_unfixed_scheduler_DB G d j)")
   apply(rename_tac G d n y j i)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient)
        apply(rename_tac G d n y j i)(*strict*)
        apply(force)
       apply(rename_tac G d n y j i)(*strict*)
       apply(simp add: parserHFS.derivation_initial_def)
      apply(rename_tac G d n y j i)(*strict*)
      apply (metis parserHFS.derivation_initial_belongs)
     apply(rename_tac G d n y j i)(*strict*)
     apply(force)
    apply(rename_tac G d n y j i)(*strict*)
    apply(force)
   apply(rename_tac G d n y j i)(*strict*)
   apply(force)
  apply(rename_tac G d n y j i)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G d n y j i c ca)(*strict*)
  apply(rule_tac
      t="right_quotient_word (ca @ c @ [parser_bottom G]) (c @ [parser_bottom G])"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G d n y j i c ca)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n y j i c ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac G d n y j i c ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d n y j i c ca e cb)(*strict*)
   apply(subgoal_tac "cb \<in> parserHFS_configurations G")
    apply(rename_tac G d n y j i c ca e cb)(*strict*)
    apply(simp add: parser_scheduler_fragments_def parserHFS_get_unfixed_scheduler_DB_def parserHFS_get_scheduler_def get_configuration_def parserHFS_configurations_def)
    apply(clarsimp)
    apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
    apply(case_tac "(parser_fixed_input_length_recN d i - length w)")
     apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
      apply(rule_tac
      B="set(ca@c)"
      in subset_trans)
       apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
       apply(force)
      apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
      apply(rule_tac
      t="ca @ c"
      and s="drop (parser_fixed_input_length_recN d i) w"
      in ssubst)
       apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
       apply(force)
      apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
      apply(rule_tac
      B="set w"
      in subset_trans)
       apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
       apply(rule set_drop_subset)
      apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
     apply(rule_tac
      B="set(ca@c)"
      in nset_mp)
      apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
     apply(rule_tac
      t="ca @ c"
      and s="drop (parser_fixed_input_length_recN d i) w"
      in ssubst)
      apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i c ca e f h l w)(*strict*)
     apply (metis in_set_dropD)
    apply(rename_tac G d n y j i c ca e f h l w nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G d n y j i c ca e cb)(*strict*)
   apply (metis parserHFS.belongs_configurations parserHFS.derivation_initial_belongs)
  apply(rename_tac G d n y j i c ca)(*strict*)
  apply(rule parserHFS.pre_some_position_is_some_position)
    apply(rename_tac G d n y j i c ca)(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
    apply(force)
   apply(rename_tac G d n y j i c ca)(*strict*)
   apply(force)
  apply(rename_tac G d n y j i c ca)(*strict*)
  apply(force)
  done

lemma parserHFS_inst_AX_get_unfixed_scheduler_DB_extendable_on_initial_configuration: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G d 0 \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac G d)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "c \<in> parserHFS_configurations G")
    apply(rename_tac G d c)(*strict*)
    apply(simp add: parserHFS_configurations_def parserHFS_get_scheduler_def)
    apply(clarsimp)
    apply(rename_tac G d f h l w)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac G d c)(*strict*)
   apply (metis parserHFS.belongs_configurations parserHFS.derivation_initial_belongs)
  apply(rename_tac G d)(*strict*)
  apply (metis parserHFS.derivation_initial_is_derivation parserHFS.some_position_has_details_at_0)
  done

lemma parserHFS_inst_AX_get_unfixed_scheduler_DB_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation G d \<longrightarrow> parserHFS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>e c. d n = Some (pair e c)) \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G d n \<in> parser_unfixed_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parser_unfixed_schedulers_def parserHFS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(rule drop_suffix_closure)
  apply(simp add: parserHFS_get_scheduler_def)
  apply(subgoal_tac "c \<in> parserHFS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply(rule parserHFS.belongs_configurations)
    apply(rename_tac G d n e c)(*strict*)
    apply(force)
   apply(rename_tac G d n e c)(*strict*)
   apply(force)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserHFS_configurations_def parser_schedulers_def)
  apply(clarsimp)
  done

lemma parserHFS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation G d \<longrightarrow> (\<forall>c. d 0 = Some (pair None c) \<longrightarrow> c \<in> parserHFS_initial_configurations G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G d 0 \<sqsupseteq> [parser_bottom G] \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHFS_set_unfixed_scheduler_DB G d 0 sUF \<in> parserHFS_initial_configurations G))))"
  apply(clarsimp)
  apply(rename_tac G d c sUF)(*strict*)
  apply(simp add: get_configuration_def parserHFS_set_unfixed_scheduler_DB_def parserHFS_initial_configurations_def parserHFS_configurations_def parserHFS_get_fixed_scheduler_DB_def parser_unfixed_schedulers_def parser_schedulers_def suffix_closure_def suffix_def prefix_def)
  apply(clarsimp)
  done

lemma parserHFS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation G d \<longrightarrow> parserHFS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserHFS_get_fixed_scheduler_DB G d n \<in> parser_fixed_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def get_configuration_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b)(*strict*)
  apply(subgoal_tac "b \<in> parserHFS_configurations G")
   apply(rename_tac G d n option b)(*strict*)
   prefer 2
   apply (metis parserHFS.belongs_configurations)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: parserHFS_get_scheduler_def parserHFS_configurations_def parser_fixed_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G d n option f h l w)(*strict*)
  apply(simp add: prefix_closure_def prefix_def parser_schedulers_def)
  apply(case_tac "(parser_fixed_input_length_recN d n - length w)")
   apply(rename_tac G d n option f h l w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d n option f h l w c)(*strict*)
   apply(rule_tac
      x="take (parser_fixed_input_length_recN d n) w @ [parser_bottom G]"
      in exI)
   apply(clarsimp)
   apply (metis in_set_takeD le_fun_def set_take_subset subset_trans)
  apply(rename_tac G d n option f h l w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option f h l w nat c)(*strict*)
  apply(rule_tac
      x="w @ [parser_bottom G]"
      in exI)
  apply(clarsimp)
  done

lemma parserHFS_inst_AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> parserHFS_get_unfixed_scheduler (parserHFS_set_unfixed_scheduler_DB G d n sUF) = sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n y sUF)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_def parserHFS_set_unfixed_scheduler_DB_def get_configuration_def)
  apply(case_tac y)
  apply(rename_tac G d n y sUF option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n sUF option b)(*strict*)
  apply(rule_tac
      t="left_quotient_word (parserHFS_conf_fixed b) (parserHFS_get_fixed_scheduler_DB G d n @ sUF)"
      and s="Some sUF"
      in ssubst)
   apply(rename_tac G d n sUF option b)(*strict*)
   apply(rule left_quotient_word_Some_by_append)
   defer
   apply(force)
  apply(rename_tac G d n sUF option b)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def)
  apply(simp add: get_configuration_def parserHFS_get_scheduler_def)
  apply(rule parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler)
    apply(rename_tac G d n sUF option b)(*strict*)
    apply(force)+
  done

lemma parserHFS_inst_AX_set_unfixed_scheduler_set_unfixed_scheduler_DB_sound: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> parserHFS_set_unfixed_scheduler (the (get_configuration (d n))) sUF = parserHFS_set_unfixed_scheduler_DB G d n sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n y sUF)(*strict*)
  apply(simp add: parserHFS_get_scheduler_def parserHFS_set_unfixed_scheduler_def parserHFS_get_fixed_scheduler_DB_def parserHFS_get_unfixed_scheduler_def parserHFS_set_unfixed_scheduler_DB_def get_configuration_def)
  apply(case_tac y)
  apply(rename_tac G d n y sUF option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n sUF option b)(*strict*)
  apply(subgoal_tac "take (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler b) = parserHFS_conf_fixed b")
   apply(rename_tac G d n sUF option b)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler)
     apply(rename_tac G d n sUF option b)(*strict*)
     apply(force)+
  done

lemma parserHFS_inst_AX_state_based_vs_derivation_based_get_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G d n = parserHFS_get_unfixed_scheduler c)))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def get_configuration_def)
  apply(subgoal_tac "take (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler c) = parserHFS_conf_fixed c")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler)
     apply(rename_tac G d n e c)(*strict*)
     apply(force)+
  apply(rename_tac G d n e c)(*strict*)
  apply(subgoal_tac "parserHFS_get_scheduler c = parserHFS_conf_fixed c @ (parserHFS_get_unfixed_scheduler c)")
   apply(rename_tac G d n e c)(*strict*)
   apply (metis left_quotient_word_drop parserHFS_get_unfixed_scheduler_def parserHFS_get_scheduler_def option.sel)
  apply(rename_tac G d n e c)(*strict*)
  apply(subgoal_tac "c \<in> parserHFS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   apply(simp add: parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G d n e h l w)(*strict*)
   apply(simp add: parserHFS_get_scheduler_def parserHFS_get_unfixed_scheduler_def)
   apply (metis left_quotient_word_Some_by_append append_assoc append_take_drop_id_hlp take_append option.sel)
  apply(rename_tac G d n e c)(*strict*)
  apply (metis parserHFS.belongs_configurations parserHFS.derivation_initial_belongs)
  done

lemma parserHFS_inst_AX_state_based_vs_derivation_based_set_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> (\<forall>sUF. parserHFS_set_unfixed_scheduler_DB G d n sUF = parserHFS_set_unfixed_scheduler c sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n e c sUF)(*strict*)
  apply(simp add: parserHFS_set_unfixed_scheduler_DB_def get_configuration_def parserHFS_set_unfixed_scheduler_def)
  apply(subgoal_tac "parserHFS_get_fixed_scheduler_DB G d n = parserHFS_conf_fixed c")
   apply(rename_tac G d n e c sUF)(*strict*)
   apply(force)
  apply(rename_tac G d n e c sUF)(*strict*)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def get_configuration_def)
  apply(rename_tac G d n e c)(*strict*)
  apply (metis parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler parserHFS_get_scheduler_def)
  done

lemma parserHFS_parser_fixed_input_length_recN_with_derivation_append: "
  i\<le>n
  \<Longrightarrow> parserHFS.derivation M d1
  \<Longrightarrow> parser_fixed_input_length_recN (derivation_append d1 d2 n) i = parser_fixed_input_length_recN d1 i"
  apply(induct i)
   apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(clarsimp)
  apply(simp add: derivation_append_def)
  apply(case_tac "d1 (Suc i)")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> d1 (Suc i) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation M c1 e2 c2")
   apply(rename_tac i a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac i a)(*strict*)
     apply(force)
    apply(rename_tac i a)(*strict*)
    apply(force)
   apply(rename_tac i a)(*strict*)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(simp add: derivation_append_def)
  done

lemma parserHFS_inst_AX_get_fixed_scheduler_DB_restrict: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>x n. x \<le> n \<longrightarrow> (\<forall>d1. parserHFS.derivation G d1 \<longrightarrow> (\<forall>d2. parserHFS_get_fixed_scheduler_DB G (derivation_append d1 d2 n) x = parserHFS_get_fixed_scheduler_DB G d1 x))))"
  apply(clarsimp)
  apply(rename_tac G x n d1 d2)(*strict*)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def parserHFS_get_scheduler_def)
  apply(rule_tac
      t="derivation_append d1 d2 n x"
      and s="d1 x"
      in ssubst)
   apply(rename_tac G x n d1 d2)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G x n d1 d2)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_append d1 d2 n) x"
      and s="parser_fixed_input_length_recN d1 x"
      in ssubst)
   apply(rename_tac G x n d1 d2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G x n d1 d2)(*strict*)
  apply (metis parserHFS_parser_fixed_input_length_recN_with_derivation_append)
  done

lemma parserHFS_inst_AX_unfixed_scheduler_extendable_quasi_preserved_by_set_unfixed_scheduler : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_configurations G \<longrightarrow> (\<forall>c2. c2 \<in> parserHFS_configurations G \<longrightarrow> parserHFS_get_unfixed_scheduler c1 \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHFS_set_unfixed_scheduler c1 (parserHFS_get_unfixed_scheduler c2) = c2 \<longrightarrow> parserHFS_get_unfixed_scheduler c2 \<sqsupseteq> [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G c1 c2)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_def parserHFS_set_unfixed_scheduler_def parserHFS_configurations_def)
  apply(case_tac c1)
  apply(rename_tac G c1 c2 parserHFS_conf_fixeda parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_schedulera)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G c1 c2 parserHFS_conf_fixeda parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduleraa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka w wa)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka w wa c ca cb cc)(*strict*)
  apply(subgoal_tac "left_quotient_word parserHFS_conf_fixeda (wa @ [parser_bottom G]) = Some cb")
   apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka w wa c ca cb cc)(*strict*)
   prefer 2
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka w wa c ca cb cc)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "left_quotient_word parserHFS_conf_fixeda (w @ [parser_bottom G]) = Some ca")
   apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka w wa c ca cb cc)(*strict*)
   prefer 2
   apply(rule left_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka w wa c ca cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka wa c cb cc)(*strict*)
  apply(case_tac cb)
   apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka wa c cb cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka wa c cb cc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. cb = w' @ [x']")
   apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka wa c cb cc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G parserHFS_conf_fixeda parserHFS_conf_stacka wa c cb cc a list)(*strict*)
  apply(thin_tac "cb = a # list")
  apply(force)
  done

lemma parserHFS_inst_AX_unfixed_scheduler_extendable_quasi_preserved_by_set_unfixed_scheduler_prime : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserHFS_configurations G \<longrightarrow> (\<forall>c2. c2 \<in> parserHFS_configurations G \<longrightarrow> \<not> parserHFS_conf_fixed c1 \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHFS_set_unfixed_scheduler c1 (parserHFS_get_unfixed_scheduler c2) = c2 \<longrightarrow> \<not> parserHFS_conf_fixed c2 \<sqsupseteq> [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G c1 c2)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_def parserHFS_set_unfixed_scheduler_def parserHFS_configurations_def)
  apply(case_tac c1)
  apply(rename_tac G c1 c2 parserHFS_conf_fixeda parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_schedulera)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G c1 c2 parserHFS_conf_fixeda parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_schedulera parserHFS_conf_fixedaa parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_scheduleraa)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n m. n \<le> m \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G d n = parserHFS_get_unfixed_scheduler_DB G (derivation_take d m) n))"
  apply(clarsimp)
  apply(rename_tac G d n m)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d m) n"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
   apply(rename_tac G d n m)(*strict*)
   defer
   apply(simp add: derivation_take_def)
  apply(rename_tac G d n m)(*strict*)
  apply (metis parserHFS.derivation_initial_is_derivation parserHFS_parser_fixed_input_length_recN_with_derivation_take)
  done

lemma parserHFS_inst_ATS_SchedUF_SB_axioms: "
  ATS_SchedUF_SB_axioms valid_parser parserHFS_configurations
     parser_step_labels parserHFS_step_relation (@)
     parser_unfixed_schedulers right_quotient_word
     parser_unfixed_scheduler_extendable parserHFS_set_unfixed_scheduler
     parserHFS_get_unfixed_scheduler "
  apply(simp add: ATS_SchedUF_SB_axioms_def)
  apply(simp add: parserHFS_inst_schedUF_closed parserHFS_inst_AX_set_unfixed_scheduler_set parserHFS_inst_AX_get_set_unfixed_scheduler parserHFS_inst_AX_set_unfixed_scheduler_get )
  apply(rule conjI, rule parserHFS_inst_AX_unfixed_scheduler_extendable_quasi_preserved_by_set_unfixed_scheduler)
  apply(rule parserHFS_inst_AX_unfixed_scheduler_right_quotient_split)
  done

lemma parserHFS_inst_ATS_SchedF_SB_axioms: "
  ATS_SchedF_SB_axioms valid_parser parserHFS_configurations parserHFS_step_relation parser_fixed_scheduler_extendable parserHFS_conf_fixed "
  apply(simp add: ATS_SchedF_SB_axioms_def)
  apply(simp add: parserHFS_inst_AX_fixed_scheduler_extendable_translates_backwards )
  done

lemma parserHFS_inst_ATS_Sched_axioms: "
  ATS_Sched_axioms valid_parser parserHFS_configurations
     parser_scheduler_fragments parser_empty_scheduler_fragment (@)
     parser_schedulers parser_schedulers parser_empty_scheduler
     parserHFS_get_scheduler (@)"
  apply(simp add: ATS_Sched_axioms_def)
  apply(simp add: parser_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed parser_inst_AX_extend_scheduler_closed parser_inst_AX_empty_scheduler_in_schedulers parserHFS_inst_AX_get_scheduler_closed )
  done

lemma parserHFS_inst_ATS_Sched_SB_axioms: "
  ATS_Sched_SB_axioms valid_parser parserHFS_configurations
     parser_fixed_scheduler_extendable parser_empty_unfixed_scheduler
     parser_unfixed_scheduler_extendable parserHFS_get_scheduler (@)
     parserHFS_set_unfixed_scheduler parserHFS_get_unfixed_scheduler
     parserHFS_conf_fixed"
  apply(simp add: ATS_Sched_SB_axioms_def)
  apply(simp add: parserHFS_inst_AX_not_extendable_fixed_scheduler_implies_empty_unfixed_scheduler parserHFS_inst_extendable_implies_notempty_unfixed parserHFS_inst_AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler parserHFS_inst_AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable )
  apply(rule parserHFS_inst_AX_equal_up_to_unfixed_scheduler_implies_equal_fixed_scheduler)
  done

print_locale loc_autHFS_4
interpretation "parserHFS" : loc_autHFS_4
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHFS_inst_ATS_axioms parserHFS_inst_ATS_History_axioms parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms parserHFS_inst_ATS_String_State_Modification_axioms parserHFS_inst_ATS_SchedF_SB_axioms parserHFS_inst_ATS_SchedUF_SB_axioms parserHFS_inst_ATS_Sched_SB_axioms parserHFS_inst_ATS_Sched_axioms )
  done

lemma parserHFS_PARSER_UnseenPartStrictlyDecreases: "
  valid_parser P
  \<Longrightarrow> parserHFS.belongs P d
  \<Longrightarrow> parserHFS.derivation P d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> d (i+j) = Some (pair e' c')
  \<Longrightarrow> length (parserHFS_conf_scheduler c) - (parser_fixed_input_length_recN d i) \<ge> length (parserHFS_conf_scheduler c') - (parser_fixed_input_length_recN d (i+j))"
  apply(induct j arbitrary: e' c')
   apply(rename_tac e' c')(*strict*)
   apply(clarsimp)
  apply(rename_tac j e' c')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (i+j) = Some (pair e1 c1) \<and> d (Suc (i+j)) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation P c1 e2 c2")
   apply(rename_tac j e' c')(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+j)"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac j e' c')(*strict*)
     apply(force)
    apply(rename_tac j e' c')(*strict*)
    apply(force)
   apply(rename_tac j e' c')(*strict*)
   apply(force)
  apply(rename_tac j e' c')(*strict*)
  apply(clarsimp)
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(rule_tac
      j="length (parserHFS_conf_scheduler c1) - parser_fixed_input_length_recN d (i + j)"
      in le_trans)
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(thin_tac "length (parserHFS_conf_scheduler c1) - parser_fixed_input_length_recN d (i + j) \<le> length (parserHFS_conf_scheduler c) - parser_fixed_input_length_recN d i")
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(subgoal_tac "e2 \<in> parser_rules P")
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: parserHFS.belongs_def)
   apply(erule_tac
      x="Suc (i+j)"
      in allE)
   apply(clarsimp)
   apply(simp add: parser_step_labels_def)
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(subgoal_tac "length (rule_rpush e2) \<le> length (rule_rpop e2)")
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   prefer 2
   apply(rule valid_parser_rules_rhs_gets_shorter)
    apply(rename_tac j c' e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state c1 = w @ (parserHFS_string_state c')")
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc 0"
      in parserHFS.derivation_monotonically_dec)
        apply(rename_tac j c' e1 e2 c1)(*strict*)
        apply(force)
       apply(rename_tac j c' e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac j c' e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac j c' e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac j c' e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac j c' e1 e2 c1 w)(*strict*)
  apply(simp add: parserHFS_string_state_def)
  apply(subgoal_tac "length w = (length (rule_rpop e2) - length (rule_rpush e2))")
   apply(rename_tac j c' e1 e2 c1 w)(*strict*)
   apply(force)
  apply(rename_tac j c' e1 e2 c1 w)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac j c' e1 e2 c1 w x xa y)(*strict*)
  apply(rule_tac
      t="rule_rpop e2"
      and s="w @ rule_rpush e2"
      in ssubst)
   apply(rename_tac j c' e1 e2 c1 w x xa y)(*strict*)
   apply(force)
  apply(rename_tac j c' e1 e2 c1 w x xa y)(*strict*)
  apply(rule_tac
      t="length (w@rule_rpush e2)"
      and s="length w + length (rule_rpush e2)"
      in ssubst)
   apply(rename_tac j c' e1 e2 c1 w x xa y)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac j c' e1 e2 c1 w x xa y)(*strict*)
  apply(simp (no_asm_use))
  done

lemma parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime: "
  valid_parser M
  \<Longrightarrow> parserHFS.belongs M d
  \<Longrightarrow> parserHFS.derivation M d
  \<Longrightarrow> d m = Some (pair e c)
  \<Longrightarrow> parser_fixed_input_length_recN d m \<le> length (parserHFS_conf_scheduler c)"
  apply(induct m arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac m e c)(*strict*)
  apply(clarsimp)
  apply(case_tac "d (Suc m)")
   apply(rename_tac m e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac m e c a)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e c)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d m = Some (pair e1 c1) \<and> d (Suc m) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation M c1 e2 c2")
   apply(rename_tac m e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc m"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac m e c)(*strict*)
     apply(force)
    apply(rename_tac m e c)(*strict*)
    apply(force)
   apply(rename_tac m e c)(*strict*)
   apply(force)
  apply(rename_tac m e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac m c e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "e2 \<in> parser_rules M")
   apply(rename_tac m c e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: parserHFS.belongs_def)
   apply(erule_tac
      x="Suc m"
      in allE)
   apply(clarsimp)
   apply(simp add: parser_step_labels_def)
  apply(rename_tac m c e1 e2 c1)(*strict*)
  apply(subgoal_tac "length (rule_rpush e2) \<le> length (rule_rpop e2)")
   apply(rename_tac m c e1 e2 c1)(*strict*)
   prefer 2
   apply(rule valid_parser_rules_rhs_gets_shorter)
    apply(rename_tac m c e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac m c e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac m c e1 e2 c1)(*strict*)
  apply(subgoal_tac "valid_parser_step_label M e2")
   apply(rename_tac m c e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac m c e1 e2 c1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac m c e1 e2 c1 parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_schedulera)(*strict*)
  apply(rename_tac c1l c1r)
  apply(rename_tac m c e1 e2 c1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r)(*strict*)
  apply(case_tac c)
  apply(rename_tac m c e1 e2 c1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stack parserHFS_conf_schedulera)(*strict*)
  apply(rename_tac c2l c2r)
  apply(rename_tac m c e1 e2 c1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac m c e1 e2 c1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r rule_lpop rule_rpopa rule_lpush rule_rpusha)(*strict*)
  apply(rename_tac l1 r1 cons_l2 r2)
  apply(rename_tac m c e1 e2 c1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(case_tac "parser_fixed_input_length_recN d m \<ge> length r1")
   apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 r1 cons_l2 r2)(*strict*)
   apply(rule_tac
      t="max (parser_fixed_input_length_recN d m) (length r1)"
      and s="parser_fixed_input_length_recN d m"
      in ssubst)
    apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 r1 cons_l2 r2)(*strict*)
    apply(force)
   apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 r1 cons_l2 r2)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history l1 r1 cons_l2 r2 x xa y)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history l1 cons_l2 r2 x xa y k w xc)(*strict*)
   apply (metis concat_asso diff_add_inverse diff_cancel diff_le_mono length_Suc length_append add.commute)
  apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(rule_tac
      t="max (parser_fixed_input_length_recN d m) (length r1)"
      and s="length r1"
      in ssubst)
   apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 r1 cons_l2 r2)(*strict*)
   apply(force)
  apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history c1l c1r parserHFS_conf_fixeda parserHFS_conf_historya c2l c2r l1 cons_l2 r2 k w xa)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac m e1 parserHFS_conf_fixed parserHFS_conf_history l1 cons_l2 r2 k w xa x xb y)(*strict*)
  apply (metis drop_length_append length_Suc)
  done

lemma parserHFS_schedUF_db_decreases: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> \<exists>w. parserHFS_get_unfixed_scheduler_DB G d i = w @ (parserHFS_get_unfixed_scheduler_DB G d j)"
  apply(rule_tac
      t="parserHFS_get_unfixed_scheduler_DB G d i"
      and s="drop (parser_fixed_input_length_recN d i) (parserHFS_conf_scheduler ci)"
      in ssubst)
   apply(simp add: parserHFS_get_unfixed_scheduler_DB_def get_configuration_def parserHFS_get_scheduler_def)
  apply(rule_tac
      t="parserHFS_get_unfixed_scheduler_DB G d j"
      and s="drop (parser_fixed_input_length_recN d j) (parserHFS_conf_scheduler cj)"
      in ssubst)
   apply(simp add: parserHFS_get_unfixed_scheduler_DB_def get_configuration_def parserHFS_get_scheduler_def)
  apply(subgoal_tac "length (parserHFS_conf_scheduler ci) - (parser_fixed_input_length_recN d i) \<ge> length (parserHFS_conf_scheduler cj) - (parser_fixed_input_length_recN d (i+(j-i)))")
   prefer 2
   apply(rule_tac parserHFS_PARSER_UnseenPartStrictlyDecreases)
       apply(force)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(force)
      apply(force)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state ci = w @ parserHFS_string_state cj")
   prefer 2
   apply(rule_tac
      j="j-i"
      and d="d"
      in parserHFS.derivation_monotonically_dec)
        apply(force)
       apply(force)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(force)
      apply(force)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: parserHFS_string_state_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d j \<le> length (parserHFS_conf_scheduler cj)")
   apply(rename_tac w)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d i \<le> length (parserHFS_conf_scheduler ci)")
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_fixed_input_length_recN d i - length w \<le> parser_fixed_input_length_recN d j")
     apply(rename_tac w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(rule_tac
      x="(drop (parser_fixed_input_length_recN d i) w) @ (take (parser_fixed_input_length_recN d j - (parser_fixed_input_length_recN d i - length w)) (drop (parser_fixed_input_length_recN d i - length w) (parserHFS_conf_scheduler cj)))"
      in exI)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
    apply (metis append_take_drop_id_hlp drop_distrib_append drop_take take_all_length)
   apply(rename_tac w)(*strict*)
   apply(rule parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(rule parserHFS.derivation_initial_belongs)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(rule parserHFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(rule parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(rule parserHFS.derivation_initial_belongs)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule parserHFS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(force)
  done

lemma parserHFS_inst_AX_schedF_db_extendable_translates_backwards: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d1. parserHFS.derivation G d1 \<longrightarrow> parserHFS.belongs G d1 \<longrightarrow> (\<forall>n x. (\<exists>y. d1 (n + x) = Some y) \<longrightarrow> \<not> parserHFS_get_fixed_scheduler_DB G d1 (n + x) \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> parserHFS_get_fixed_scheduler_DB G d1 n \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G d1 n x y)(*strict*)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def)
  apply(case_tac y)
  apply(rename_tac G d1 n x y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d1 n x option b)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 n = Some (pair e c)")
   apply(rename_tac G d1 n x option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "parser_fixed_input_length_recN d1 n = length (parserHFS_get_scheduler c)")
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_fixed_input_length_recN d1 (n+x) = length (parserHFS_get_scheduler b)")
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(subgoal_tac "b \<in> parserHFS_configurations G")
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(simp add: parserHFS_configurations_def suffix_def parserHFS_get_scheduler_def)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply (metis parserHFS.belongs_configurations)
    apply(rename_tac G d1 n x option b e c)(*strict*)
    prefer 2
    apply(subgoal_tac "c \<in> parserHFS_configurations G")
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(subgoal_tac "parser_fixed_input_length_recN d1 n \<le> length (parserHFS_conf_scheduler c)")
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(simp add: parserHFS_configurations_def suffix_def parserHFS_get_scheduler_def)
      apply(clarsimp)
      apply(rename_tac G d1 n x option b e ca f l cb w)(*strict*)
      apply(case_tac "parser_fixed_input_length_recN d1 n - length w")
       apply(rename_tac G d1 n x option b e ca f l cb w)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "parser_bottom G \<in> set w")
        apply(rename_tac G d1 n x option b e ca f l cb w)(*strict*)
        apply(force)
       apply(rename_tac G d1 n x option b e ca f l cb w)(*strict*)
       apply (metis butlast_if_match_direct butlast_if_match_direct2_prime in_set_takeD kPrefix_def not_Cons_self2 self_append_conv)
      apply(rename_tac G d1 n x option b e ca f l cb w nat)(*strict*)
      apply(clarsimp)
      apply(rename_tac G d1 n x option b e ca f l cb nat)(*strict*)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(rule parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac G d1 n x option b e c)(*strict*)
        apply(force)
       apply(rename_tac G d1 n x option b e c)(*strict*)
       apply(force)
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(force)
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply (metis parserHFS.belongs_configurations)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   prefer 2
   apply(rename_tac G d1 n x option b)(*strict*)
   apply(rule parserHFS.pre_some_position_is_some_position)
     apply(rename_tac G d1 n x option b)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac G d1 n x option b)(*strict*)
    apply(force)
   apply(rename_tac G d1 n x option b)(*strict*)
   apply(force)
  apply(rename_tac G d1 n x option b e c)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d1 (n+x) \<le> length (parserHFS_conf_scheduler b)")
   apply(rename_tac G d1 n x option b e c)(*strict*)
   prefer 2
   apply(rule parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(force)
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply(force)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   apply(force)
  apply(rename_tac G d1 n x option b e c)(*strict*)
  apply(subgoal_tac "length (parserHFS_conf_scheduler c) - (parser_fixed_input_length_recN d1 n) \<ge> length (parserHFS_conf_scheduler b) - (parser_fixed_input_length_recN d1 (n+x))")
   apply(rename_tac G d1 n x option b e c)(*strict*)
   prefer 2
   apply(rule parserHFS_PARSER_UnseenPartStrictlyDecreases)
       apply(rename_tac G d1 n x option b e c)(*strict*)
       apply(force)
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(force)
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply(force)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   apply(force)
  apply(rename_tac G d1 n x option b e c)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_get_scheduler_def)
  done

lemma parserHFS_inst_AX_sched_modification_preserves_steps: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>dh n. maximum_of_domain dh n \<longrightarrow> parserHFS.derivation G dh \<longrightarrow> parserHFS.belongs G dh \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> (\<exists>sF. \<not> sF \<sqsupseteq> [parser_bottom G]) \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>m e2 c2. dh (Suc m) = Some (pair (Some e2) c2) \<longrightarrow> (\<forall>e1 c1. dh m = Some (pair e1 c1) \<longrightarrow> parserHFS_step_relation G c1 e2 c2 \<longrightarrow> parserHFS_step_relation G (parserHFS_set_unfixed_scheduler_DB G dh m (the (right_quotient_word (parserHFS_get_unfixed_scheduler_DB G dh m) (parserHFS_get_unfixed_scheduler_DB G dh n)) @ sUF)) e2 (parserHFS_set_unfixed_scheduler_DB G dh (Suc m) (the (right_quotient_word (parserHFS_get_unfixed_scheduler_DB G dh (Suc m)) (parserHFS_get_unfixed_scheduler_DB G dh n)) @ sUF))))))"
  apply(clarsimp)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1)(*strict*)
  apply(simp add: get_configuration_def parserHFS_set_unfixed_scheduler_DB_def parserHFS_get_fixed_scheduler_DB_def parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
  apply(subgoal_tac "Suc m \<le> n")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
   prefer 2
   apply (metis less_eq_Suc_le_raw not_Some_eq not_less_eq parserHFS.no_some_beyond_maximum_of_domain)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
  apply(subgoal_tac "suffix (parserHFS_get_unfixed_scheduler_DB G dh m) (parserHFS_get_unfixed_scheduler_DB G dh (Suc m))")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
   prefer 2
   apply(rule_tac
      n="n"
      in parserHFS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient)
        apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
        apply(force)
       apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
       apply(force)
      apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
      apply(force)
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
  apply(subgoal_tac "suffix (parserHFS_get_unfixed_scheduler_DB G dh (Suc m)) (parserHFS_get_unfixed_scheduler_DB G dh n)")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
   prefer 2
   apply(rule_tac
      n="n"
      in parserHFS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient)
        apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
        apply(force)
       apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
       apply(force)
      apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
      apply(force)
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa y)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
  apply(rule_tac
      t="right_quotient_word (ca @ cb @ parserHFS_get_unfixed_scheduler_DB G dh n) (parserHFS_get_unfixed_scheduler_DB G dh n)"
      and s="Some (ca@cb)"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="right_quotient_word (cb @ parserHFS_get_unfixed_scheduler_DB G dh n) (parserHFS_get_unfixed_scheduler_DB G dh n)"
      and s="Some cb"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(simp add: parserHFS_get_scheduler_def)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
     apply(force)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc)(*strict*)
  apply(case_tac "parser_fixed_input_length_recN dh m - length (rule_rpop e2)")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "max (parser_fixed_input_length_recN dh m) (length (rule_rpop e2)) = length (rule_rpop e2)")
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc)(*strict*)
   apply(clarsimp)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
   apply(rule_tac
      t="length (xc @ rule_rpush e2) - length (rule_rpush e2)"
      and s="length xc"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
    apply (metis append_length_inc diff_diff_cancel drop_prefix_closureise length_drop)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
   apply(rule_tac
      t="length (xc @ rule_rpush e2) - length xc"
      and s="length(rule_rpush e2)"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
    apply (metis drop_prefix_closureise length_drop)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
   apply(rule_tac
      t="take (length (rule_rpush e2)) (rule_rpush e2)"
      and s="rule_rpush e2"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
    apply (metis le_refl take_all)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
   apply(rule_tac
      x="cb @ c @ [parser_bottom G]"
      in exI)
   apply(clarsimp)
   apply(subgoal_tac "prefix (drop (parser_fixed_input_length_recN dh m) (kPrefix k (w @ [parser_bottom G]))) ca \<or> prefix ca (drop (parser_fixed_input_length_recN dh m) (kPrefix k (w @ [parser_bottom G])))")
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc "cd")(*strict*)
    apply (metis valid_parser_rules_rhs_gets_shorter append_Nil2 append_eq_appendI append_self_conv2 append_take_drop_id_hlp diff_diff_cancel drop_append2)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc k w xc)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "max (parser_fixed_input_length_recN dh m) (length (rule_rpop e2)) = parser_fixed_input_length_recN dh m")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat)(*strict*)
  apply(clarsimp)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
  apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
  apply(rule_tac
      t="length (xc @ rule_rpush e2) - length (rule_rpush e2)"
      and s="length xc"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
   apply (metis append_length_inc diff_diff_cancel drop_prefix_closureise length_drop)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
  apply(rule_tac
      t="length xc + length (rule_rpush e2)"
      and s="length (kPrefix k (w @ [parser_bottom G]))"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
   apply (metis length_append)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN dh m - length (kPrefix k (w @ [parser_bottom G]))"
      and s="Suc nat"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh m - length xc \<ge> length (rule_rpush e2)")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
   prefer 2
   apply (metis diff_diff_left diff_is_0_eq length_append lessI less_zeroE nat_le_linear)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc)(*strict*)
  apply(clarsimp)
  apply(simp add: parser_unfixed_schedulers_def suffix_closure_def suffix_def parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa y c ca cb e cc nat k w xc "cd")(*strict*)
  apply (metis valid_parser_rules_rhs_gets_shorter parser_step_labels_def append_self_conv2 drop_prefix_closureise le_add_diff_inverse2 add.commute nat_minus_add_max parserHFS_string_state_def prefix_def)
  done

lemma parserHFS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserHFS_get_fixed_scheduler_DB G d n @ parserHFS_get_unfixed_scheduler_DB G d n = ATS_Sched.get_scheduler_nth parserHFS_get_scheduler d n)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserHFS.get_scheduler_nth_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def)
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  done

lemma parserHFS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserHFS_get_fixed_scheduler_DB G d n @ parserHFS_get_unfixed_scheduler_DB G d n \<in> parser_schedulers G))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def parserHFS_get_scheduler_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(simp add: get_configuration_def parserHFS_get_unfixed_scheduler_DB_def parserHFS_get_scheduler_def)
  apply(subgoal_tac "b \<in> parserHFS_configurations G")
   apply(rename_tac G d n y option b)(*strict*)
   prefer 2
   apply (metis parserHFS.belongs_configurations parserHFS.derivation_initial_belongs)
  apply(rename_tac G d n y option b)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d n option f h l w)(*strict*)
  apply(simp add: parser_schedulers_def)
  done

lemma parserHFS_parser_fixed_input_length_recN_equal_by_labels: "
  parserHFS.derivation G d1
  \<Longrightarrow> parserHFS.derivation G d2
  \<Longrightarrow> (\<And>i. i\<le>n \<longrightarrow> get_label (d1 i) = get_label (d2 i))
  \<Longrightarrow> parser_fixed_input_length_recN d1 n = parser_fixed_input_length_recN d2 n"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d1 (Suc n)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="Suc n"
      in meta_allE)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(case_tac "d2 (Suc n)")
    apply(rename_tac n)(*strict*)
    prefer 2
    apply(rename_tac n a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac n a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
  apply(rename_tac n a)(*strict*)
  apply(erule_tac
      x="Suc n"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: get_label_def)
  apply(case_tac a)
  apply(rename_tac n a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n b)(*strict*)
  apply(case_tac "d2 (Suc n)")
   apply(rename_tac n b)(*strict*)
   apply(clarsimp)
  apply(rename_tac n b a)(*strict*)
  apply(case_tac a)
  apply(rename_tac n b a option ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac n b option ba)(*strict*)
  apply(case_tac option)
   apply(rename_tac n b option ba)(*strict*)
   apply(clarsimp)
  apply(rename_tac n b option ba a)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_inst_ATS_SchedUF_DB_axioms: "
  ATS_SchedUF_DB_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parser_scheduler_fragments
     parser_unfixed_schedulers right_quotient_word
     parser_unfixed_scheduler_extendable parserHFS_set_unfixed_scheduler_DB
     parserHFS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_SchedUF_DB_axioms_def)
  apply(simp add: parserHFS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations parserHFS_inst_AX_get_unfixed_scheduler_DB_extendable_on_initial_configuration parserHFS_inst_AX_get_unfixed_scheduler_DB_closed parserHFS_inst_get_unfixed_scheduler_DB_constructs_right_quotient )
  apply(rule parserHFS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take)
  done

lemma parserHFS_inst_ATS_SchedF_DB_axioms: "
  ATS_SchedF_DB_axioms valid_parser parserHFS_configurations
     parser_step_labels parserHFS_step_relation parser_fixed_schedulers
     parser_fixed_scheduler_extendable parserHFS_get_fixed_scheduler_DB "
  apply(simp add: ATS_SchedF_DB_axioms_def)
  apply(simp add: parserHFS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers parserHFS_inst_AX_get_fixed_scheduler_DB_restrict parserHFS_inst_AX_schedF_db_extendable_translates_backwards )
  done

lemma parserHFS_inst_AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB: "
   \<forall>G::('stack, 'event, 'marker) parser.
       valid_parser G \<longrightarrow>
       (\<forall>d::(('stack, 'event) parser_step_label,
                   ('stack, 'event) parserHFS_conf) derivation.
           ATS.derivation_initial parserHFS_initial_configurations
            parserHFS_step_relation G d \<longrightarrow>
           (\<forall>n::nat.
               (\<exists>y::(('stack, 'event) parser_step_label,
                    ('stack, 'event) parserHFS_conf) derivation_configuration.
                   d n = Some y) \<longrightarrow>
               (\<not> parserHFS_get_fixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G]) =
               parserHFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def parserHFS_get_fixed_scheduler_DB_def get_configuration_def parserHFS_get_scheduler_def)
  apply(case_tac y)
  apply(rename_tac G d n y option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: suffix_def)
  apply(subgoal_tac "c \<in> parserHFS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply (metis parserHFS.derivation_initial_configurations)
  apply(rename_tac G d n e c)(*strict*)
  apply(rule antisym)
   apply(rename_tac G d n e c)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G d n e c ca cb)(*strict*)
   apply(subgoal_tac "parserHFS_conf_scheduler c = (cb @ [parser_bottom G]) @ (ca @ [parser_bottom G])")
    apply(rename_tac G d n e c ca cb)(*strict*)
    prefer 2
    apply(rule_tac
      t="cb @ [parser_bottom G]"
      and s="take (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler c)"
      in ssubst)
     apply(rename_tac G d n e c ca cb)(*strict*)
     apply(force)
    apply(rename_tac G d n e c ca cb)(*strict*)
    apply(rule_tac
      t="ca @ [parser_bottom G]"
      and s="drop (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler c)"
      in ssubst)
     apply(rename_tac G d n e c ca cb)(*strict*)
     apply(force)
    apply(rename_tac G d n e c ca cb)(*strict*)
    apply (metis append_Cons append_take_drop_id)
   apply(rename_tac G d n e c ca cb)(*strict*)
   apply(thin_tac "drop (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler c) = ca @ [parser_bottom G]")
   apply(thin_tac "take (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler c) = cb @ [parser_bottom G]")
   apply(subgoal_tac "c \<notin> parserHFS_configurations G")
    apply(rename_tac G d n e c ca cb)(*strict*)
    prefer 2
    apply(simp add: parserHFS_configurations_def)
    apply(force)
   apply(rename_tac G d n e c ca cb)(*strict*)
   apply(force)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d n e f h l w)(*strict*)
  apply(rule_tac
      xs="take (parser_fixed_input_length_recN d n) w @ take (parser_fixed_input_length_recN d n - length w) [parser_bottom G]"
      in rev_cases)
   apply(rename_tac G d n e f h l w)(*strict*)
   prefer 2
   apply(rename_tac G d n e f h l w ys y)(*strict*)
   apply(clarsimp)
   apply(case_tac "parser_fixed_input_length_recN d n - length w")
    apply(rename_tac G d n e f h l w ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac G d n e f h l w ys y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac G d n e f h l w)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_inst_ATS_Sched_DB0_axioms: "
  ATS_Sched_DB0_axioms valid_parser parserHFS_configurations
     parserHFS_initial_configurations parser_step_labels
     parserHFS_step_relation parser_fixed_scheduler_extendable
     parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parser_schedulers
     parserHFS_get_scheduler (@) parserHFS_set_unfixed_scheduler_DB
     parserHFS_get_unfixed_scheduler_DB parserHFS_get_fixed_scheduler_DB "
  apply(simp add: ATS_Sched_DB0_axioms_def)
  apply(simp add: parserHFS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime parserHFS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth parserHFS_inst_AX_sched_modification_preserves_steps parserHFS_inst_AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB )
  done

interpretation "parserHFS" : loc_autHFS_5
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHFS_inst_ATS_axioms parserHFS_inst_ATS_History_axioms parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms parserHFS_inst_ATS_String_State_Modification_axioms parserHFS_inst_ATS_Sched_SB_axioms parserHFS_inst_ATS_SchedF_SB_axioms parserHFS_inst_ATS_SchedUF_SB_axioms parserHFS_inst_ATS_SchedF_DB_axioms parserHFS_inst_ATS_SchedUF_DB_axioms parserHFS_inst_ATS_Sched_axioms parserHFS_inst_ATS_Sched_DB0_axioms )
  done

lemma mod_preserves_derivation_prime: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> sUF \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHFS.derivation_initial G dh
  \<Longrightarrow> parserHFS.derivation G (parserHFS.replace_unfixed_scheduler_DB G dh sUF n)"
  apply(simp add: parserHFS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
    apply(clarsimp)
   apply(rule parserHFS.some_position_has_details_at_0)
   apply(simp add: parserHFS.derivation_initial_def)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "(parserHFS.replace_unfixed_scheduler_DB G dh sUF n (Suc nat))")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh nat = Some (pair e1 c1) \<and> dh (Suc nat) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac nat option b)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac nat option b)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac nat option b)(*strict*)
    apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def)
    apply(case_tac "dh (Suc nat)")
     apply(rename_tac nat option b)(*strict*)
     apply(force)
    apply(rename_tac nat option b a)(*strict*)
    apply(force)
   apply(rename_tac nat option b)(*strict*)
   apply(force)
  apply(rename_tac nat option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b e1 e2 c1 c2)(*strict*)
  apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
  apply(rule conjI)
   apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
   apply(simp add: parserHFS_set_unfixed_scheduler_DB_def get_configuration_def)
  apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHFS_get_unfixed_scheduler_DB G dh nat = w @ (parserHFS_get_unfixed_scheduler_DB G dh (Suc nat))")
   apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
   apply(subgoal_tac "\<exists>w. parserHFS_get_unfixed_scheduler_DB G dh (Suc nat) = w @ (parserHFS_get_unfixed_scheduler_DB G dh n)")
    apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa y w wa)(*strict*)
    apply(simp add: right_quotient_word_def)
    apply(subgoal_tac "valid_parser_step_label G e2")
     apply(rename_tac nat e1 e2 c1 c2 x xa y w wa)(*strict*)
     prefer 2
     apply(simp add: valid_parser_def)
    apply(rename_tac nat e1 e2 c1 c2 x xa y w wa)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc)(*strict*)
    apply(simp add: parserHFS_set_unfixed_scheduler_DB_def parserHFS_get_fixed_scheduler_DB_def parserHFS_get_unfixed_scheduler_DB_def parserHFS_get_scheduler_def get_configuration_def)
    apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
     apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c)(*strict*)
     apply(case_tac "(parser_fixed_input_length_recN dh nat) - (length (kPrefix k (wb @ [parser_bottom G])))")
      apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "max (parser_fixed_input_length_recN dh nat) (length (kPrefix k (wb @ [parser_bottom G]))) = (length (kPrefix k (wb @ [parser_bottom G])))")
       apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "(length (kPrefix k (wb @ [parser_bottom G])) - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2))) = length (rule_rpush e2)")
       apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c)(*strict*)
       prefer 2
       apply (metis diff_diff_cancel dropPrecise drop_length_append length_drop)
      apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c)(*strict*)
      apply(clarsimp)
      apply(rename_tac nat e1 e2 c1 c2 x y wa k wb xc e c)(*strict*)
      apply(simp add: suffix_def)
      apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "max (parser_fixed_input_length_recN dh nat) (length (kPrefix k (wb @ [parser_bottom G]))) = (parser_fixed_input_length_recN dh nat)")
      apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "take (parser_fixed_input_length_recN dh nat - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2))) (rule_rpush e2) = rule_rpush e2")
      apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply(rule take_all)
      apply (metis Suc_not_Zero diff_diff_cancel diff_diff_left diff_is_0_eq dropPrecise drop_length_append length_append length_drop nat_le_linear)
     apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(parser_fixed_input_length_recN dh nat - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2) + length (rule_rpush e2))) = Suc nata")
      apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply (metis butn_length butn_prefix_closureise length_append)
     apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 x xa y wa k wb xc e c nata)(*strict*)
     apply(simp add: suffix_def)
     apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc)(*strict*)
    apply(rule parserHFS.some_position_has_details_before_max_dom)
      apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa y w wa k wb xc)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
   apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
    apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
    prefer 2
    apply(rule parserHFS.some_position_has_details_before_max_dom)
      apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x xa y w e c)(*strict*)
   apply(rule parserHFS_schedUF_db_decreases)
       apply(rename_tac nat e1 e2 c1 c2 x xa y w e c)(*strict*)
       apply(force)+
   apply(rename_tac nat e1 e2 c1 c2 x xa y w e c)(*strict*)
   defer
   apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
   apply(rule parserHFS_schedUF_db_decreases)
       apply(rename_tac nat e1 e2 c1 c2 x xa y)(*strict*)
       apply(force)+
  apply(rename_tac nat e1 e2 c1 c2 x xa y w e c)(*strict*)
  defer
  apply (metis not_None_eq parserHFS.allPreMaxDomSome_prime parserHFS.derivation_initial_is_derivation)
  done

lemma parserHFS_inst_AX_replace_unfixed_scheduler_DB_sound: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d n. maximum_of_domain d n \<longrightarrow> parserHFS.derivation_initial G d \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G d sUF n) n = sUF))"
  apply(clarsimp)
  apply(rename_tac G d n sUF)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS.replace_unfixed_scheduler_DB G d sUF n) n"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
   apply(rename_tac G d n sUF)(*strict*)
   defer
   apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
    apply(rename_tac G d n sUF)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply(simp add: get_configuration_def)
    apply(rule_tac
      t="right_quotient_word (parserHFS_get_unfixed_scheduler_DB G d n) (parserHFS_get_unfixed_scheduler_DB G d n)"
      and s="Some []"
      in ssubst)
     apply(rename_tac G d n sUF e c)(*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHFS_set_unfixed_scheduler_DB_def get_configuration_def parserHFS_get_scheduler_def)
    apply(subgoal_tac "parser_fixed_input_length_recN d n = length (parserHFS_get_fixed_scheduler_DB G d n)")
     apply(rename_tac G d n sUF e c)(*strict*)
     apply(force)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply(simp add: parserHFS_get_fixed_scheduler_DB_def get_configuration_def)
    apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserHFS_get_scheduler c)")
     apply(rename_tac G d n sUF e c)(*strict*)
     apply(force)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply (metis Nil_is_append_conv drop_eq_Nil not_Cons_self order_less_asym parserHFS_get_scheduler_def suffix_def trivNat)
   apply(rename_tac G d n sUF)(*strict*)
   apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac G d n sUF y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G d n sUF y option b)(*strict*)
   apply(force)
  apply(rename_tac G d n sUF)(*strict*)
  apply(rule parserHFS_parser_fixed_input_length_recN_equal_by_labels)
    apply(rename_tac G d n sUF)(*strict*)
    defer
    apply(simp add: parserHFS.derivation_initial_def)
    apply(force)
   apply(rename_tac G d n sUF i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. d i =Some (pair e c)")
    apply(rename_tac G d n sUF i)(*strict*)
    prefer 2
    apply(rule parserHFS.some_position_has_details_before_max_dom)
      apply(rename_tac G d n sUF i)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(rename_tac G d n sUF i)(*strict*)
     apply(force)
    apply(rename_tac G d n sUF i)(*strict*)
    apply(force)
   apply(rename_tac G d n sUF i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d n sUF i e c)(*strict*)
   apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def)
   apply(simp add: get_label_def)
  apply(rename_tac G d n sUF)(*strict*)
  apply(rule mod_preserves_derivation_prime)
     apply(rename_tac G d n sUF)(*strict*)
     apply(force)+
  done

lemma parserHFS_inst_ATS_Sched_DB_axioms: "
  ATS_Sched_DB_axioms valid_parser parserHFS_initial_configurations
     parserHFS_step_relation parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserHFS_set_unfixed_scheduler_DB
     parserHFS_get_unfixed_scheduler_DB "
  apply(simp add: ATS_Sched_DB_axioms_def)
  apply(rule parserHFS_inst_AX_replace_unfixed_scheduler_DB_sound)
  done

print_locale loc_autHFS_5b
interpretation "parserHFS" : loc_autHFS_5b
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHFS_inst_ATS_axioms parserHFS_inst_ATS_History_axioms parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms parserHFS_inst_ATS_String_State_Modification_axioms parserHFS_inst_ATS_Sched_SB_axioms parserHFS_inst_ATS_SchedF_SB_axioms parserHFS_inst_ATS_SchedUF_SB_axioms parserHFS_inst_ATS_Sched_DB0_axioms parserHFS_inst_ATS_SchedF_DB_axioms parserHFS_inst_ATS_SchedUF_DB_axioms parserHFS_inst_ATS_Sched_DB_axioms parserHFS_inst_ATS_Sched_axioms )
  done

lemma parserHFS_inst_AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserHFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (parserHFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] = ATS_SchedUF_SB.get_unfixed_scheduler_nth parserHFS_get_unfixed_scheduler d n \<sqsupseteq> [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: suffix_def)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac G d n y)(*strict*)
   prefer 2
   apply(case_tac y)
   apply(rename_tac G d n y option b)(*strict*)
   apply(force)
  apply(rename_tac G d n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def get_configuration_def parserHFS.get_unfixed_scheduler_nth_def parserHFS_get_unfixed_scheduler_def parserHFS_get_scheduler_def)
  apply(subgoal_tac "c \<in> parserHFS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply (metis parserHFS.belongs_configurations parserHFS.derivation_initial_belongs)
  apply(rename_tac G d n e c)(*strict*)
  apply(subgoal_tac "take (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler c) = parserHFS_conf_fixed c")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply(rule parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler)
     apply(rename_tac G d n e c)(*strict*)
     apply(force)+
  apply(rename_tac G d n e c)(*strict*)
  apply (metis left_quotient_word_drop parserHFS_get_unfixed_scheduler_def parserHFS_get_scheduler_def option.sel)
  done

lemma parserHFS_inst_ATS_SchedF_SDB_axioms: "
  ATS_SchedF_SDB_axioms valid_parser parserHFS_initial_configurations parserHFS_step_relation parserHFS_conf_fixed parserHFS_get_fixed_scheduler_DB "
  apply(simp add: ATS_SchedF_SDB_axioms_def)
  apply(rule parserHFS_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler)
  done

lemma parserHFS_inst_ATS_SchedUF_SDB_axioms: "
  ATS_SchedUF_SDB_axioms valid_parser parserHFS_initial_configurations
     parserHFS_step_relation parser_unfixed_schedulers
     parser_unfixed_scheduler_extendable parserHFS_set_unfixed_scheduler
     parserHFS_get_unfixed_scheduler parserHFS_set_unfixed_scheduler_DB
     parserHFS_get_unfixed_scheduler_DB "
  apply(simp add: ATS_SchedUF_SDB_axioms_def)
  apply(simp add: parserHFS_inst_AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound parserHFS_inst_AX_set_unfixed_scheduler_set_unfixed_scheduler_DB_sound parserHFS_inst_AX_state_based_vs_derivation_based_get_unfixed_scheduler parserHFS_inst_AX_state_based_vs_derivation_based_set_unfixed_scheduler )
  done

lemma parserHFS_inst_ATS_Sched_SDB_axioms: "
  ATS_Sched_SDB_axioms valid_parser parserHFS_initial_configurations
     parserHFS_step_relation parser_unfixed_scheduler_extendable
     parserHFS_get_unfixed_scheduler parserHFS_get_unfixed_scheduler_DB "
  apply(simp add: ATS_Sched_SDB_axioms_def)
  apply(simp add: parserHFS_inst_AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations)
  done

interpretation "parserHFS" : loc_autHFS_6
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHFS_inst_ATS_axioms parserHFS_inst_ATS_History_axioms parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms parserHFS_inst_ATS_String_State_Modification_axioms parserHFS_inst_ATS_Sched_SB_axioms parserHFS_inst_ATS_SchedF_SB_axioms parserHFS_inst_ATS_SchedUF_SB_axioms parserHFS_inst_ATS_Sched_DB0_axioms parserHFS_inst_ATS_SchedF_DB_axioms parserHFS_inst_ATS_SchedUF_DB_axioms parserHFS_inst_ATS_Sched_DB_axioms parserHFS_inst_ATS_SchedF_SDB_axioms parserHFS_inst_ATS_SchedUF_SDB_axioms parserHFS_inst_ATS_Sched_SDB_axioms parserHFS_inst_ATS_Sched_axioms )
  done

lemma parserHFS_inst_AX_history_no_mod_after_nonextendable_fixed_sched: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. parserHFS_conf_fixed c \<sqsupseteq> [parser_bottom G] \<longrightarrow> c \<in> parserHFS_configurations G \<longrightarrow> (\<forall>e c'. parserHFS_step_relation G c e c' \<longrightarrow> parserHFS_conf_history c = parserHFS_conf_history c')))"
  apply(clarsimp)
  apply(rename_tac G c e c')(*strict*)
  apply(subgoal_tac "parserHFS_conf_fixed c = parserHFS_conf_scheduler c")
   apply(rename_tac G c e c')(*strict*)
   apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G e c' h x xa y w)(*strict*)
   apply(subgoal_tac "drop (length (rule_rpop e) + length xa) (butlast_if_match (rule_rpop e) (parser_bottom G))=[]")
    apply(rename_tac G e c' h x xa y w)(*strict*)
    prefer 2
    apply (metis drop_entire_butlast_if_match drop_length_append length_append)
   apply(rename_tac G e c' h x xa y w)(*strict*)
   apply(clarsimp)
  apply(rename_tac G c e c')(*strict*)
  apply(thin_tac "parserHFS_step_relation G c e c'")
  apply(simp add: parserHFS_configurations_def)
  apply(rename_tac G c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G f h l w)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac G l w c ca cb)(*strict*)
  apply(case_tac ca)
   apply(rename_tac G l w c ca cb)(*strict*)
   apply(force)
  apply(rename_tac G l w c ca cb a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac G l w c ca cb a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G l w c ca cb a list)(*strict*)
  apply(thin_tac "ca=a#list")
  apply(clarsimp)
  done

lemma parserHFS_inst_ATS_determHIST_SB_axioms: "
  ATS_determHIST_SB_axioms valid_parser parserHFS_configurations
     parserHFS_step_relation parserHFS_conf_history
     parser_fixed_scheduler_extendable parserHFS_conf_fixed"
  apply(simp add: ATS_determHIST_SB_axioms_def)
  apply(simp add: parserHFS_inst_AX_history_no_mod_after_nonextendable_fixed_sched )
  done

interpretation "parserHFS" : loc_autHFS_7
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHFS_inst_ATS_axioms parserHFS_inst_ATS_History_axioms parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms parserHFS_inst_ATS_String_State_Modification_axioms parserHFS_inst_ATS_Sched_SB_axioms parserHFS_inst_ATS_SchedF_SB_axioms parserHFS_inst_ATS_SchedUF_SB_axioms parserHFS_inst_ATS_Sched_DB0_axioms parserHFS_inst_ATS_SchedF_DB_axioms parserHFS_inst_ATS_SchedUF_DB_axioms parserHFS_inst_ATS_Sched_DB_axioms parserHFS_inst_ATS_SchedF_SDB_axioms parserHFS_inst_ATS_SchedUF_SDB_axioms parserHFS_inst_ATS_Sched_SDB_axioms parserHFS_inst_ATS_Sched_axioms parserHFS_inst_ATS_determHIST_SB_axioms )
  done

lemma parserHFS_history_in_parser_events_no_bottom: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> set (parserHFS_conf_history c) \<subseteq> parser_events G - {parser_bottom G}"
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x f h l w)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x f l w c ca)(*strict*)
  apply(erule disjE)
   apply(rename_tac x f l w c ca)(*strict*)
   apply(force)
  apply(rename_tac x f l w c ca)(*strict*)
  apply(force)
  done

lemma parserHFS_turning_nonextendable_rule_rpop_complete: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> \<not> parserHFS_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHFS_conf_fixed c1 \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> rule_rpop e1 = parserHFS_conf_scheduler c"
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa y)(*strict*)
  apply(simp add: parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac x xa y f h w)(*strict*)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac x xa y f w c ca cb)(*strict*)
  apply(case_tac xa)
   apply(rename_tac x xa y f w c ca cb)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa y f w c ca cb a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
   apply(rename_tac x xa y f w c ca cb a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xa y f w c ca cb a list)(*strict*)
  apply(thin_tac "xa=a#list")
  apply(clarsimp)
  apply(rename_tac x f c ca cb w')(*strict*)
  apply(subgoal_tac "\<exists>w. rule_rpop e1 = w @ rule_rpush e1")
   apply(rename_tac x f c ca cb w')(*strict*)
   apply(clarsimp)
   apply(rename_tac x f c ca cb w' w)(*strict*)
   apply(subgoal_tac "butlast_if_match f (parser_bottom G)=f")
    apply(rename_tac x f c ca cb w' w)(*strict*)
    apply(clarsimp)
    apply(thin_tac "butlast_if_match f (parser_bottom G)=f")
    apply(case_tac ca)
     apply(rename_tac x f c ca cb w' w)(*strict*)
     apply(force)
    apply(rename_tac x f c ca cb w' w a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
     apply(rename_tac x f c ca cb w' w a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac x f c ca cb w' w a list)(*strict*)
    apply(thin_tac "ca=a#list")
    apply(clarsimp)
    apply(rename_tac x f c cb w' w w'a)(*strict*)
    apply(case_tac "length w + length (rule_rpush e1) \<ge> length f")
     apply(rename_tac x f c cb w' w w'a)(*strict*)
     prefer 2
     apply(case_tac "drop (length w + length (rule_rpush e1)) f")
      apply(rename_tac x f c cb w' w w'a)(*strict*)
      apply(clarsimp)
     apply(rename_tac x f c cb w' w w'a a list)(*strict*)
     apply (metis head_in_set in_set_dropD length_append length_splice not_set_append set_rotate1 rotate_simps)
    apply(rename_tac x f c cb w' w w'a)(*strict*)
    apply(clarsimp)
   apply(rename_tac x f c ca cb w' w)(*strict*)
   apply (metis butlast_if_match_reduces rotate_simps)
  apply(rename_tac x f c ca cb w')(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(rename_tac x f c ca cb w')(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac x f c ca cb w')(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac x f c ca cb w' k w xb)(*strict*)
  apply(rule_tac
      x="xb"
      in exI)
  apply(force)
  done

lemma parserHFS_history_modification_implies_extendable_before: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e c'
  \<Longrightarrow> parserHFS_conf_history c \<noteq> parserHFS_conf_history c'
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> \<not> parserHFS_conf_fixed c \<sqsupseteq> [parser_bottom G]"
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa y)(*strict*)
  apply (metis append_Nil2 butlast_if_match_prefix insert_Nil le_refl nat_le_linear parserHFS.AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler parserHFS_inst_AX_not_extendable_fixed_scheduler_implies_empty_unfixed_scheduler parserHFS_get_scheduler_def mutual_prefix_implies_equality2 prefix_transitive prefix_def)
  done

lemma parserHFS_prefix_of_rhs_wrt_fixed_and_parser_bottom: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> prefix w1 (butlast_if_match (the (left_quotient_word (parserHFS_conf_fixed c) (parserHFS_conf_scheduler c))) (parser_bottom G))"
  apply(simp add: parserHFS_configurations_def parserHFS_step_relation_def prefix_def)
  apply(clarsimp)
  apply(rename_tac f h x xa c ca y w)(*strict*)
  apply(subgoal_tac "left_quotient_word f (rule_rpop e1 @ xa) = Some c")
   apply(rename_tac f h x xa c ca y w)(*strict*)
   prefer 2
   apply (metis left_quotient_word_removes_right_addition)
  apply(rename_tac f h x xa c ca y w)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac f x xa c ca y w cb cc)(*strict*)
  apply(subgoal_tac "prefix f (rule_rpop e1) \<or> prefix (rule_rpop e1) f")
   apply(rename_tac f x xa c ca y w cb cc)(*strict*)
   prefer 2
   apply (metis mutual_prefix_prefix)
  apply(rename_tac f x xa c ca y w cb cc)(*strict*)
  apply(erule disjE)
   apply(rename_tac f x xa c ca y w cb cc)(*strict*)
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac x c ca y w cb cc "cd")(*strict*)
   apply(rule_tac
      t="drop (length (rule_rpop e1) + length cd) (butlast_if_match (rule_rpop e1) (parser_bottom G))"
      and s="[]"
      in ssubst)
    apply(rename_tac x c ca y w cb cc "cd")(*strict*)
    apply (metis drop_entire_butlast_if_match drop_length_append length_append)
   apply(rename_tac x c ca y w cb cc "cd")(*strict*)
   apply(force)
  apply(rename_tac f x xa c ca y w cb cc)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac f x xa c ca y w cb cc "cd")(*strict*)
  apply(subgoal_tac "drop (length (rule_rpop e1)) f=[]")
   apply(rename_tac f x xa c ca y w cb cc "cd")(*strict*)
   prefer 2
   apply (metis drop_all drop_length_append)
  apply(rename_tac f x xa c ca y w cb cc "cd")(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "xa=ca")
   apply(rename_tac f x xa c ca y w cb cc "cd")(*strict*)
   prefer 2
   apply (metis dropPrecise)
  apply(rename_tac f x xa c ca y w cb cc "cd")(*strict*)
  apply(clarsimp)
  apply(rename_tac f x c ca y w cb cc "cd")(*strict*)
  apply(thin_tac "left_quotient_word f (rule_rpop e1 @ ca) = Some c")
  apply(subgoal_tac "c=cd@ca")
   apply(rename_tac f x c ca y w cb cc "cd")(*strict*)
   prefer 2
   apply (metis append_assoc dropPrecise)
  apply(rename_tac f x c ca y w cb cc "cd")(*strict*)
  apply(clarsimp)
  apply(rename_tac f x ca y w cb cc "cd")(*strict*)
  apply(case_tac ca)
   apply(rename_tac f x ca y w cb cc "cd")(*strict*)
   apply(clarsimp)
   apply(rename_tac f x y w cb cc "cd")(*strict*)
   apply(case_tac "cd")
    apply(rename_tac f x y w cb cc "cd")(*strict*)
    apply(clarsimp)
    apply(rename_tac x y w cb cc)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply (metis butlast_if_match_direct2_prime drop_entire_butlast_if_match in_set_conv_nth le_refl length_Suc less_zeroE list.size(3))
   apply(rename_tac f x y w cb cc "cd" a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. cd = w' @ [x']")
    apply(rename_tac f x y w cb cc "cd" a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac f x y w cb cc "cd" a list)(*strict*)
   apply(thin_tac "cd=a#list")
   apply(clarsimp)
   apply(rename_tac f x y w cb cc w' x')(*strict*)
   apply(subgoal_tac "x'=parser_bottom G")
    apply(rename_tac f x y w cb cc w' x')(*strict*)
    prefer 2
    apply (metis Suc_length butn_prefix_closureise concat_asso length_rotate1 list.size(3) nth_append_length rotate_simps)
   apply(rename_tac f x y w cb cc w' x')(*strict*)
   apply(clarsimp)
   apply(rename_tac f x y w cb cc w')(*strict*)
   apply(subgoal_tac "f@w'=w")
    apply(rename_tac f x y w cb cc w')(*strict*)
    prefer 2
    apply (metis Suc_length butn_prefix_closureise concat_asso length_rotate1 list.size(3) rotate_simps)
   apply(rename_tac f x y w cb cc w')(*strict*)
   apply(clarsimp)
   apply(rename_tac f x y cb cc w')(*strict*)
   apply (metis insert_def append_Nil2 butlast_if_match_direct butlast_if_match_pull_out_prime drop_append2 rotate_simps)
  apply(rename_tac f x ca y w cb cc "cd" a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ca = w' @ [x']")
   apply(rename_tac f x ca y w cb cc "cd" a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac f x ca y w cb cc "cd" a list)(*strict*)
  apply(thin_tac "ca=a#list")
  apply(clarsimp)
  apply(rename_tac f x cb cc "cd" w')(*strict*)
  apply(subgoal_tac "butlast_if_match (cd @ w' @ [parser_bottom G]) (parser_bottom G)=cd@w'")
   apply(rename_tac f x cb cc "cd" w')(*strict*)
   prefer 2
   apply (metis butlast_if_match_direct butlast_if_match_pull_out length_Suc list.size(3) nat.simps(2))
  apply(rename_tac f x cb cc "cd" w')(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="w'"
      in exI)
  apply(clarsimp)
  apply (metis butlast_if_match_direct2_prime drop_append2)
  done

lemma parserHFS_parserHFS_mutual_history_extension_hlp: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ w2
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> length w1 \<le> length w2
  \<Longrightarrow> w2 \<sqsubseteq> w1 \<or> w1 \<sqsubseteq> w2"
  apply(rule disjI2)
  apply(rule_tac
      w="butlast_if_match (the (left_quotient_word (parserHFS_conf_fixed c) (parserHFS_conf_scheduler c))) (parser_bottom G)"
      in prefix_common_max)
    apply(rule parserHFS_prefix_of_rhs_wrt_fixed_and_parser_bottom)
        apply(force)+
   apply(rule_tac
      ?c1.0="c2"
      in parserHFS_prefix_of_rhs_wrt_fixed_and_parser_bottom)
       apply(force)+
  done

lemma parserHFS_mutual_history_extension: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ w2
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> w2 \<sqsubseteq> w1 \<or> w1 \<sqsubseteq> w2"
  apply(case_tac "length w1 \<le> length w2")
   apply (metis parserHFS_parserHFS_mutual_history_extension_hlp)
  apply(subgoal_tac "w1 \<sqsubseteq> w2 \<or> w2 \<sqsubseteq> w1")
   apply(force)
  apply (metis linorder_le_cases parserHFS_parserHFS_mutual_history_extension_hlp)
  done

lemma parserHFS_strict_history_extension_implies_pop_extension_hlp: "
  \<forall>c. e2 @ c \<noteq> e1
  \<Longrightarrow> X \<in> set e2 \<longrightarrow> (\<exists>w. e2=w@[X] \<and> X \<notin> set w)
  \<Longrightarrow> X \<in> set e1 \<longrightarrow> (\<exists>w. e1=w@[X] \<and> X \<notin> set w)
  \<Longrightarrow> ca \<noteq> []
  \<Longrightarrow> drop n (butlast_if_match e2 X) @ ca = drop n (butlast_if_match e1 X)
  \<Longrightarrow> length (butlast_if_match e1 X) > n
  \<Longrightarrow> e1 @ caa = e2
  \<Longrightarrow> False"
  apply(case_tac e2)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. e2 = w' @ [x']")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(thin_tac "e2=a#list")
  apply(clarsimp)
  apply(rename_tac w' x')(*strict*)
  apply(case_tac e1)
   apply(rename_tac w' x')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "drop n (butlast_if_match [] X) = []")
    apply(rename_tac w' x')(*strict*)
    prefer 2
    apply (metis drop_entire_butlast_if_match le0 list.size(3))
   apply(rename_tac w' x')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. e1 = w' @ [x']")
   apply(rename_tac w' x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w' x' a list)(*strict*)
  apply(thin_tac "e1=a#list")
  apply(clarsimp)
  apply(rename_tac w' x' w'a x'a)(*strict*)
  apply(subgoal_tac "prefix w' w'a \<or> prefix w'a w'")
   apply(rename_tac w' x' w'a x'a)(*strict*)
   prefer 2
   apply(metis mutual_prefix_prefix)
  apply(rename_tac w' x' w'a x'a)(*strict*)
  apply(erule disjE)
   apply(rename_tac w' x' w'a x'a)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac w' x' x'a c)(*strict*)
   apply(subgoal_tac "c=[]")
    apply(rename_tac w' x' x'a c)(*strict*)
    apply(subgoal_tac "caa=[]")
     apply(rename_tac w' x' x'a c)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' x' x'a c)(*strict*)
    apply (metis append_self_conv2 list.inject)
   apply(rename_tac w' x' x'a c)(*strict*)
   apply (metis Cons_eq_appendI append_Nil insert_Nil length_1_context_empty)
  apply(rename_tac w' x' w'a x'a)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x' w'a x'a c)(*strict*)
  apply(case_tac caa)
   apply(rename_tac x' w'a x'a c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x' w'a x'a c a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. caa = w' @ [x']")
   apply(rename_tac x' w'a x'a c a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x' w'a x'a c a list)(*strict*)
  apply(thin_tac "caa=a#list")
  apply(clarsimp)
  apply(rename_tac x' w'a x'a w')(*strict*)
  apply(case_tac "X=x'")
   apply(rename_tac x' w'a x'a w')(*strict*)
   prefer 2
   apply(clarsimp)
   apply(subgoal_tac "butlast_if_match (w'a @ x'a # w' @ [x']) X = w'a @ x'a # w' @ [x']")
    apply(rename_tac x' w'a x'a w')(*strict*)
    prefer 2
    apply (metis append_Cons butlast_if_match_direct2 butlast_if_match_pull_out_prime)
   apply(rename_tac x' w'a x'a w')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast_if_match (w'a @ [x'a]) X = w'a @ [x'a]")
    apply(rename_tac x' w'a x'a w')(*strict*)
    prefer 2
    apply (metis butlast_if_match_direct2 rotate_simps)
   apply(rename_tac x' w'a x'a w')(*strict*)
   apply(clarsimp)
  apply(rename_tac x' w'a x'a w')(*strict*)
  apply(clarsimp)
  apply(rename_tac w'a x'a w')(*strict*)
  apply(subgoal_tac "butlast_if_match (w'a @ x'a # w' @ [X]) X = w'a @ x'a # w'")
   apply(rename_tac w'a x'a w')(*strict*)
   prefer 2
   apply (metis append_Cons butlast_if_match_direct butlast_if_match_pull_out snoc_eq_iff_butlast)
  apply(rename_tac w'a x'a w')(*strict*)
  apply(clarsimp)
  apply(thin_tac "butlast_if_match (w'a @ x'a # w' @ [X]) X = w'a @ x'a # w'")
  apply(subgoal_tac "butlast_if_match (w'a @ [x'a]) X = w'a@[x'a]")
   apply(rename_tac w'a x'a w')(*strict*)
   prefer 2
   apply (metis butlast_if_match_direct2 rotate_simps)
  apply(rename_tac w'a x'a w')(*strict*)
  apply(subgoal_tac "w'@ca=[]")
   apply(rename_tac w'a x'a w')(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac w'a x'a w')(*strict*)
  apply(force)
  done

lemma parserHFS_strict_history_extension_implies_pop_extension: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ w2
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> w1 \<noteq> w2
  \<Longrightarrow> w2 \<sqsubseteq> w1
  \<Longrightarrow> \<exists>x. rule_rpop e1 @ x = parserHFS_conf_scheduler c
  \<Longrightarrow> \<exists>x. x \<noteq> [] \<and> w2 @ x = w1
  \<Longrightarrow> rule_rpop e2 \<sqsubseteq> rule_rpop e1"
  apply(clarsimp)
  apply(rename_tac x xa)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa xb xc xd xe y ya)(*strict*)
  apply(subgoal_tac "rule_rpop e2 \<sqsubseteq> rule_rpop e1 \<or> rule_rpop e1 \<sqsubseteq> rule_rpop e2")
   apply(rename_tac xa xb xc xd xe y ya)(*strict*)
   prefer 2
   apply (metis mutual_prefix_prefix)
  apply(rename_tac xa xb xc xd xe y ya)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
  apply(case_tac "length (parserHFS_conf_fixed c) < length (butlast_if_match (rule_rpop e1) (parser_bottom G))")
   apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
  apply(rule_tac
      X="parser_bottom G"
      and ?e1.0="rule_rpop e1"
      and ?e2.0="rule_rpop e2"
      in parserHFS_strict_history_extension_implies_pop_extension_hlp)
        apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
        apply(force)
       apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
       apply(subgoal_tac "valid_parser_step_label G e2")
        apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
        apply(simp add: valid_parser_step_label_def)
        apply(clarsimp)
        apply(rename_tac xa xb xc xd xe y ya ca caa k w xf)(*strict*)
        apply(simp add: kPrefix_def)
        apply(case_tac "k - length w")
         apply(rename_tac xa xb xc xd xe y ya ca caa k w xf)(*strict*)
         apply(clarsimp)
         apply (metis in_set_takeD kPrefix_def not_in_diff)
        apply(rename_tac xa xb xc xd xe y ya ca caa k w xf nat)(*strict*)
        apply(clarsimp)
        apply(rename_tac xa xb xc xd xe y ya ca caa k w xf nat x)(*strict*)
        apply (metis not_in_diff)
       apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
       apply(simp add: valid_parser_def)
      apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
      apply(subgoal_tac "valid_parser_step_label G e1")
       apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
       apply(simp add: valid_parser_step_label_def)
       apply(clarsimp)
       apply(rename_tac xa xb xc xd xe y ya ca caa k w xf)(*strict*)
       apply(simp add: kPrefix_def)
       apply(case_tac "k - length w")
        apply(rename_tac xa xb xc xd xe y ya ca caa k w xf)(*strict*)
        apply(clarsimp)
        apply (metis in_set_takeD kPrefix_def not_in_diff)
       apply(rename_tac xa xb xc xd xe y ya ca caa k w xf nat)(*strict*)
       apply(clarsimp)
       apply(rename_tac xa xb xc xd xe y ya ca caa k w xf nat x)(*strict*)
       apply (metis not_in_diff)
      apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
      apply(simp add: valid_parser_def)
     apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
  apply(subgoal_tac "xa=ca")
   apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
   prefer 2
   apply (metis append_injective2)
  apply(rename_tac xa xb xc xd xe y ya ca caa)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_extendable_if_extendable_and_no_parser_bottom_reading_step: "
  valid_parser G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> \<not> parserHFS_conf_fixed c \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> (rule_rpop e1) \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> \<not> parserHFS_conf_fixed c1 \<sqsupseteq> [parser_bottom G]"
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x xa y)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac x xa y ca)(*strict*)
  apply(case_tac "drop (length (rule_rpop e1)) (parserHFS_conf_fixed c)")
   apply(rename_tac x xa y ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "valid_parser_step_label G e1")
    apply(rename_tac x xa y ca)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x xa y ca k w xc)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac x xa y ca k w xc)(*strict*)
     apply(clarsimp)
     apply (metis append_butlast_last_id append_is_Nil_conv last_appendR last_triv_prime not_Cons_self)
    apply(rename_tac x xa y ca k w xc nat)(*strict*)
    apply(force)
   apply(rename_tac x xa y ca)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac x xa y ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. drop (length (rule_rpop e1)) (parserHFS_conf_fixed c) = w' @ [x']")
   apply(rename_tac x xa y ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xa y ca a list)(*strict*)
  apply(thin_tac "drop (length (rule_rpop e1)) (parserHFS_conf_fixed c)=a#list")
  apply(clarsimp)
  apply(rename_tac x xa y w')(*strict*)
  apply(case_tac "parserHFS_conf_fixed c")
   apply(rename_tac x xa y w')(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa y w' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. (parserHFS_conf_fixed c) = w' @ [x']")
   apply(rename_tac x xa y w' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac x xa y w' a list)(*strict*)
  apply(thin_tac " (parserHFS_conf_fixed c)=a#list")
  apply(clarsimp)
  apply(rename_tac x xa y w' w'a x')(*strict*)
  apply(case_tac "length (rule_rpop e1) - length w'a")
   apply(rename_tac x xa y w' w'a x')(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa y w' w'a x' nat)(*strict*)
  apply(clarsimp)
  done

lemma parserHFS_inst_hlp_AX_is_forward_edge_deterministic_correspond_SB: "
  valid_parser G
  \<Longrightarrow> c \<in> parserHFS.get_accessible_configurations G
  \<Longrightarrow> parserHFS_step_relation G c e1 c1
  \<Longrightarrow> parserHFS_step_relation G c e2 c2
  \<Longrightarrow> parserHFS_conf_history c1 = parserHFS_conf_history c @ w1
  \<Longrightarrow> parserHFS_conf_history c2 = parserHFS_conf_history c @ w2
  \<Longrightarrow> c \<in> parserHFS_configurations G
  \<Longrightarrow> c1 \<in> parserHFS_configurations G
  \<Longrightarrow> c2 \<in> parserHFS_configurations G
  \<Longrightarrow> w1 \<noteq> w2
  \<Longrightarrow> w2 \<sqsubseteq> w1
  \<Longrightarrow> \<not> parserHFS_conf_fixed c2 \<sqsupseteq> [parser_bottom G]"
  apply(subgoal_tac "\<not> parserHFS_conf_fixed c \<sqsupseteq> [parser_bottom G]")
   prefer 2
   apply(rule parserHFS_history_modification_implies_extendable_before)
      apply(force)+
    apply(case_tac "w1")
     apply(simp add: prefix_def)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>x. rule_rpop e1 @ x = parserHFS_conf_scheduler c")
   prefer 2
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
  apply(subgoal_tac "\<exists>x. x\<noteq>[] \<and> w2 @ x = w1")
   prefer 2
   apply(simp add: prefix_def)
   apply(force)
  apply(subgoal_tac "prefix (rule_rpop e2) (rule_rpop e1)")
   prefer 2
   apply(rule_tac
      ?w1.0="w1"
      in parserHFS_strict_history_extension_implies_pop_extension)
              apply(force)+
  apply(subgoal_tac "\<exists>x. x\<noteq>[] \<and> rule_rpop e2 @ x = rule_rpop e1")
   prefer 2
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac ca x caa)(*strict*)
   apply(erule_tac
      x="caa"
      in allE)
   apply(clarsimp)
   apply(rename_tac ca x)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
  apply(subgoal_tac "\<exists>x. x\<noteq>[] \<and> rule_rpop e2 @ x = parserHFS_conf_scheduler c")
   prefer 2
   apply(clarsimp)
   apply(rename_tac x xa xb)(*strict*)
   apply(erule_tac
      x="xb@x"
      in allE)
   apply(clarsimp)
   apply (metis concat_asso parserHFS_get_scheduler_def)
  apply(rule parserHFS_extendable_if_extendable_and_no_parser_bottom_reading_step)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x xa xb xc)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac x xa xb xc ca)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e1")
   apply(rename_tac x xa xb xc ca)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac x xa xb xc ca k w xe)(*strict*)
   apply(case_tac xb)
    apply(rename_tac x xa xb xc ca k w xe)(*strict*)
    apply(force)
   apply(rename_tac x xa xb xc ca k w xe a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
    apply(rename_tac x xa xb xc ca k w xe a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac x xa xb xc ca k w xe a list)(*strict*)
   apply(thin_tac "xb=a#list")
   apply(clarsimp)
   apply(rename_tac x xa xc ca k w xe w' x')(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac x xa xc ca k w xe w' x')(*strict*)
    apply(clarsimp)
    apply (metis ConsApp append_assoc in_set_takeD kPrefix_def not_in_diff set_append2 set_append_contra1 set_subset_in)
   apply(rename_tac x xa xc ca k w xe w' x' nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac x xa xb xc ca)(*strict*)
  apply(simp add: valid_parser_def parserHFS_step_relation_def)
  done

lemma parserHFS_inst_AX_is_forward_target_deterministic_correspond_SB: "
  \<forall>G. valid_parser G \<longrightarrow>
        ATS.is_forward_target_deterministic_accessible
         parserHFS_initial_configurations parserHFS_step_relation G =
        ATS_determHIST_SB.is_forward_target_deterministicHist_SB_long
         parserHFS_initial_configurations parserHFS_step_relation
         parser_markers (@) (@) parserHFS_conf_history
         parser_fixed_scheduler_extendable parserHFS_conf_fixed G"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rule parserHFS.is_forward_target_deterministic_accessible_implies_is_forward_target_deterministicHist_SB_long)
    apply(rename_tac G)(*strict*)
    apply(force)
   apply(rename_tac G)(*strict*)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(simp add: parserHFS.is_forward_target_deterministicHist_SB_long_def)
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
  apply(erule impE)
   apply(rename_tac G c c1 c2 e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(clarsimp)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e x xa y ya)(*strict*)
  apply(simp add: parser_markers_def)
  apply(rule_tac
      B="set (rule_rpop e)"
      in subset_trans)
   apply(rename_tac G c c1 c2 e x xa y ya)(*strict*)
   apply (metis set_butlast_if_match_is_subset set_drop_subset subset_trans)
  apply(rename_tac G c c1 c2 e x xa y ya)(*strict*)
  apply(rule PARSER_rule_rpop_in_parser_events)
   apply(rename_tac G c c1 c2 e x xa y ya)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e x xa y ya)(*strict*)
  apply(force)
  done

lemma parserHFS_inst_ATS_HistoryCT_SB_axioms: "
  ATS_HistoryCT_SB_axioms valid_parser parserHFS_initial_configurations parserHFS_step_relation parser_markers (@) (@) parserHFS_conf_history parser_fixed_scheduler_extendable parserHFS_conf_fixed "
  apply(simp add: ATS_HistoryCT_SB_axioms_def)
  apply(simp add: parserHFS_inst_AX_is_forward_target_deterministic_correspond_SB )
  done

lemma parserHFS_inst_AX_is_forward_edge_deterministic_correspond_SB: "
  \<forall>G. valid_parser G \<longrightarrow>
        ATS.is_forward_edge_deterministic_accessible
         parserHFS_initial_configurations parserHFS_step_relation G =
        ATS_determHIST_SB.is_forward_edge_deterministicHist_SB_long
         parserHFS_initial_configurations parserHFS_step_relation
         parser_markers (@) (@) parserHFS_conf_history
         parser_fixed_scheduler_extendable parserHFS_conf_fixed G"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserHFS.is_forward_edge_deterministic_accessible_def)
  apply(simp add: parserHFS.is_forward_edge_deterministicHist_SB_long_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e1 e2)(*strict*)
  apply(erule_tac
      x="c"
      in ballE)
   apply(rename_tac G c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2)(*strict*)
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
  apply(erule impE)
   apply(rename_tac G c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w1. parserHFS_conf_history c1 = parserHFS_conf_history c @ w1")
   apply(rename_tac G c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply (metis (full_types) parserHFS.AX_steps_extend_history parserHFS.get_accessible_configurations_are_configurations subsetD)
  apply(rename_tac G c c1 c2 e1 e2)(*strict*)
  apply(subgoal_tac "\<exists>w2. parserHFS_conf_history c2 = parserHFS_conf_history c @ w2")
   apply(rename_tac G c c1 c2 e1 e2)(*strict*)
   prefer 2
   apply (metis (full_types) parserHFS.AX_steps_extend_history parserHFS.get_accessible_configurations_are_configurations subsetD)
  apply(rename_tac G c c1 c2 e1 e2)(*strict*)
  apply(erule exE)+
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule_tac
      x="w1"
      in exI)
  apply(rule conjI)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(subgoal_tac "c1 \<in> parserHFS_configurations G")
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    prefer 2
    apply (metis (mono_tags) contra_subsetD parserHFS.AX_step_relation_preserves_belongsC parserHFS.get_accessible_configurations_are_configurations)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(simp add: parserHFS_configurations_def parser_markers_def prefix_def)
   apply(clarsimp)
   apply(rename_tac G c c2 e1 e2 w1 w2 x f l ca w)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule_tac
      x="w2"
      in exI)
  apply(rule conjI)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(subgoal_tac "c2 \<in> parserHFS_configurations G")
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    prefer 2
    apply (metis (mono_tags) contra_subsetD parserHFS.AX_step_relation_preserves_belongsC parserHFS.get_accessible_configurations_are_configurations)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(simp add: parserHFS_configurations_def parser_markers_def prefix_def)
   apply(clarsimp)
   apply(rename_tac G c c1 e1 e2 w1 w2 x f l ca w)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes parser_markers (@) G w2 = ATS_History.history_fragment_prefixes parser_markers (@) G w1"
      and s="ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w1 \<and> ATS_History.history_fragment_prefixes parser_markers (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w2"
      in ssubst)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(subgoal_tac "c \<in> parserHFS_configurations G")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   prefer 2
   apply (metis (full_types) parserHFS.get_accessible_configurations_are_configurations subsetD)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(subgoal_tac "c1 \<in> parserHFS_configurations G")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   prefer 2
   apply (metis parserHFS_inst_AX_step_relation_preserves_belongs)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(subgoal_tac "c2 \<in> parserHFS_configurations G")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   prefer 2
   apply (metis parserHFS_inst_AX_step_relation_preserves_belongs)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes parser_markers (@) G w1 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w2"
      and s="prefix w1 w2"
      in ssubst)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(rule order_antisym)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(clarsimp)
    apply(simp add: prefix_def)
    apply(subgoal_tac "w1 \<in> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}")
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(rule_tac
      A="{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}"
      in set_mp)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(thin_tac "{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1} \<subseteq> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}")
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(clarsimp)
    apply(simp add: parser_markers_def)
    apply(rule_tac
      B="set (parserHFS_conf_history c1)"
      in subset_trans)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(rule_tac
      B="parser_events G - {parser_bottom G}"
      in subset_trans)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(rule parserHFS_history_in_parser_events_no_bottom)
      apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
      apply(force)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G c c1 c2 e1 e2 w2 x hf'')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
   apply(simp add: parser_markers_def)
   apply(rule_tac
      B="set (parserHFS_conf_history c2)"
      in subset_trans)
    apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
   apply(rule_tac
      B="parser_events G - {parser_bottom G}"
      in subset_trans)
    apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
    apply(rule parserHFS_history_in_parser_events_no_bottom)
     apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule_tac
      t="ATS_History.history_fragment_prefixes parser_markers (@) G w2 \<subseteq> ATS_History.history_fragment_prefixes parser_markers (@) G w1"
      and s="prefix w2 w1"
      in ssubst)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(simp add: parserHFS.history_fragment_prefixes_def)
   apply(rule order_antisym)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(clarsimp)
    apply(simp add: prefix_def)
    apply(subgoal_tac "w2 \<in> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}")
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(rule_tac
      A="{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2}"
      in set_mp)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(thin_tac "{hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w2} \<subseteq> {hf' \<in> parser_markers G. \<exists>hf''\<in> parser_markers G. hf' @ hf'' = w1}")
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(clarsimp)
    apply(simp add: parser_markers_def)
    apply(rule_tac
      B="set (parserHFS_conf_history c2)"
      in subset_trans)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(rule_tac
      B="parser_events G - {parser_bottom G}"
      in subset_trans)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(rule parserHFS_history_in_parser_events_no_bottom)
      apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
      apply(force)
     apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac G c c1 c2 e1 e2 w1 x hf'')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
   apply(simp add: parser_markers_def)
   apply(rule_tac
      B="set (parserHFS_conf_history c1)"
      in subset_trans)
    apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
   apply(rule_tac
      B="parser_events G - {parser_bottom G}"
      in subset_trans)
    apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
    apply(rule parserHFS_history_in_parser_events_no_bottom)
     apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
     apply(force)
    apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 x hf'' ca)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule_tac
      t="w2 \<sqsubseteq> w1 \<and> w1 \<sqsubseteq> w2"
      and s="w1=w2"
      in ssubst)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(case_tac "w1=w2")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(subgoal_tac "w2 \<sqsubseteq> w1 \<or> w1 \<sqsubseteq> w2")
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      ?c2.0="c2"
      and ?c1.0="c1"
      in parserHFS_mutual_history_extension)
          apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
          apply(force)+
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(erule disjE)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(rule conjI)
    apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
    apply(force)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(rule parserHFS_inst_hlp_AX_is_forward_edge_deterministic_correspond_SB)
             apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
             apply(force)+
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule disjI1)
  apply(rule conjI)
   apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
   apply(force)
  apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
  apply(rule_tac
      ?c1.0="c2"
      in parserHFS_inst_hlp_AX_is_forward_edge_deterministic_correspond_SB)
            apply(rename_tac G c c1 c2 e1 e2 w1 w2)(*strict*)
            apply(force)+
  done

lemma parserHFS_inst_ATS_HistoryCE_SB_axioms: "
  ATS_HistoryCE_SB_axioms valid_parser parserHFS_initial_configurations
     parserHFS_step_relation parser_markers (@) (@) parserHFS_conf_history
     parser_fixed_scheduler_extendable parserHFS_conf_fixed "
  apply(simp add: ATS_HistoryCE_SB_axioms_def)
  apply(simp add: parserHFS_inst_AX_is_forward_edge_deterministic_correspond_SB )
  done

lemma parserHFS_inst_ATS_HistoryCE_DB_axioms: "
  ATS_HistoryCE_DB_axioms valid_parser parserHFS_initial_configurations
     parserHFS_step_relation parser_markers (@) (@) parserHFS_conf_history
     parser_fixed_scheduler_extendable parserHFS_get_fixed_scheduler_DB"
  apply(simp add: ATS_HistoryCE_DB_axioms_def)
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule_tac
      t="ATS_determHIST_DB.is_forward_edge_deterministicHist_DB_long parserHFS_initial_configurations parserHFS_step_relation parser_markers (@) (@) parserHFS_conf_history parser_fixed_scheduler_extendable parserHFS_get_fixed_scheduler_DB G"
      and s="ATS_determHIST_SB.is_forward_edge_deterministicHist_SB_long parserHFS_initial_configurations parserHFS_step_relation parser_markers (@) (@) parserHFS_conf_history parser_fixed_scheduler_extendable parserHFS_conf_fixed G"
      in ssubst)
   apply(rename_tac G)(*strict*)
   prefer 2
   apply(metis parserHFS_inst_AX_is_forward_edge_deterministic_correspond_SB)
  apply(rename_tac G)(*strict*)
  apply (metis parserHFS.AX_is_forward_edge_deterministic_correspond_DB_SB)
  done

interpretation "parserHFS" : loc_autHFS_8
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHFS_inst_ATS_axioms parserHFS_inst_ATS_History_axioms parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms parserHFS_inst_ATS_String_State_Modification_axioms parserHFS_inst_ATS_Sched_SB_axioms parserHFS_inst_ATS_SchedF_SB_axioms parserHFS_inst_ATS_SchedUF_SB_axioms parserHFS_inst_ATS_Sched_DB0_axioms parserHFS_inst_ATS_SchedF_DB_axioms parserHFS_inst_ATS_SchedUF_DB_axioms parserHFS_inst_ATS_Sched_DB_axioms parserHFS_inst_ATS_SchedF_SDB_axioms parserHFS_inst_ATS_SchedUF_SDB_axioms parserHFS_inst_ATS_Sched_SDB_axioms parserHFS_inst_ATS_determHIST_SB_axioms parserHFS_inst_ATS_Sched_axioms parserHFS_inst_ATS_HistoryCT_SB_axioms parserHFS_inst_ATS_HistoryCE_SB_axioms parserHFS_inst_ATS_HistoryCE_DB_axioms )
  done

lemma parserHFS_inst_AX_is_forward_target_deterministic_correspond_DB: "
  \<forall>G. valid_parser G \<longrightarrow> parserHFS.is_forward_target_deterministic_accessible G = ATS_determHIST_DB.is_forward_target_deterministicHist_DB_long parserHFS_initial_configurations parserHFS_step_relation parser_markers (@) (@) parserHFS_conf_history parser_fixed_scheduler_extendable parserHFS_get_fixed_scheduler_DB G"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS.is_forward_target_deterministicHist_DB_long_def)
   apply(clarsimp)
   apply(rename_tac G c d n c1 c2 e w1 w2)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
   apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserHFS.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac G c c1 c2 e)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  done

lemma parserHFS_inst_ATS_HistoryCT_DB_axioms: "
  ATS_HistoryCT_DB_axioms valid_parser parserHFS_initial_configurations parserHFS_step_relation parser_markers (@) (@) parserHFS_conf_history parser_fixed_scheduler_extendable parserHFS_get_fixed_scheduler_DB "
  apply(simp add: ATS_HistoryCT_DB_axioms_def)
  apply(simp add: parserHFS_inst_AX_is_forward_target_deterministic_correspond_DB )
  done

interpretation "parserHFS" : loc_autHFS_9
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
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserHFS_inst_AX_initial_configuration_belongs parserHFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserHFS_inst_ATS_axioms parserHFS_inst_ATS_History_axioms parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms parserHFS_inst_ATS_String_State_Modification_axioms parserHFS_inst_ATS_Sched_SB_axioms parserHFS_inst_ATS_SchedF_SB_axioms parserHFS_inst_ATS_SchedUF_SB_axioms parserHFS_inst_ATS_Sched_DB0_axioms parserHFS_inst_ATS_SchedF_DB_axioms parserHFS_inst_ATS_SchedUF_DB_axioms parserHFS_inst_ATS_Sched_DB_axioms parserHFS_inst_ATS_SchedF_SDB_axioms parserHFS_inst_ATS_SchedUF_SDB_axioms parserHFS_inst_ATS_Sched_SDB_axioms parserHFS_inst_ATS_determHIST_SB_axioms parserHFS_inst_ATS_HistoryCT_SB_axioms parserHFS_inst_ATS_HistoryCE_SB_axioms parserHFS_inst_ATS_HistoryCT_DB_axioms parserHFS_inst_ATS_Sched_axioms )
  done

lemma parserHFS_unique_step: "
  valid_parser G
  \<Longrightarrow> \<exists>c2. parserHFS_step_relation G c1 e c2
  \<Longrightarrow> \<exists>!c2. parserHFS_step_relation G c1 e c2"
  apply(rule ex_ex1I)
   apply(force)
  apply(rename_tac c2 y)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  done

theorem parserHFS_is_forward_target_deterministic_accessible: "
  valid_parser G
  \<Longrightarrow> parserHFS.is_forward_target_deterministic_accessible G"
  apply(simp add: parserHFS.is_forward_target_deterministic_accessible_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e)(*strict*)
  apply(simp add: parserHFS_step_relation_def)
  apply(clarsimp)
  done

lemmas parserHFS_interpretations0 =
  parser_interpretations
  parserHFS_inst_AX_initial_configuration_belongs
  parserHFS_inst_AX_step_relation_preserves_belongs
  parserHFS_inst_ATS_axioms
  parserHFS_inst_ATS_History_axioms
  parserHFS_inst_ATS_Language_by_Finite_Derivations_axioms
  parserHFS_inst_ATS_String_State_Modification_axioms
  parserHFS_inst_ATS_Sched_SB_axioms
  parserHFS_inst_ATS_SchedF_SB_axioms
  parserHFS_inst_ATS_SchedUF_SB_axioms
  parserHFS_inst_ATS_Sched_DB0_axioms
  parserHFS_inst_ATS_SchedF_DB_axioms
  parserHFS_inst_ATS_SchedUF_DB_axioms
  parserHFS_inst_ATS_Sched_DB_axioms
  parserHFS_inst_ATS_SchedF_SDB_axioms
  parserHFS_inst_ATS_SchedUF_SDB_axioms
  parserHFS_inst_ATS_Sched_SDB_axioms
  parserHFS_inst_ATS_determHIST_SB_axioms
  parserHFS_inst_ATS_HistoryCT_SB_axioms
  parserHFS_inst_ATS_HistoryCE_SB_axioms
  parserHFS_inst_ATS_HistoryCT_DB_axioms
  parserHFS_inst_ATS_Sched_axioms

end
