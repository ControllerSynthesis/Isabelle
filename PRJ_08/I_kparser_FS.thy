section {*I\_kparser\_FS*}
theory
  I_kparser_FS

imports
  I_kparser_base

begin

record ('stack, 'event) parserFS_conf =
  parserFS_conf_fixed :: "'event list"
  parserFS_conf_stack :: "'stack list"
  parserFS_conf_scheduler :: "'event list"

definition parserFS_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserFS_conf set"
  where
    "parserFS_configurations G \<equiv>
  {\<lparr>parserFS_conf_fixed = f,
    parserFS_conf_stack = l,
    parserFS_conf_scheduler = r\<rparr>
  | f l r.
  set l \<subseteq> parser_nonterms G
  \<and> f \<in> parser_fixed_schedulers G
  \<and> r \<in> parser_unfixed_schedulers G
  \<and> f @ r \<in> parser_schedulers G}"

definition parserFS_step_relation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserFS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserFS_conf
  \<Rightarrow> bool"
  where
    "parserFS_step_relation G c1 p c2 \<equiv>
  p \<in> parser_rules G
  \<and> ((\<exists>x. parserFS_conf_stack c1=x@(rule_lpop p) \<and> parserFS_conf_stack c2=x@(rule_lpush p))
  \<and> (\<exists>v. rule_rpop p=v@rule_rpush p \<and>
  ((\<exists>popnew. parserFS_conf_fixed c1 @ popnew = rule_rpop p
  \<and> parserFS_conf_scheduler c1=popnew@parserFS_conf_scheduler c2
  \<and> parserFS_conf_fixed c2 = rule_rpush p)
  \<or>
  (\<exists>remainder. rule_rpop p @ remainder = parserFS_conf_fixed c1
  \<and> parserFS_conf_scheduler c1=parserFS_conf_scheduler c2
  \<and> parserFS_conf_fixed c2 = rule_rpush p@remainder)
  )))"

definition parserFS_step_relation_ALT :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserFS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserFS_conf
  \<Rightarrow> bool"
  where
    "parserFS_step_relation_ALT G c1 e c2 \<equiv>
  e \<in> parser_rules G
  \<and> (\<exists>x. parserFS_conf_stack c1 = x @ rule_lpop e
            \<and> parserFS_conf_stack c2 = x @ rule_lpush e)
  \<and> (\<exists>v. rule_rpop e = v @ rule_rpush e)
  \<and> ((\<exists>popnew.
        parserFS_conf_fixed c1 @ popnew = rule_rpop e
        \<and> parserFS_conf_scheduler c1 = popnew @ parserFS_conf_scheduler c2
        \<and> parserFS_conf_fixed c2 = rule_rpush e)
     \<or> (\<exists>remainder.
          rule_rpop e @ remainder = parserFS_conf_fixed c1
          \<and> parserFS_conf_scheduler c1=parserFS_conf_scheduler c2
          \<and> parserFS_conf_fixed c2 = rule_rpush e @ remainder)
  )"

lemma parserFS_step_relation_ALT_vs_parserFS_step_relation: "
  parserFS_step_relation_ALT G c1 p c2 = parserFS_step_relation G c1 p c2"
  apply(simp add: parserFS_step_relation_ALT_def parserFS_step_relation_def)
  done

definition parserFS_step_relation_ALT2 :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserFS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserFS_conf
  \<Rightarrow> bool"
  where
    "parserFS_step_relation_ALT2 G c1 e c2 \<equiv>
  e \<in> parser_rules G
  \<and> (\<exists>x. parserFS_conf_stack c1 = x @ rule_lpop e
            \<and> parserFS_conf_stack c2 = x @ rule_lpush e)
  \<and> ((\<exists>popnew.
        parserFS_conf_fixed c1 @ popnew = rule_rpop e
        \<and> parserFS_conf_scheduler c1 = popnew @ parserFS_conf_scheduler c2
        \<and> parserFS_conf_fixed c2 = rule_rpush e)
     \<or> (\<exists>remainder.
          parserFS_conf_fixed c1 = rule_rpop e @ remainder
          \<and> parserFS_conf_scheduler c1 = parserFS_conf_scheduler c2
          \<and> parserFS_conf_fixed c2 = rule_rpush e @ remainder)
  )"

lemma parserFS_step_relation_ALT2_vs_parserFS_step_relation_ALT: "
  valid_parser G
  \<Longrightarrow> parserFS_step_relation_ALT2 G c1 p c2 = parserFS_step_relation_ALT G c1 p c2"
  apply(simp add: parserFS_step_relation_ALT_def parserFS_step_relation_ALT2_def)
  apply(rule order_antisym)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="p"
      in ballE)+
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac x k xa)(*strict*)
  apply(rule conjI)
   apply(rename_tac x k xa)(*strict*)
   apply(rule_tac
      x="xa"
      in exI)
   apply(force)
  apply(rename_tac x k xa)(*strict*)
  apply(force)
  done

definition parserFS_step_relation_HFS_STYLE :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserFS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserFS_conf
  \<Rightarrow> bool"
  where
    "parserFS_step_relation_HFS_STYLE G c1 e c2 \<equiv>
  e \<in> parser_rules G
  \<and> (\<exists>x. parserFS_conf_stack c1 = x @ rule_lpop e
            \<and> parserFS_conf_stack c2 = x @ rule_lpush e)
  \<and> (\<exists>x. parserFS_conf_scheduler c1 = rule_rpop e @ x
         \<and> parserFS_conf_scheduler c2 = rule_rpush e @ x)
  \<and> parserFS_conf_fixed c2
      = rule_rpush e
        @ drop
            (length (rule_rpop e))
            (parserFS_conf_fixed c1)"

definition parserFS_initial_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserFS_conf set"
  where
    "parserFS_initial_configurations G \<equiv>
  {c. parserFS_conf_fixed c = []
      \<and> parserFS_conf_stack c = [parser_initial G]}
  \<inter> parserFS_configurations G"

definition parserFS_marking_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserFS_conf set"
  where
    "parserFS_marking_configurations G \<equiv>
  {c. \<exists>f \<in> parser_marking G. \<exists>w.
      parserFS_conf_stack c = w @ [f]
      \<and> parserFS_conf_fixed c @ parserFS_conf_scheduler c
          = [parser_bottom G]}
  \<inter> parserFS_configurations G"

definition parserFS_marking_condition :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf)derivation
  \<Rightarrow> bool"
  where
    "parserFS_marking_condition G d \<equiv>
  (\<exists>c.
    d 0 =Some (pair None c)
    \<and> c \<in> parserFS_configurations G)
  \<and> (\<exists>i e c.
      d i = Some (pair e c)
      \<and> c \<in> parserFS_marking_configurations G)"

definition parserFS_marked_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf)derivation
  \<Rightarrow> 'event list set"
  where
    "parserFS_marked_effect G d \<equiv>
  {w. \<exists>c.
      d 0 = Some (pair None c)
      \<and> w = butlast (parserFS_conf_scheduler c)}"

definition parserFS_unmarked_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf)derivation
  \<Rightarrow> 'event list set"
  where
    "parserFS_unmarked_effect G d \<equiv>
  {w. \<exists>c c' i e v.
      d 0 = Some (pair None c)
      \<and> d i = Some (pair e c')
      \<and> v @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'
          = parserFS_conf_scheduler c
      \<and> w = butlast_if_match
              (v @ parserFS_conf_fixed c')
              (parser_bottom G)}"

definition parserFS_get_destinations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf)derivation_configuration
  \<Rightarrow> ('stack, 'event) parser_destinations set"
  where
    "parserFS_get_destinations G e \<equiv>
  case e of pair e c \<Rightarrow>
    state ` set (parserFS_conf_stack c)
    \<union> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {rule e'})"

definition parserFS_string_state :: "
  ('stack, 'event) parserFS_conf
  \<Rightarrow> 'event list"
  where
    "parserFS_string_state c \<equiv>
  parserFS_conf_fixed c @ parserFS_conf_scheduler c"

lemma parserFS_inst_AX_initial_configuration_belongs: "
  (\<forall>G. valid_parser G \<longrightarrow> parserFS_initial_configurations G \<subseteq> parserFS_configurations G)"
  apply(clarsimp)
  apply(rename_tac G x)(*strict*)
  apply(simp add: parserFS_initial_configurations_def)
  done

lemma parserFS_inst_AX_step_relation_preserves_belongs: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1 e c2. parserFS_step_relation G c1 e c2 \<longrightarrow> c1 \<in> parserFS_configurations G \<longrightarrow> e \<in> parser_step_labels G \<and> c2 \<in> parserFS_configurations G))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(simp add: parser_step_labels_def parserFS_step_relation_def)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G e c2 f l r)(*strict*)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G e c2 f r x v)(*strict*)
  apply(simp add: parser_step_labels_def)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G e c2 f r x v)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac G e c2 f r x v)(*strict*)
  apply(erule disjE)
   apply(rename_tac G e c2 f r x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e c2 f x v popnew)(*strict*)
   apply(case_tac c2)
   apply(rename_tac G e c2 f x v popnew parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e f x v popnew parserFS_conf_scheduler)(*strict*)
   apply(rule conjI)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac G e f x v popnew parserFS_conf_scheduler)(*strict*)
   apply(rule conjI)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler)(*strict*)
    apply(simp add: parser_fixed_schedulers_def)
    apply(simp add: prefix_closure_def prefix_def parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      x="rule_rpush e @ [parser_bottom G]"
      in exI)
     apply(rule conjI)
      apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<in> set w")
      apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w)(*strict*)
      apply(force)
     apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w)(*strict*)
     apply (metis elem_set_app in_set_takeD)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w nat xa)(*strict*)
    apply(rule_tac
      x="rule_rpush e"
      in exI)
    apply(clarsimp)
    apply(rule_tac
      x="xa"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "set xa \<subseteq> set w")
     apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w nat xa)(*strict*)
     apply(rule conjI)
      apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w nat xa)(*strict*)
      apply (metis butlast_snoc subset_trans trivButLast)
     apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w nat xa)(*strict*)
     apply (metis nset_diff subset_trans)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w nat xa)(*strict*)
    apply(rule_tac
      t="w"
      and s="v@xa"
      in ssubst)
     apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w nat xa)(*strict*)
     apply(rule_tac
      v="[parser_bottom G]"
      in append_injr)
     apply (metis concat_asso)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c k w nat xa)(*strict*)
    apply(force)
   apply(rename_tac G e f x v popnew parserFS_conf_scheduler)(*strict*)
   apply(rule conjI)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler)(*strict*)
    apply(simp add: parser_unfixed_schedulers_def)
    apply(simp add: suffix_closure_def parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc)(*strict*)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c)(*strict*)
    apply(rule_tac
      x="vb @ [parser_bottom G]"
      in exI)
    apply(rule conjI)
     apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c)(*strict*)
     prefer 2
     apply(rule_tac
      x="f@popnew"
      in exI)
     apply(rule sym)
     apply(rule_tac
      t="vb @ [parser_bottom G]"
      and s="f @ popnew @ parserFS_conf_scheduler"
      in ssubst)
      apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c)(*strict*)
      apply(force)
     apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler vb vc c)(*strict*)
    apply(force)
   apply(rename_tac G e f x v popnew parserFS_conf_scheduler)(*strict*)
   apply(simp add: parser_schedulers_def)
   apply(clarsimp)
   apply(rename_tac G e f x v popnew parserFS_conf_scheduler va)(*strict*)
   apply(case_tac "parserFS_conf_scheduler")
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler va)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f x v popnew va)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac G e f x v popnew va k w xb xc)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac G e f x v popnew va k w xb xc)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<in> set w")
      apply(rename_tac G e f x v popnew va k w xb xc)(*strict*)
      apply(force)
     apply(rename_tac G e f x v popnew va k w xb xc)(*strict*)
     apply (metis kPrefix_def take_reflects_mem)
    apply(rename_tac G e f x v popnew va k w xb xc nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e f x v popnew k w xb xc nat)(*strict*)
    apply(rule_tac
      x="xc"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "set xc \<subseteq> set w")
     apply(rename_tac G e f x v popnew k w xb xc nat)(*strict*)
     apply(force)
    apply(rename_tac G e f x v popnew k w xb xc nat)(*strict*)
    apply (metis butlast_snoc_2 set_append2 snoc_eq_iff_butlast)
   apply(rename_tac G e f x v popnew parserFS_conf_scheduler va a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. parserFS_conf_scheduler = w' @ [x']")
    apply(rename_tac G e f x v popnew parserFS_conf_scheduler va a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e f x v popnew parserFS_conf_scheduler va a list)(*strict*)
   apply(thin_tac "parserFS_conf_scheduler = a # list")
   apply(clarsimp)
   apply(rename_tac G e f x v popnew w')(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G e f x v popnew w' k w)(*strict*)
   apply(simp add: kPrefix_def)
   apply(case_tac "k-length w")
    apply(rename_tac G e f x v popnew w' k w)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_bottom G \<in> set w")
     apply(rename_tac G e f x v popnew w' k w)(*strict*)
     apply(force)
    apply(rename_tac G e f x v popnew w' k w)(*strict*)
    apply (metis nset_mp set_append2 set_take_subset)
   apply(rename_tac G e f x v popnew w' k w nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e f x v popnew w' k w nat xa)(*strict*)
   apply(case_tac "popnew")
    apply(rename_tac G e f x v popnew w' k w nat xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G e f x v popnew w' k w nat xa a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. popnew = w' @ [x']")
    apply(rename_tac G e f x v popnew w' k w nat xa a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e f x v popnew w' k w nat xa a list)(*strict*)
   apply(thin_tac "popnew = a # list")
   apply(clarsimp)
  apply(rename_tac G e c2 f r x v)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e c2 x v remainder)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G e c2 x v remainder parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e x v remainder parserFS_conf_scheduler)(*strict*)
  apply(rule conjI)
   apply(rename_tac G e x v remainder parserFS_conf_scheduler)(*strict*)
   apply(simp add: valid_parser_step_label_def)
  apply(rename_tac G e x v remainder parserFS_conf_scheduler)(*strict*)
  apply(simp add: parser_fixed_schedulers_def)
  apply(simp add: prefix_closure_def prefix_def parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc c)(*strict*)
  apply(case_tac c)
   apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc)(*strict*)
   apply(case_tac "remainder")
    apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x v parserFS_conf_scheduler vb vc)(*strict*)
    apply(case_tac "rule_rpush e")
     apply(rename_tac G e x v parserFS_conf_scheduler vb vc)(*strict*)
     apply(clarsimp)
     apply(rename_tac G e x parserFS_conf_scheduler vb vc)(*strict*)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac G e x v parserFS_conf_scheduler vb vc a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
     apply(rename_tac G e x v parserFS_conf_scheduler vb vc a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x v parserFS_conf_scheduler vb vc a list)(*strict*)
    apply(thin_tac "rule_rpush e = a # list")
    apply(clarsimp)
    apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
    apply(subgoal_tac "parserFS_conf_scheduler=[]")
     apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
     prefer 2
     apply(case_tac parserFS_conf_scheduler)
      apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
      apply(clarsimp)
     apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. parserFS_conf_scheduler = w' @ [x']")
      apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
     apply(thin_tac "parserFS_conf_scheduler = a # list")
     apply(clarsimp)
    apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x v w')(*strict*)
    apply(rule_tac
      x="w' @ [parser_bottom G]"
      in exI)
    apply(force)
   apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. remainder= w' @ [x']")
    apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc a list)(*strict*)
   apply(thin_tac "remainder = a # list")
   apply(clarsimp)
   apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
   apply(subgoal_tac "parserFS_conf_scheduler=[]")
    apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
    prefer 2
    apply(case_tac parserFS_conf_scheduler)
     apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
     apply(clarsimp)
    apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. parserFS_conf_scheduler = w' @ [x']")
     apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
    apply(thin_tac "parserFS_conf_scheduler = a # list")
    apply(clarsimp)
   apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
   apply(clarsimp)
   apply(rename_tac G e x v w')(*strict*)
   apply(rule_tac
      x="rule_rpush e @ w' @ [parser_bottom G]"
      in exI)
   apply(force)
  apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc c a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. c= w' @ [x']")
   apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc c a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e x v remainder parserFS_conf_scheduler vb vc c a list)(*strict*)
  apply(thin_tac "c = a # list")
  apply(clarsimp)
  apply(rename_tac G e x v remainder parserFS_conf_scheduler vb w')(*strict*)
  apply(case_tac "remainder")
   apply(rename_tac G e x v remainder parserFS_conf_scheduler vb w')(*strict*)
   apply(clarsimp)
   apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
   apply(rule conjI)
    apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
    apply(rule_tac
      x="rule_rpush e@[parser_bottom G]"
      in exI)
    apply(force)
   apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
   apply(case_tac "parserFS_conf_scheduler")
    apply(rename_tac G e x v parserFS_conf_scheduler vb w')(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x v vb w')(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac G e x v vb w' k w xb xc)(*strict*)
    apply(subgoal_tac "parser_bottom G \<in> set (rule_rpush e)")
     apply(rename_tac G e x v vb w' k w xb xc)(*strict*)
     apply(force)
    apply(rename_tac G e x v vb w' k w xb xc)(*strict*)
    apply(rule_tac
      t="rule_rpush e"
      and s="xc @ [parser_bottom G]"
      in ssubst)
     apply(rename_tac G e x v vb w' k w xb xc)(*strict*)
     apply(force)
    apply(rename_tac G e x v vb w' k w xb xc)(*strict*)
    apply (metis Nil_is_append_conv last_in_set last_snoc not_Cons_self2)
   apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. parserFS_conf_scheduler= w' @ [x']")
    apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e x v parserFS_conf_scheduler vb w' a list)(*strict*)
   apply(thin_tac "parserFS_conf_scheduler = a # list")
   apply(clarsimp)
  apply(rename_tac G e x v remainder parserFS_conf_scheduler vb w' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. remainder= w' @ [x']")
   apply(rename_tac G e x v remainder parserFS_conf_scheduler vb w' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e x v remainder parserFS_conf_scheduler vb w' a list)(*strict*)
  apply(thin_tac "remainder = a # list")
  apply(clarsimp)
  apply(rename_tac G e x v parserFS_conf_scheduler vb w' w'a x')(*strict*)
  apply(rule conjI)
   apply(rename_tac G e x v parserFS_conf_scheduler vb w' w'a x')(*strict*)
   apply(rule_tac
      x="rule_rpush e @ w'a @ [x']@[parser_bottom G]"
      in exI)
   apply(force)
  apply(rename_tac G e x v parserFS_conf_scheduler vb w' w'a x')(*strict*)
  apply(case_tac "parserFS_conf_scheduler")
   apply(rename_tac G e x v parserFS_conf_scheduler vb w' w'a x')(*strict*)
   apply(clarsimp)
  apply(rename_tac G e x v parserFS_conf_scheduler vb w' w'a x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. parserFS_conf_scheduler= w' @ [x']")
   apply(rename_tac G e x v parserFS_conf_scheduler vb w' w'a x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e x v parserFS_conf_scheduler vb w' w'a x' a list)(*strict*)
  apply(thin_tac "parserFS_conf_scheduler = a # list")
  apply(clarsimp)
  done

interpretation "parserFS" : loc_autFS_0
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserFS_configurations"
  (* initial_configurations *)
  "parserFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserFS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserFS_marking_condition"
  (* marked_effect *)
  "parserFS_marked_effect"
  (* unmarked_effect *)
  "parserFS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserFS_get_destinations"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserFS_inst_AX_initial_configuration_belongs parserFS_inst_AX_step_relation_preserves_belongs )
  done

lemma parserFS_input_decreases: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation G d
  \<Longrightarrow> parserFS.belongs G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> d j = Some (pair e' c')
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> \<exists>w. parserFS_conf_scheduler c = w @ parserFS_conf_scheduler c'"
  apply(induct "j-i" arbitrary: i e c)
   apply(rename_tac i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac x i e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="j"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac x i e c)(*strict*)
     apply(force)
    apply(rename_tac x i e c)(*strict*)
    apply(force)
   apply(rename_tac x i e c)(*strict*)
   apply(force)
  apply(rename_tac x i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="Some e2"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler c = w @ parserFS_conf_scheduler c2")
   apply(rename_tac x i e c e2 c2 w)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2 w)(*strict*)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 w xa v)(*strict*)
  apply(erule disjE)
   apply(rename_tac x i e c e2 c2 w xa v)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e c e2 c2 w xa v)(*strict*)
  apply(clarsimp)
  done

lemma parserFS_input_with_fixed_decreases: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation G d
  \<Longrightarrow> parserFS.belongs G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> d j = Some (pair e' c')
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> \<exists>w. parserFS_conf_fixed c @ parserFS_conf_scheduler c = w @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'"
  apply(induct "j-i" arbitrary: i e c)
   apply(rename_tac i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac x i e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="j"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac x i e c)(*strict*)
     apply(force)
    apply(rename_tac x i e c)(*strict*)
    apply(force)
   apply(rename_tac x i e c)(*strict*)
   apply(force)
  apply(rename_tac x i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="Some e2"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i e c e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_conf_fixed c @ parserFS_conf_scheduler c = w @ parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2")
   apply(rename_tac x i e c e2 c2 w)(*strict*)
   apply(force)
  apply(rename_tac x i e c e2 c2 w)(*strict*)
  apply(thin_tac "parserFS_conf_fixed c2 @ parserFS_conf_scheduler c2 = w @ parserFS_conf_fixed c' @ parserFS_conf_scheduler c'")
  apply(rename_tac x i e c e2 c2 w)(*strict*)
  apply(simp add: parserFS_step_relation_def)
  apply(rename_tac x i e c e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 xa v)(*strict*)
  apply(erule disjE)
   apply(rename_tac x i e c e2 c2 xa v)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i e c e2 c2 xa v)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i e c e2 c2 xa v remainder)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(force)
  done

lemma parserFS_inst_AX_effect_inclusion1: "
  (\<forall>M. valid_parser M \<longrightarrow>
         (\<forall>f. ATS.derivation_initial parserFS_initial_configurations
               parserFS_step_relation M f \<longrightarrow>
              parserFS_marking_condition M f \<longrightarrow>
              parserFS_marked_effect M f \<subseteq> parserFS_unmarked_effect M f))"
  apply(clarsimp)
  apply(rename_tac M f x)(*strict*)
  apply(simp add: parserFS_unmarked_effect_def parserFS_marked_effect_def parserFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac M f c i e cb)(*strict*)
  apply(rule_tac
      x="cb"
      in exI)
  apply(rule conjI)
   apply(rename_tac M f c i e cb)(*strict*)
   apply(force)
  apply(rename_tac M f c i e cb)(*strict*)
  apply(simp add: parserFS_marking_configurations_def parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac M f i e fa l r fb w fc ra)(*strict*)
  apply(subgoal_tac "fa=[]")
   apply(rename_tac M f i e fa l r fb w fc ra)(*strict*)
   prefer 2
   apply(simp add: parserFS.derivation_initial_def)
   apply(clarsimp)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac M f i e fa l r fb w fc ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac M f i e l r fb w fc ra)(*strict*)
  apply(subgoal_tac "\<exists>w. r=w @ ra")
   apply(rename_tac M f i e l r fb w fc ra)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>x. parserFS_conf_scheduler \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = l, parserFS_conf_scheduler = r\<rparr> = x @ parserFS_conf_scheduler \<lparr>parserFS_conf_fixed = fc, parserFS_conf_stack = w @ [fb], parserFS_conf_scheduler = ra\<rparr>")
    apply(rename_tac M f i e l r fb w fc ra)(*strict*)
    prefer 2
    apply(rule parserFS_input_decreases)
         apply(rename_tac M f i e l r fb w fc ra)(*strict*)
         apply(force)
        apply(rename_tac M f i e l r fb w fc ra)(*strict*)
        apply(rule parserFS.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac M f i e l r fb w fc ra)(*strict*)
       apply(rule parserFS.derivation_initial_belongs)
        apply(rename_tac M f i e l r fb w fc ra)(*strict*)
        apply(force)
       apply(rename_tac M f i e l r fb w fc ra)(*strict*)
       apply(force)
      apply(rename_tac M f i e l r fb w fc ra)(*strict*)
      apply(force)
     apply(rename_tac M f i e l r fb w fc ra)(*strict*)
     apply(force)
    apply(rename_tac M f i e l r fb w fc ra)(*strict*)
    apply(force)
   apply(rename_tac M f i e l r fb w fc ra)(*strict*)
   apply(clarsimp)
  apply(rename_tac M f i e l r fb w fc ra)(*strict*)
  apply(clarsimp)
  apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
  apply(subgoal_tac "\<exists>w. w@fc@ra=wa@ra")
   apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
   prefer 2
   apply(subgoal_tac "\<exists>x. parserFS_conf_fixed \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = l, parserFS_conf_scheduler = wa @ ra\<rparr> @ parserFS_conf_scheduler \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = l, parserFS_conf_scheduler = wa @ ra\<rparr> = x @ parserFS_conf_fixed \<lparr>parserFS_conf_fixed = fc, parserFS_conf_stack = w @ [fb], parserFS_conf_scheduler = ra\<rparr> @ parserFS_conf_scheduler \<lparr>parserFS_conf_fixed = fc, parserFS_conf_stack = w @ [fb], parserFS_conf_scheduler = ra\<rparr>")
    apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
    prefer 2
    apply(rule parserFS_input_with_fixed_decreases)
         apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
         apply(force)
        apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
        apply(rule parserFS.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
       apply(rule parserFS.derivation_initial_belongs)
        apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
        apply(force)
       apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
       apply(force)
      apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
      apply(force)
     apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
     apply(force)
    apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
    apply(force)
   apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
   apply(clarsimp)
  apply(rename_tac M f i e l fb w fc ra wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac M f i e l fb w fc ra wa wb)(*strict*)
  apply(case_tac ra)
   apply(rename_tac M f i e l fb w fc ra wa wb)(*strict*)
   apply(clarsimp)
   apply(rename_tac M f i e l fb w wb)(*strict*)
   apply (metis butlast_if_match_direct)
  apply(rename_tac M f i e l fb w fc ra wa wb a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ra = w' @ [x']")
   apply(rename_tac M f i e l fb w fc ra wa wb a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac M f i e l fb w fc ra wa wb a list)(*strict*)
  apply(thin_tac "ra = a # list")
  apply(clarsimp)
  apply(rename_tac M f i e l fb w wa)(*strict*)
  apply(simp add: parser_unfixed_schedulers_def parser_schedulers_def)
  apply(clarsimp)
  apply (metis butlast_if_match_direct2_prime)
  done

lemma parserFS_inst_lang_sound: "
  (\<forall>M. valid_parser M \<longrightarrow> parserFS.unmarked_language M \<subseteq> parser_markers M)"
  apply(clarsimp)
  apply(rename_tac M x)(*strict*)
  apply(simp add: parserFS.unmarked_language_def parserFS_unmarked_effect_def parser_markers_def)
  apply(clarsimp)
  apply(rename_tac M xa d c c' i v e)(*strict*)
  apply(subgoal_tac "c \<in> parserFS_configurations M")
   apply(rename_tac M xa d c c' i v e)(*strict*)
   apply(subgoal_tac "c' \<in> parserFS_configurations M")
    apply(rename_tac M xa d c c' i v e)(*strict*)
    apply(simp add: parserFS_configurations_def parser_unfixed_schedulers_def parser_schedulers_def suffix_closure_def suffix_def parser_fixed_schedulers_def prefix_closure_def prefix_def)
    apply(clarsimp)
    apply(rename_tac M xa d i v e f fa l la ra ve ca vg vh cb cc vj "cd")(*strict*)
    apply(rule_tac
      A="set (v@fa)"
      in set_mp)
     apply(rename_tac M xa d i v e f fa l la ra ve ca vg vh cb cc vj "cd")(*strict*)
     prefer 2
     apply (metis set_butlast_if_match_is_subset subsetD)
    apply(rename_tac M xa d i v e f fa l la ra ve ca vg vh cb cc vj "cd")(*strict*)
    apply(simp add: valid_parser_def)
    apply (metis append_Nil2 butlast_if_match_direct butlast_if_match_pull_out set_app_subset set_concat_subset set_subset_in2 subset_trans)
   apply(rename_tac M xa d c c' i v e)(*strict*)
   apply(rule parserFS.belongs_configurations)
    apply(rename_tac M xa d c c' i v e)(*strict*)
    apply(rule parserFS.derivation_initial_belongs)
     apply(rename_tac M xa d c c' i v e)(*strict*)
     apply(force)
    apply(rename_tac M xa d c c' i v e)(*strict*)
    apply(force)
   apply(rename_tac M xa d c c' i v e)(*strict*)
   apply(force)
  apply(rename_tac M xa d c c' i v e)(*strict*)
  apply(rule parserFS.belongs_configurations)
   apply(rename_tac M xa d c c' i v e)(*strict*)
   apply(rule parserFS.derivation_initial_belongs)
    apply(rename_tac M xa d c c' i v e)(*strict*)
    apply(force)
   apply(rename_tac M xa d c c' i v e)(*strict*)
   apply(force)
  apply(rename_tac M xa d c c' i v e)(*strict*)
  apply(force)
  done

lemma parserFS_inst_AX_marking_condition_implies_existence_of_effect: "
  (\<forall>M. valid_parser M \<longrightarrow>
         (\<forall>f. ATS.derivation_initial parserFS_initial_configurations
               parserFS_step_relation M f \<longrightarrow>
              parserFS_marking_condition M f \<longrightarrow>
              parserFS_marked_effect M f \<noteq> {}))"
  apply(simp add: parserFS_marking_condition_def parserFS_marked_effect_def)
  apply(clarsimp)
  done

lemma parserFS_inst_AX_unmarked_effect_persists: "
  (\<forall>G. valid_parser G \<longrightarrow>
         (\<forall>d. ATS.derivation_initial parserFS_initial_configurations
               parserFS_step_relation G d \<longrightarrow>
              (\<forall>n. parserFS_unmarked_effect G (derivation_take d n)
                   \<subseteq> parserFS_unmarked_effect G d)))"
  apply(clarsimp)
  apply(rename_tac G d n xa)(*strict*)
  apply(simp add: parserFS_unmarked_effect_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac G d n c c' i v e)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac G d n c c' i v e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G d n c c' i v e)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="c'"
      in exI)
  apply(rule conjI)
   apply(rename_tac G d n c c' i v e)(*strict*)
   apply(force)
  apply(rename_tac G d n c c' i v e)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(clarsimp)
  done

lemma parserFS_inst_ATS_axioms: "
  ATS_Language_axioms valid_parser parserFS_initial_configurations
     parserFS_step_relation parser_markers parserFS_marking_condition
     parserFS_marked_effect parserFS_unmarked_effect "
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: parserFS_inst_AX_effect_inclusion1 parserFS_inst_lang_sound parserFS_inst_AX_marking_condition_implies_existence_of_effect parserFS_inst_AX_unmarked_effect_persists )
  done

interpretation "parserFS" : loc_autFS_1
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserFS_configurations"
  (* initial_configurations *)
  "parserFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserFS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserFS_marking_condition"
  (* marked_effect *)
  "parserFS_marked_effect"
  (* unmarked_effect *)
  "parserFS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserFS_get_destinations"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserFS_inst_AX_initial_configuration_belongs parserFS_inst_AX_step_relation_preserves_belongs parserFS_inst_ATS_axioms )
  done

lemma parserFS_inst_AX_marking_can_not_be_disabled: "
  (\<forall>G d. (\<exists>n. parserFS_marking_condition G (derivation_take d n)) \<longrightarrow> parserFS_marking_condition G d)"
  apply(clarsimp)
  apply(rename_tac G d n)(*strict*)
  apply(simp add: parserFS_marking_condition_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac G d n c i e ca)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac G d n c i e ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G d n c i e ca)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="ca"
      in exI)
  apply(clarsimp)
  done

lemma parserFS_inst_AX_marked_effect_persists: "
  (\<forall>G d n. parserFS_marked_effect G (derivation_take d n) \<subseteq> parserFS_marked_effect G d)"
  apply(clarsimp)
  apply(rename_tac G d n x)(*strict*)
  apply(simp add: parserFS_marked_effect_def derivation_take_def)
  done

lemma parserFS_inst_accept: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> parserFS_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> parserFS_marking_configurations G))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: parserFS_marking_condition_def)
  apply(rule order_antisym)
   apply(rename_tac G d)(*strict*)
   apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d i e c)(*strict*)
  apply(simp add: parserFS.derivation_initial_def)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(rename_tac G d i e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G d i e c a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac G d i e c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d i e c b)(*strict*)
  apply(simp add: parserFS_initial_configurations_def)
  done

lemma parserFS_inst_AX_string_state_decreases: "
  \<forall>G. valid_parser G \<longrightarrow>
        (\<forall>c1. c1 \<in> parserFS_configurations G \<longrightarrow>
              (\<forall>e c2. parserFS_step_relation G c1 e c2 \<longrightarrow>
                      (\<exists>w. parserFS_string_state c1 =
                           w @ parserFS_string_state c2)))"
  apply(clarsimp)
  apply(rename_tac M c1 e c2)(*strict*)
  apply(simp add: parserFS_string_state_def parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac M c1 e c2 x v)(*strict*)
  apply(subgoal_tac "valid_parser_step_label M e")
   apply(rename_tac M e c1 c2 x v)(*strict*)
   prefer 2
   apply(rename_tac M c1 e c2 x v)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac M e c1 c2 x v)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac M e c1 c2 x v k w)(*strict*)
  apply(erule disjE)
   apply(rename_tac M e c1 c2 x v k w)(*strict*)
   apply(clarsimp)
   apply(rename_tac M e c1 c2 x v k w popnew)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(force)
  apply(rename_tac M e c1 c2 x v k w)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e c1 c2 x v k w remainder)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(force)
  done

lemma parserFS_inst_lang_finite: "
  (\<forall>G. valid_parser G \<longrightarrow> parserFS.finite_marked_language G = parserFS.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserFS.finite_marked_language_def parserFS.marked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: parserFS.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: parserFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d c)(*strict*)
  apply(simp add: parserFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G d c i e ca)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d c i e ca)(*strict*)
   apply(rule parserFS.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac G d c i e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d c i e ca)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d c i e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d c i e ca)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d c i e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d c i e ca)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="ca"
      in exI)
   apply(clarsimp)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d c i e ca)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma parserFS_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_parser G \<longrightarrow> parserFS.finite_unmarked_language G = parserFS.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserFS.finite_unmarked_language_def parserFS.unmarked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(simp add: parserFS.derivation_initial_def)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: parserFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d c c' i v e)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G d c c' i v e)(*strict*)
   apply(rule parserFS.derivation_take_preserves_derivation_initial)
   apply(force)
  apply(rename_tac G d c c' i v e)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d c c' i v e)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G d c c' i v e)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G d c c' i v e)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule conjI)
    apply(rename_tac G d c c' i v e)(*strict*)
    apply(simp add: derivation_take_def)
    apply(force)
   apply(rename_tac G d c c' i v e)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(clarsimp)
  apply(rename_tac G d c c' i v e)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule maximum_of_domain_derivation_take)
  apply(force)
  done

lemma parserFS_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_parser
     parserFS_initial_configurations parserFS_step_relation
     parserFS_marking_condition parserFS_marked_effect
     parserFS_unmarked_effect "
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(simp add: parserFS_inst_lang_finite parserFS_inst_AX_unmarked_language_finite )
  done

lemma parserFS_inst_ATS_String_State_Modification_axioms: "
  ATS_String_State_Modification_axioms valid_parser parserFS_configurations
     parserFS_step_relation True parserFS_string_state"
  apply(simp add: ATS_String_State_Modification_axioms_def)
  apply(simp add: parserFS_inst_AX_string_state_decreases )
  done

interpretation "parserFS" : loc_autFS_2
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserFS_configurations"
  (* initial_configurations *)
  "parserFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserFS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserFS_marking_condition"
  (* marked_effect *)
  "parserFS_marked_effect"
  (* unmarked_effect *)
  "parserFS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserFS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserFS_string_state"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserFS_inst_AX_initial_configuration_belongs parserFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserFS_inst_ATS_axioms parserFS_inst_ATS_String_State_Modification_axioms parserFS_inst_ATS_Language_by_Finite_Derivations_axioms )
  done

definition parserFS_get_scheduler :: "
  ('stack, 'event) parserFS_conf
  \<Rightarrow> 'event list"
  where
    "parserFS_get_scheduler c \<equiv>
  parserFS_conf_fixed c @ parserFS_conf_scheduler c"

definition parserFS_set_unfixed_scheduler :: "
  ('stack, 'event) parserFS_conf
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserFS_conf"
  where
    "parserFS_set_unfixed_scheduler c sUF \<equiv>
  c \<lparr>parserFS_conf_scheduler := sUF\<rparr>"

definition parserFS_get_unfixed_scheduler :: "
  ('stack, 'event) parserFS_conf
  \<Rightarrow> 'event list"
  where
    "parserFS_get_unfixed_scheduler c \<equiv>
  parserFS_conf_scheduler c"

lemma parserFS_inst_AX_get_scheduler_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserFS_configurations G \<longrightarrow> parserFS_get_scheduler c \<in> parser_schedulers G))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserFS_get_scheduler_def parserFS_configurations_def parser_schedulers_def prefix_def)
  apply(clarsimp)
  done

lemma parserFS_inst_schedUF_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserFS_configurations G \<longrightarrow> parserFS_get_unfixed_scheduler c \<in> parser_unfixed_schedulers G))"
  apply(simp add: parserFS_get_unfixed_scheduler_def parser_unfixed_schedulers_def parserFS_configurations_def)
  apply(clarsimp)
  done

lemma parserFS_inst_AX_set_unfixed_scheduler_set: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserFS_configurations G \<longrightarrow> (\<forall>sUF1. sUF1 \<in> parser_unfixed_schedulers G \<longrightarrow> (\<forall>sUF2. sUF2 \<in> parser_unfixed_schedulers G \<longrightarrow> parserFS_set_unfixed_scheduler (parserFS_set_unfixed_scheduler c sUF1) sUF2 = parserFS_set_unfixed_scheduler c sUF2))))"
  apply(simp add: parserFS_set_unfixed_scheduler_def)
  done

lemma parserFS_inst_AX_get_set_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserFS_configurations G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> parserFS_get_unfixed_scheduler (parserFS_set_unfixed_scheduler c sUF) = sUF)))"
  apply(simp add: parserFS_get_unfixed_scheduler_def parserFS_set_unfixed_scheduler_def)
  done

lemma parserFS_inst_AX_set_unfixed_scheduler_get: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserFS_configurations G \<longrightarrow> (\<forall>c2. c2 \<in> parserFS_configurations G \<longrightarrow> (\<exists>sUF\<in> parser_unfixed_schedulers G. parserFS_set_unfixed_scheduler c1 sUF = parserFS_set_unfixed_scheduler c2 sUF) \<longrightarrow> parserFS_set_unfixed_scheduler c1 (parserFS_get_unfixed_scheduler c2) = c2)))"
  apply(clarsimp)
  apply(rename_tac G c1 c2 sUF)(*strict*)
  apply(simp add: parserFS_set_unfixed_scheduler_def parserFS_get_unfixed_scheduler_def parserFS_configurations_def prefix_def)
  apply(clarsimp)
  done

lemma parserFS_inst_AX_unfixed_scheduler_extendable_quasi_preserved_by_set_unfixed_scheduler : "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserFS_configurations G \<longrightarrow> (\<forall>c2. c2 \<in> parserFS_configurations G \<longrightarrow> parserFS_get_unfixed_scheduler c1 \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserFS_set_unfixed_scheduler c1 (parserFS_get_unfixed_scheduler c2) = c2 \<longrightarrow> parserFS_get_unfixed_scheduler c2 \<sqsupseteq> [parser_bottom G])))"
  apply(clarsimp)
  apply(rename_tac G c1 c2)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_def parserFS_set_unfixed_scheduler_def parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G fa la r ra)(*strict*)
  apply(simp add: parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G fa la r ra v va)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G fa la ra va c)(*strict*)
  apply(case_tac ra)
   apply(rename_tac G fa la ra va c)(*strict*)
   apply(force)
  apply(rename_tac G fa la ra va c a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. ra = w' @ [x']")
   apply(rename_tac G fa la ra va c a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G fa la ra va c a list)(*strict*)
  apply(thin_tac "ra = a # list")
  apply(force)
  done

lemma parserFS_unfixed_is_reduced_by_single_step: "
  valid_parser G
  \<Longrightarrow> c1 \<in> parserFS_configurations G
  \<Longrightarrow> valid_parser_step_label G e
  \<Longrightarrow> c2 \<in> parserFS_configurations G
  \<Longrightarrow> parserFS_step_relation G c1 e c2
  \<Longrightarrow> parserFS_get_unfixed_scheduler c1 \<sqsupseteq> parserFS_get_unfixed_scheduler c2"
  apply(simp add: parserFS_step_relation_def)
  apply(simp add: parserFS_get_unfixed_scheduler_def parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac f fa r ra x v)(*strict*)
  apply(erule disjE)
   apply(rename_tac f fa r ra x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac f ra x v popnew)(*strict*)
   apply(simp add: suffix_def)
  apply(rename_tac f fa r ra x v)(*strict*)
  apply(clarsimp)
  apply(rename_tac ra x v remainder)(*strict*)
  apply(simp add: suffix_def)
  done

lemma parserFS_unfixed_is_reduced_by_steps: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation G d
  \<Longrightarrow> parserFS.belongs G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> d m = Some (pair e' c')
  \<Longrightarrow> n\<le>m
  \<Longrightarrow> suffix (parserFS_get_unfixed_scheduler c) (parserFS_get_unfixed_scheduler c')"
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac x n m e c e' c')(*strict*)
   prefer 2
   apply(rule_tac
      m="m"
      in parserFS.step_detail_before_some_position)
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
  apply(subgoal_tac "parserFS_get_unfixed_scheduler c \<sqsupseteq> parserFS_get_unfixed_scheduler c2")
   apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
   apply(simp add: suffix_def)
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
  apply(rule parserFS_unfixed_is_reduced_by_single_step)
      apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
      apply(force)
     apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
     apply (metis parserFS.belongs_configurations)
    apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
    prefer 2
    apply (metis parserFS.belongs_configurations)
   apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x n m e c e' c' e2 c2)(*strict*)
  apply(simp add: parserFS_step_relation_def valid_parser_def)
  done

lemma parserFS_inst_AX_unfixed_scheduler_right_quotient_split: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation G d \<longrightarrow> parserFS.belongs G d \<longrightarrow> (\<forall>n e1 c1. d n = Some (pair e1 c1) \<longrightarrow> (\<forall>m e2 c2. d m = Some (pair e2 c2) \<longrightarrow> (\<forall>k e3 c3. d k = Some (pair e3 c3) \<longrightarrow> n \<le> m \<longrightarrow> m \<le> k \<longrightarrow> the (right_quotient_word (parserFS_get_unfixed_scheduler c1) (parserFS_get_unfixed_scheduler c3)) = the (right_quotient_word (parserFS_get_unfixed_scheduler c1) (parserFS_get_unfixed_scheduler c2)) @ the (right_quotient_word (parserFS_get_unfixed_scheduler c2) (parserFS_get_unfixed_scheduler c3))))))"
  apply(clarsimp)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
  apply(subgoal_tac "suffix (parserFS_get_unfixed_scheduler c1) (parserFS_get_unfixed_scheduler c2)")
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
   prefer 2
   apply(rule parserFS_unfixed_is_reduced_by_steps)
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
  apply(subgoal_tac "suffix (parserFS_get_unfixed_scheduler c2) (parserFS_get_unfixed_scheduler c3)")
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3)(*strict*)
   prefer 2
   apply(rule parserFS_unfixed_is_reduced_by_steps)
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
      t="right_quotient_word (c @ ca @ parserFS_get_unfixed_scheduler c3) (parserFS_get_unfixed_scheduler c3)"
      and s="Some(c@ca)"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
  apply(rule_tac
      t="right_quotient_word (c @ ca @ parserFS_get_unfixed_scheduler c3) (ca@parserFS_get_unfixed_scheduler c3)"
      and s="Some c"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
  apply(rule_tac
      t="right_quotient_word (ca @ parserFS_get_unfixed_scheduler c3) (parserFS_get_unfixed_scheduler c3)"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G d n e1 c1 m e2 c2 k e3 c3 c ca)(*strict*)
  apply(clarsimp)
  done

lemma parserFS_inst_ATS_SchedUF_SB_axioms: "
  ATS_SchedUF_SB_axioms valid_parser parserFS_configurations
     parser_step_labels parserFS_step_relation (@)
     parser_unfixed_schedulers right_quotient_word
     parser_unfixed_scheduler_extendable parserFS_set_unfixed_scheduler
     parserFS_get_unfixed_scheduler"
  apply(simp add: ATS_SchedUF_SB_axioms_def)
  apply(simp add: parserFS_inst_schedUF_closed parserFS_inst_AX_set_unfixed_scheduler_set parserFS_inst_AX_get_set_unfixed_scheduler parserFS_inst_AX_set_unfixed_scheduler_get )
  apply(rule conjI, rule parserFS_inst_AX_unfixed_scheduler_extendable_quasi_preserved_by_set_unfixed_scheduler)
  apply(rule parserFS_inst_AX_unfixed_scheduler_right_quotient_split)
  done

lemma parserFS_inst_AX_fixed_scheduler_extendable_translates_backwards: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserFS_configurations G \<longrightarrow> (\<forall>e c2. parserFS_step_relation G c1 e c2 \<longrightarrow> \<not> parserFS_conf_fixed c2 \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> parserFS_conf_fixed c1 \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_string_state c1 = w @ parserFS_string_state c2")
   apply(rename_tac G c1 e c2)(*strict*)
   prefer 2
   apply(rule parserFS.AX_string_state_decreases)
      apply(rename_tac G c1 e c2)(*strict*)
      apply(force)
     apply(rename_tac G c1 e c2)(*strict*)
     apply(force)
    apply(rename_tac G c1 e c2)(*strict*)
    apply(simp add: parser_step_labels_def parserFS_step_relation_def)
   apply(rename_tac G c1 e c2)(*strict*)
   apply(force)
  apply(rename_tac G c1 e c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c1 e c2 w)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e")
   apply(rename_tac G c1 e c2 w)(*strict*)
   prefer 2
   apply(simp add: parserFS_step_relation_def valid_parser_def)
  apply(rename_tac G c1 e c2 w)(*strict*)
  apply(subgoal_tac "c2 \<in> parserFS_configurations G")
   apply(rename_tac G c1 e c2 w)(*strict*)
   prefer 2
   apply(rule parserFS.AX_step_relation_preserves_belongsC)
     apply(rename_tac G c1 e c2 w)(*strict*)
     apply(force)
    apply(rename_tac G c1 e c2 w)(*strict*)
    apply(force)
   apply(rename_tac G c1 e c2 w)(*strict*)
   apply(force)
  apply(rename_tac G c1 e c2 w)(*strict*)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G c1 e c2 w x v)(*strict*)
  apply(erule disjE)
   apply(rename_tac G c1 e c2 w x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac G c1 e c2 w x v popnew)(*strict*)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac G c1 e c2 w x v popnew c)(*strict*)
   apply(case_tac popnew)
    apply(rename_tac G c1 e c2 w x v popnew c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G c1 e c2 w x v c)(*strict*)
    apply(case_tac "rule_rpush e")
     apply(rename_tac G c1 e c2 w x v c)(*strict*)
     apply(clarsimp)
     apply(rename_tac G c1 e c2 w x c)(*strict*)
     apply(simp add: valid_parser_step_label_def)
    apply(rename_tac G c1 e c2 w x v c a list)(*strict*)
    apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
     apply(rename_tac G c1 e c2 w x v c a list)(*strict*)
     prefer 2
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac G c1 e c2 w x v c a list)(*strict*)
    apply(thin_tac "rule_rpush e = a # list")
    apply(force)
   apply(rename_tac G c1 e c2 w x v popnew c a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. popnew = w' @ [x']")
    apply(rename_tac G c1 e c2 w x v popnew c a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G c1 e c2 w x v popnew c a list)(*strict*)
   apply(thin_tac "popnew = a # list")
   apply(clarsimp)
   apply(rename_tac G c1 e c2 w x v c w' x')(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G c1 e c2 w x v c w' x' k wa)(*strict*)
   apply(simp add: kPrefix_def)
   apply(subgoal_tac "parser_bottom G \<in> set wa")
    apply(rename_tac G c1 e c2 w x v c w' x' k wa)(*strict*)
    apply(subgoal_tac "parser_bottom G \<notin> set wa")
     apply(rename_tac G c1 e c2 w x v c w' x' k wa)(*strict*)
     apply(force)
    apply(rename_tac G c1 e c2 w x v c w' x' k wa)(*strict*)
    apply (metis not_in_diff)
   apply(rename_tac G c1 e c2 w x v c w' x' k wa)(*strict*)
   apply(case_tac "k-length wa")
    apply(rename_tac G c1 e c2 w x v c w' x' k wa)(*strict*)
    apply(clarsimp)
    apply (metis take_reflects_mem)
   apply(rename_tac G c1 e c2 w x v c w' x' k wa nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac G c1 e c2 w x v)(*strict*)
  apply(clarsimp)
  apply(rename_tac G c1 e c2 w x v remainder)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G c1 e c2 w x v remainder c)(*strict*)
  apply(simp add: parserFS_string_state_def)
  apply(clarsimp)
  apply(rename_tac G c1 e c2 w x remainder c)(*strict*)
  apply(case_tac c1)
  apply(rename_tac G c1 e c2 w x remainder c parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G c1 e c2 w x remainder c parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G e w x remainder c parserFS_conf_schedulera)(*strict*)
  apply(rename_tac r)
  apply(rename_tac G e w x remainder c r)(*strict*)
  apply(case_tac remainder)
   apply(rename_tac G e w x remainder c r)(*strict*)
   apply(clarsimp)
   apply(rename_tac G e w x c r)(*strict*)
   apply(case_tac "rule_rpush e")
    apply(rename_tac G e w x c r)(*strict*)
    apply(clarsimp)
    apply(rename_tac G e x c r)(*strict*)
    apply(simp add: valid_parser_step_label_def)
   apply(rename_tac G e w x c r a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. rule_rpush e = w' @ [x']")
    apply(rename_tac G e w x c r a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G e w x c r a list)(*strict*)
   apply(thin_tac "rule_rpush e = a # list")
   apply(force)
  apply(rename_tac G e w x remainder c r a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. remainder = w' @ [x']")
   apply(rename_tac G e w x remainder c r a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G e w x remainder c r a list)(*strict*)
  apply(thin_tac "remainder = a # list")
  apply(clarsimp)
  done

lemma parserFS_inst_ATS_SchedF_SB_axioms: "
  ATS_SchedF_SB_axioms valid_parser parserFS_configurations
     parserFS_step_relation parser_fixed_scheduler_extendable
     parserFS_conf_fixed"
  apply(simp add: ATS_SchedF_SB_axioms_def)
  apply(simp add: parserFS_inst_AX_fixed_scheduler_extendable_translates_backwards )
  done

lemma parserFS_inst_AX_not_extendable_fixed_scheduler_implies_empty_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserFS_configurations G \<longrightarrow> parserFS_conf_fixed c \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserFS_get_unfixed_scheduler c = []))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G f l r)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_def)
  apply(simp add: prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac G l r c)(*strict*)
  apply(simp add: parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G l r c v)(*strict*)
  apply(case_tac r)
   apply(rename_tac G l r c v)(*strict*)
   apply(clarsimp)
  apply(rename_tac G l r c v a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
   apply(rename_tac G l r c v a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G l r c v a list)(*strict*)
  apply(thin_tac "r = a # list")
  apply(clarsimp)
  done

lemma parserFS_inst_extendable_implies_notempty_unfixed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserFS_configurations G \<longrightarrow> \<not> parserFS_conf_fixed c \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserFS_get_unfixed_scheduler c \<noteq> []))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G f l r)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_def)
  apply(simp add: suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G f l)(*strict*)
  apply(simp add: parser_schedulers_def)
  done

lemma parserFS_inst_AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserFS_configurations G \<longrightarrow> parserFS_get_scheduler c = parserFS_conf_fixed c @ parserFS_get_unfixed_scheduler c))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: parserFS_configurations_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G f l r)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_def)
  apply(simp add: parserFS_get_scheduler_def)
  done

lemma parserFS_inst_AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserFS_configurations G \<longrightarrow> parserFS_get_unfixed_scheduler c \<sqsupseteq> [parser_bottom G] = (\<not> parserFS_conf_fixed c \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G c)(*strict*)
  apply(simp add: prefix_def suffix_def parserFS_configurations_def parserFS_get_unfixed_scheduler_def)
  apply(clarsimp)
  apply(rename_tac G f l r)(*strict*)
  apply(simp add: parser_schedulers_def parser_unfixed_schedulers_def parser_fixed_schedulers_def prefix_closure_def suffix_closure_def prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac G f l r vb vc c vd ca)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G f l r vb vc c vd ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f l r vb vc c vd ca)(*strict*)
  apply(clarsimp)
  apply(case_tac r)
   apply(rename_tac G f l r vb vc c vd ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac G f l r vb vc c vd ca a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
   apply(rename_tac G f l r vb vc c vd ca a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G f l r vb vc c vd ca a list)(*strict*)
  apply(thin_tac "r = a # list")
  apply(clarsimp)
  done

lemma parserFS_inst_AX_equal_up_to_unfixed_scheduler_implies_equal_fixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c1. c1 \<in> parserFS_configurations G \<longrightarrow> (\<forall>c2. c2 \<in> parserFS_configurations G \<longrightarrow> parserFS_set_unfixed_scheduler c1 (parserFS_get_unfixed_scheduler c2) = c2 \<longrightarrow> parserFS_conf_fixed c1 = parserFS_conf_fixed c2)))"
  apply(simp add: parserFS_set_unfixed_scheduler_def parserFS_get_unfixed_scheduler_def)
  apply(clarsimp)
  apply(rename_tac G c1 c2)(*strict*)
  apply(case_tac c1)
  apply(rename_tac G c1 c2 parserFS_conf_fixeda parserFS_conf_stack parserFS_conf_schedulera)(*strict*)
  apply(case_tac c2)
  apply(rename_tac G c1 c2 parserFS_conf_fixeda parserFS_conf_stack parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stacka parserFS_conf_scheduleraa)(*strict*)
  apply(clarsimp)
  done

lemma parserFS_inst_ATS_Sched_axioms: "
  ATS_Sched_axioms valid_parser parserFS_configurations
     parser_scheduler_fragments parser_empty_scheduler_fragment (@)
     parser_schedulers parser_schedulers parser_empty_scheduler
     parserFS_get_scheduler (@)"
  apply(simp add: ATS_Sched_axioms_def)
  apply(simp add: parser_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed parser_inst_AX_extend_scheduler_closed parser_inst_AX_empty_scheduler_in_schedulers parserFS_inst_AX_get_scheduler_closed )
  done

lemma parserFS_inst_ATS_Sched_SB_axioms: "
  ATS_Sched_SB_axioms valid_parser parserFS_configurations
     parser_fixed_scheduler_extendable parser_empty_unfixed_scheduler
     parser_unfixed_scheduler_extendable parserFS_get_scheduler (@)
     parserFS_set_unfixed_scheduler parserFS_get_unfixed_scheduler
     parserFS_conf_fixed"
  apply(simp add: ATS_Sched_SB_axioms_def)
  apply(simp add: parserFS_inst_AX_not_extendable_fixed_scheduler_implies_empty_unfixed_scheduler parserFS_inst_extendable_implies_notempty_unfixed parserFS_inst_AX_get_scheduler_vs_get_fixed_scheduler_and_get_unfixed_scheduler parserFS_inst_AX_unfixed_scheduler_extendable_vs_fixed_scheduler_extendable )
  apply(rule parserFS_inst_AX_equal_up_to_unfixed_scheduler_implies_equal_fixed_scheduler)
  done

print_locale loc_autFS_3
interpretation "parserFS" : loc_autFS_3
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserFS_configurations"
  (* initial_configurations *)
  "parserFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserFS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserFS_marking_condition"
  (* marked_effect *)
  "parserFS_marked_effect"
  (* unmarked_effect *)
  "parserFS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserFS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserFS_string_state"
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
  "parserFS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler *)
  "parserFS_set_unfixed_scheduler"
  (* get_unfixed_scheduler *)
  "parserFS_get_unfixed_scheduler"
  (* get_fixed_scheduler *)
  "parserFS_conf_fixed"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserFS_inst_AX_initial_configuration_belongs parserFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserFS_inst_ATS_axioms parserFS_inst_ATS_String_State_Modification_axioms parserFS_inst_ATS_Language_by_Finite_Derivations_axioms parserFS_inst_ATS_SchedUF_SB_axioms parserFS_inst_ATS_SchedF_SB_axioms parserFS_inst_ATS_Sched_axioms parserFS_inst_ATS_Sched_SB_axioms )
  done

definition parserFS_get_fixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "parserFS_get_fixed_scheduler_DB G d n \<equiv>
  parserFS_conf_fixed (the (get_configuration (d n)))"

definition parserFS_set_unfixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserFS_conf"
  where
    "parserFS_set_unfixed_scheduler_DB G d n sUF \<equiv>
  parserFS_set_unfixed_scheduler
    (the (get_configuration (d n))) sUF"

definition parserFS_get_unfixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "parserFS_get_unfixed_scheduler_DB G d n \<equiv>
  parserFS_conf_scheduler (the (get_configuration (d n)))"

lemma parserFS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation G d \<longrightarrow> (\<forall>c. d 0 = Some (pair None c) \<longrightarrow> c \<in> parserFS_initial_configurations G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> parserFS_get_unfixed_scheduler_DB G d 0 \<sqsupseteq> [parser_bottom G] \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserFS_set_unfixed_scheduler_DB G d 0 sUF \<in> parserFS_initial_configurations G))))"
  apply(clarsimp)
  apply(rename_tac G d c sUF)(*strict*)
  apply(simp add: get_configuration_def parserFS_set_unfixed_scheduler_DB_def parserFS_initial_configurations_def parserFS_configurations_def parserFS_get_fixed_scheduler_DB_def parser_unfixed_schedulers_def parser_schedulers_def suffix_closure_def suffix_def prefix_def)
  apply(clarsimp)
  apply(rename_tac G d ca cb cc vc "cd")(*strict*)
  apply(simp add: parserFS_set_unfixed_scheduler_def)
  apply(rule_tac
      x="cb @ [parser_bottom G]"
      in exI)
  apply(force)
  done

lemma parserFS_inst_AX_get_unfixed_scheduler_DB_extendable_on_initial_configuration: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> parserFS_get_unfixed_scheduler_DB G d 0 \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac G d)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "c \<in> parserFS_configurations G")
    apply(rename_tac G d c)(*strict*)
    apply(simp add: parserFS_configurations_def parserFS_get_scheduler_def)
    apply(clarsimp)
    apply(rename_tac G d f l r)(*strict*)
    apply(simp add: suffix_def)
    apply(simp add: parser_unfixed_schedulers_def parser_fixed_schedulers_def parser_schedulers_def prefix_def suffix_def prefix_closure_def suffix_closure_def)
    apply(clarsimp)
    apply(rename_tac G d f l r vb vc c vd ca)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
    apply(simp add: parserFS_initial_configurations_def)
   apply(rename_tac G d c)(*strict*)
   apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
  apply(rename_tac G d)(*strict*)
  apply (metis parserFS.derivation_initial_is_derivation parserFS.some_position_has_details_at_0)
  done

lemma parserFS_inst_AX_get_unfixed_scheduler_DB_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation G d \<longrightarrow> parserFS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>e c. d n = Some (pair e c)) \<longrightarrow> parserFS_get_unfixed_scheduler_DB G d n \<in> parser_unfixed_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parser_unfixed_schedulers_def parserFS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "c \<in> parserFS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply(rule parserFS.belongs_configurations)
    apply(rename_tac G d n e c)(*strict*)
    apply(force)
   apply(rename_tac G d n e c)(*strict*)
   apply(force)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: prefix_closure_def prefix_def parser_fixed_schedulers_def parser_unfixed_schedulers_def suffix_closure_def suffix_def parserFS_configurations_def parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G d n e f l r vb vc ca vd cb)(*strict*)
  apply(force)
  done

lemma parserFS_inst_get_unfixed_scheduler_DB_constructs_right_quotient: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (\<forall>j. parserFS_get_unfixed_scheduler_DB G d j \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>i\<le>j. j \<le> n \<longrightarrow> the (right_quotient_word (parserFS_get_unfixed_scheduler_DB G d i) (parserFS_get_unfixed_scheduler_DB G d j)) \<in> parser_scheduler_fragments G)))))"
  apply(clarsimp)
  apply(rename_tac G d n y j i)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. d i = Some (pair e c)")
   apply(rename_tac G d n y j i)(*strict*)
   apply(subgoal_tac "\<exists>e c. d j = Some (pair e c)")
    apply(rename_tac G d n y j i)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d n y j i e ea c ca)(*strict*)
    apply(simp add: get_configuration_def)
    apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler c = w @ parserFS_conf_scheduler ca")
     apply(rename_tac G d n y j i e ea c ca)(*strict*)
     prefer 2
     apply(rule_tac
      j="j"
      in parserFS_input_decreases)
          apply(rename_tac G d n y j i e ea c ca)(*strict*)
          apply(force)
         apply(rename_tac G d n y j i e ea c ca)(*strict*)
         apply(rule parserFS.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac G d n y j i e ea c ca)(*strict*)
        apply(rule parserFS.derivation_initial_belongs)
         apply(rename_tac G d n y j i e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac G d n y j i e ea c ca)(*strict*)
        apply(force)
       apply(rename_tac G d n y j i e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac G d n y j i e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac G d n y j i e ea c ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d n y j i e ea c ca w)(*strict*)
    apply(subgoal_tac "the (right_quotient_word (w @ parserFS_conf_scheduler ca) (parserFS_conf_scheduler ca))=w")
     apply(rename_tac G d n y j i e ea c ca w)(*strict*)
     apply(clarsimp)
     apply(simp add: parser_scheduler_fragments_def)
     apply(subgoal_tac "c \<in> parserFS_configurations G")
      apply(rename_tac G d n y j i e ea c ca w)(*strict*)
      apply(subgoal_tac "ca \<in> parserFS_configurations G")
       apply(rename_tac G d n y j i e ea c ca w)(*strict*)
       apply(simp add: parserFS_configurations_def)
       apply(clarsimp)
       apply(rename_tac G d n y j i e ea w f fa l la ra)(*strict*)
       apply(simp add: prefix_closure_def prefix_def parser_schedulers_def parser_unfixed_schedulers_def parser_fixed_schedulers_def suffix_closure_def suffix_def)
       apply(clarsimp)
      apply(rename_tac G d n y j i e ea c ca w)(*strict*)
      apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
     apply(rename_tac G d n y j i e ea c ca w)(*strict*)
     apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
    apply(rename_tac G d n y j i e ea c ca w)(*strict*)
    apply (metis right_quotient_word_removes_right_addition option.sel)
   apply(rename_tac G d n y j i)(*strict*)
   apply(rule parserFS.pre_some_position_is_some_position)
     apply(rename_tac G d n y j i)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G d n y j i)(*strict*)
    apply(force)
   apply(rename_tac G d n y j i)(*strict*)
   apply(force)
  apply(rename_tac G d n y j i)(*strict*)
  apply(rule parserFS.pre_some_position_is_some_position)
    apply(rename_tac G d n y j i)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
    apply(force)
   apply(rename_tac G d n y j i)(*strict*)
   apply(force)
  apply(rename_tac G d n y j i)(*strict*)
  apply(force)
  done

lemma parserFS_parser_fixed_input_length_recN_with_derivation_take: "
  i\<le>n
  \<Longrightarrow> parserFS.derivation M d
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserFS_step_relation M c1 e2 c2")
   apply(rename_tac i a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserFS.step_detail_before_some_position)
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

lemma parserFS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n m. n \<le> m \<longrightarrow> parserFS_get_unfixed_scheduler_DB G d n = parserFS_get_unfixed_scheduler_DB G (derivation_take d m) n))"
  apply(clarsimp)
  apply(rename_tac G d n m)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d m) n"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
   apply(rename_tac G d n m)(*strict*)
   defer
   apply(simp add: derivation_take_def)
  apply(rename_tac G d n m)(*strict*)
  apply (metis parserFS.derivation_initial_is_derivation parserFS_parser_fixed_input_length_recN_with_derivation_take)
  done

lemma parserFS_inst_ATS_SchedUF_DB_axioms: "
  ATS_SchedUF_DB_axioms valid_parser parserFS_configurations
     parserFS_initial_configurations parser_step_labels
     parserFS_step_relation parser_scheduler_fragments
     parser_unfixed_schedulers right_quotient_word
     parser_unfixed_scheduler_extendable parserFS_set_unfixed_scheduler_DB
     parserFS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_SchedUF_DB_axioms_def)
  apply(simp add: parserFS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations parserFS_inst_AX_get_unfixed_scheduler_DB_extendable_on_initial_configuration parserFS_inst_AX_get_unfixed_scheduler_DB_closed parserFS_inst_get_unfixed_scheduler_DB_constructs_right_quotient )
  apply(rule parserFS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take)
  done

lemma parserFS_parser_fixed_input_length_recN_with_derivation_append: "
  i\<le>n
  \<Longrightarrow> parserFS.derivation M d1
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> d1 (Suc i) = Some (pair (Some e2) c2) \<and> parserFS_step_relation M c1 e2 c2")
   apply(rename_tac i a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserFS.step_detail_before_some_position)
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

lemma parserFS_inst_AX_get_fixed_scheduler_DB_restrict: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>x n. x \<le> n \<longrightarrow> (\<forall>d1. parserFS.derivation G d1 \<longrightarrow> (\<forall>d2. parserFS_get_fixed_scheduler_DB G (derivation_append d1 d2 n) x = parserFS_get_fixed_scheduler_DB G d1 x))))"
  apply(clarsimp)
  apply(rename_tac G x n d1 d2)(*strict*)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def parserFS_get_scheduler_def)
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
  apply (metis parserFS_parser_fixed_input_length_recN_with_derivation_append)
  done

lemmas dom_abbreviation =
  parser_fixed_schedulers_def
  parser_unfixed_schedulers_def
  parser_schedulers_def
  prefix_def
  prefix_closure_def
  suffix_closure_def
  suffix_def

lemma parserFS_inst_AX_schedF_db_extendable_translates_backwards: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d1. parserFS.derivation G d1 \<longrightarrow> parserFS.belongs G d1 \<longrightarrow> (\<forall>n x. (\<exists>y. d1 (n + x) = Some y) \<longrightarrow> \<not> parserFS_get_fixed_scheduler_DB G d1 (n + x) \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> parserFS_get_fixed_scheduler_DB G d1 n \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G d1 n x y)(*strict*)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def)
  apply(case_tac y)
  apply(rename_tac G d1 n x y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d1 n x option b)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 n = Some (pair e c)")
   apply(rename_tac G d1 n x option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "c \<in> parserFS_configurations G")
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply(subgoal_tac "b \<in> parserFS_configurations G")
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(subgoal_tac "parserFS_conf_scheduler c = []")
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(subgoal_tac "parserFS_conf_scheduler b = []")
       apply(rename_tac G d1 n x option b e c)(*strict*)
       apply(subgoal_tac "parserFS_conf_fixed b \<sqsupseteq> [parser_bottom G]")
        apply(rename_tac G d1 n x option b e c)(*strict*)
        apply(force)
       apply(rename_tac G d1 n x option b e c)(*strict*)
       apply(simp add: parserFS_configurations_def)
       apply(clarsimp)
       apply(rename_tac G d1 n x option e f fa l la)(*strict*)
       apply(simp add: dom_abbreviation)
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler c = w @ parserFS_conf_scheduler b")
       apply(rename_tac G d1 n x option b e c)(*strict*)
       prefer 2
       apply(rule_tac
      j="n+x"
      in parserFS_input_decreases)
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
       apply(force)
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(simp add: parserFS_configurations_def)
     apply(clarsimp)
     apply(rename_tac G d1 n x option e f fa l la r ra)(*strict*)
     apply(simp add: dom_abbreviation)
     apply(clarsimp)
     apply(rename_tac G d1 n x option e fa l la r ra c vc ve vf ca vg cb vh cc vi "cd")(*strict*)
     apply(case_tac r)
      apply(rename_tac G d1 n x option e fa l la r ra c vc ve vf ca vg cb vh cc vi "cd")(*strict*)
      apply(force)
     apply(rename_tac G d1 n x option e fa l la r ra c vc ve vf ca vg cb vh cc vi "cd" a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. r = w' @ [x']")
      apply(rename_tac G d1 n x option e fa l la r ra c vc ve vf ca vg cb vh cc vi "cd" a list)(*strict*)
      prefer 2
      apply(rule NonEmptyListHasTailElem)
      apply(force)
     apply(rename_tac G d1 n x option e fa l la r ra c vc ve vf ca vg cb vh cc vi "cd" a list)(*strict*)
     apply(thin_tac "r = a # list")
     apply(clarsimp)
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply (metis parserFS.belongs_configurations)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   apply (metis parserFS.belongs_configurations)
  apply(rename_tac G d1 n x option b)(*strict*)
  apply(rule parserFS.pre_some_position_is_some_position)
    apply(rename_tac G d1 n x option b)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
   apply(rename_tac G d1 n x option b)(*strict*)
   apply(force)
  apply(rename_tac G d1 n x option b)(*strict*)
  apply(force)
  done

lemma parserFS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation G d \<longrightarrow> parserFS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserFS_get_fixed_scheduler_DB G d n \<in> parser_fixed_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def get_configuration_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b)(*strict*)
  apply(subgoal_tac "b \<in> parserFS_configurations G")
   apply(rename_tac G d n option b)(*strict*)
   prefer 2
   apply (metis parserFS.belongs_configurations)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: parserFS_get_scheduler_def parserFS_configurations_def parser_fixed_schedulers_def)
  apply(clarsimp)
  done

lemma parserFS_inst_ATS_SchedF_DB_axioms: "
  ATS_SchedF_DB_axioms valid_parser parserFS_configurations
     parser_step_labels parserFS_step_relation parser_fixed_schedulers
     parser_fixed_scheduler_extendable parserFS_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_DB_axioms_def)
  apply(simp add: parserFS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers parserFS_inst_AX_get_fixed_scheduler_DB_restrict parserFS_inst_AX_schedF_db_extendable_translates_backwards )
  done

lemma parserFS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserFS_get_fixed_scheduler_DB G d n @ parserFS_get_unfixed_scheduler_DB G d n \<in> parser_schedulers G))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def parserFS_get_scheduler_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(simp add: get_configuration_def parserFS_get_unfixed_scheduler_DB_def parserFS_get_scheduler_def)
  apply(subgoal_tac "b \<in> parserFS_configurations G")
   apply(rename_tac G d n y option b)(*strict*)
   prefer 2
   apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
  apply(rename_tac G d n y option b)(*strict*)
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  done

lemma parserFS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserFS_get_fixed_scheduler_DB G d n @ parserFS_get_unfixed_scheduler_DB G d n = ATS_Sched.get_scheduler_nth parserFS_get_scheduler d n)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserFS.get_scheduler_nth_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(simp add: parserFS_get_scheduler_def)
  done

lemma parserFS_inst_AX_sched_modification_preserves_steps: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>dh n. maximum_of_domain dh n \<longrightarrow> parserFS.derivation G dh \<longrightarrow> parserFS.belongs G dh \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> (\<exists>sF. \<not> sF \<sqsupseteq> [parser_bottom G]) \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>m e2 c2. dh (Suc m) = Some (pair (Some e2) c2) \<longrightarrow> (\<forall>e1 c1. dh m = Some (pair e1 c1) \<longrightarrow> parserFS_step_relation G c1 e2 c2 \<longrightarrow> parserFS_step_relation G (parserFS_set_unfixed_scheduler_DB G dh m (the (right_quotient_word (parserFS_get_unfixed_scheduler_DB G dh m) (parserFS_get_unfixed_scheduler_DB G dh n)) @ sUF)) e2 (parserFS_set_unfixed_scheduler_DB G dh (Suc m) (the (right_quotient_word (parserFS_get_unfixed_scheduler_DB G dh (Suc m)) (parserFS_get_unfixed_scheduler_DB G dh n)) @ sUF))))))"
  apply(clarsimp)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1)(*strict*)
  apply(simp add: get_configuration_def parserFS_set_unfixed_scheduler_DB_def parserFS_get_fixed_scheduler_DB_def parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v)(*strict*)
  apply(simp add: parserFS_set_unfixed_scheduler_def)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v)(*strict*)
     apply(force)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler c1 = w @ parserFS_conf_scheduler c2")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc m"
      in parserFS_input_decreases)
        apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
        apply(force)
       apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
       apply(force)
      apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
      apply(force)
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
     apply(force)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
  apply(subgoal_tac "Suc m\<le>n")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
   apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler c2 = w @ parserFS_conf_scheduler c")
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
    prefer 2
    apply(rule_tac
      j="n"
      in parserFS_input_decreases)
         apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
         apply(force)
        apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
        apply(force)
       apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
       apply(force)
      apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
      apply(force)
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
     apply(force)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w wa)(*strict*)
   apply(subgoal_tac "the (right_quotient_word (w @ wa @ parserFS_conf_scheduler c) (parserFS_conf_scheduler c))=w@wa")
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w wa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "the (right_quotient_word (wa @ parserFS_conf_scheduler c) (parserFS_conf_scheduler c))=wa")
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c wa remainder)(*strict*)
     apply(force)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w wa)(*strict*)
    apply (metis right_quotient_word_removes_right_addition option.sel)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w wa)(*strict*)
   apply(rule_tac
      t="w @ wa @ parserFS_conf_scheduler c"
      and s="(w @ wa) @ parserFS_conf_scheduler c"
      in ssubst)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w wa)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w wa)(*strict*)
   apply (metis right_quotient_word_removes_right_addition option.sel)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
  apply(rule parserFS.allPreMaxDomSome_prime)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
    apply(force)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x v e c w)(*strict*)
  apply(force)
  done

lemma parserFS_inst_AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB: "
   \<forall>G::('stack, 'event, 'marker) parser.
       valid_parser G \<longrightarrow>
       (\<forall>d::(('stack, 'event) parser_step_label,
                   ('stack, 'event) parserFS_conf) derivation.
           ATS.derivation_initial parserFS_initial_configurations
            parserFS_step_relation G d \<longrightarrow>
           (\<forall>n::nat.
               (\<exists>y::(('stack, 'event) parser_step_label,
                    ('stack, 'event) parserFS_conf) derivation_configuration.
                   d n = Some y) \<longrightarrow>
               (\<not> parserFS_get_fixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G]) =
               parserFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def parserFS_get_unfixed_scheduler_DB_def get_configuration_def)
  apply(case_tac y)
  apply(rename_tac G d n y option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: suffix_def)
  apply(subgoal_tac "c \<in> parserFS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply (metis parserFS.derivation_initial_configurations)
  apply(rename_tac G d n e c)(*strict*)
  apply(rule antisym)
   apply(rename_tac G d n e c)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G d n e c ca cb)(*strict*)
   apply(subgoal_tac "c \<notin> parserFS_configurations G")
    apply(rename_tac G d n e c ca cb)(*strict*)
    prefer 2
    apply(simp add: parserFS_configurations_def parser_schedulers_def)
    apply(clarsimp)
   apply(rename_tac G d n e c ca cb)(*strict*)
   apply(force)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserFS_configurations_def parser_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G d n e f l r v)(*strict*)
  apply(rule_tac
      xs="r"
      in rev_cases)
   apply(rename_tac G d n e f l r v)(*strict*)
   prefer 2
   apply(rename_tac G d n e f l r v ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac G d n e f l r v)(*strict*)
  apply(clarsimp)
  done

lemma parserFS_inst_ATS_Sched_DB0_axioms: "
  ATS_Sched_DB0_axioms valid_parser parserFS_configurations
     parserFS_initial_configurations parser_step_labels
     parserFS_step_relation parser_fixed_scheduler_extendable
     parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parser_schedulers
     parserFS_get_scheduler (@) parserFS_set_unfixed_scheduler_DB
     parserFS_get_unfixed_scheduler_DB parserFS_get_fixed_scheduler_DB"
  apply(simp add: ATS_Sched_DB0_axioms_def)
  apply(simp add: parserFS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime parserFS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth parserFS_inst_AX_sched_modification_preserves_steps parserFS_inst_AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB )
  done

print_locale loc_autFS_4
interpretation "parserFS" : loc_autFS_4
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserFS_configurations"
  (* initial_configurations *)
  "parserFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserFS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserFS_marking_condition"
  (* marked_effect *)
  "parserFS_marked_effect"
  (* unmarked_effect *)
  "parserFS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserFS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserFS_string_state"
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
  "parserFS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler *)
  "parserFS_set_unfixed_scheduler"
  (* get_unfixed_scheduler *)
  "parserFS_get_unfixed_scheduler"
  (* get_fixed_scheduler *)
  "parserFS_conf_fixed"
  (* set_unfixed_scheduler_DB *)
  "parserFS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserFS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserFS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserFS_inst_AX_initial_configuration_belongs parserFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserFS_inst_ATS_axioms parserFS_inst_ATS_String_State_Modification_axioms parserFS_inst_ATS_Language_by_Finite_Derivations_axioms parserFS_inst_ATS_SchedUF_SB_axioms parserFS_inst_ATS_SchedF_SB_axioms parserFS_inst_ATS_Sched_SB_axioms parserFS_inst_ATS_SchedUF_DB_axioms parserFS_inst_ATS_SchedF_DB_axioms parserFS_inst_ATS_Sched_DB0_axioms parserFS_inst_ATS_Sched_axioms )
  done

lemma parserFS_inst_AX_replace_unfixed_scheduler_DB_sound: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d n. maximum_of_domain d n \<longrightarrow> parserFS.derivation_initial G d \<longrightarrow> parserFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserFS_get_unfixed_scheduler_DB G (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G d sUF n) n = sUF))"
  apply(clarsimp)
  apply(rename_tac G d n sUF)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
  apply(simp add: parserFS.replace_unfixed_scheduler_DB_def)
  apply(simp add: parserFS.map_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
   apply(rename_tac G d n sUF)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d n sUF e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      t="right_quotient_word (parserFS_get_unfixed_scheduler_DB G d n) (parserFS_get_unfixed_scheduler_DB G d n)"
      and s="Some []"
      in ssubst)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply(rule right_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac G d n sUF e c)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_set_unfixed_scheduler_DB_def parserFS_set_unfixed_scheduler_def)
  apply(rename_tac G d n sUF)(*strict*)
  apply(rule parserFS.some_position_has_details_before_max_dom)
    apply(rename_tac G d n sUF)(*strict*)
    apply(rule parserFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G d n sUF)(*strict*)
   apply(force)
  apply(rename_tac G d n sUF)(*strict*)
  apply(force)
  done

lemma parserFS_inst_ATS_Sched_DB_axioms: "
  ATS_Sched_DB_axioms valid_parser parserFS_initial_configurations
     parserFS_step_relation parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserFS_set_unfixed_scheduler_DB
     parserFS_get_unfixed_scheduler_DB "
  apply(simp add: ATS_Sched_DB_axioms_def)
  apply(rule parserFS_inst_AX_replace_unfixed_scheduler_DB_sound)
  done

print_locale loc_autFS_5
interpretation "parserFS" : loc_autFS_5
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserFS_configurations"
  (* initial_configurations *)
  "parserFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserFS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserFS_marking_condition"
  (* marked_effect *)
  "parserFS_marked_effect"
  (* unmarked_effect *)
  "parserFS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserFS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserFS_string_state"
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
  "parserFS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler *)
  "parserFS_set_unfixed_scheduler"
  (* get_unfixed_scheduler *)
  "parserFS_get_unfixed_scheduler"
  (* get_fixed_scheduler *)
  "parserFS_conf_fixed"
  (* set_unfixed_scheduler_DB *)
  "parserFS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserFS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserFS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserFS_inst_AX_initial_configuration_belongs parserFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserFS_inst_ATS_axioms parserFS_inst_ATS_String_State_Modification_axioms parserFS_inst_ATS_Language_by_Finite_Derivations_axioms parserFS_inst_ATS_SchedUF_SB_axioms parserFS_inst_ATS_SchedF_SB_axioms parserFS_inst_ATS_Sched_SB_axioms parserFS_inst_ATS_SchedUF_DB_axioms parserFS_inst_ATS_SchedF_DB_axioms parserFS_inst_ATS_Sched_DB0_axioms parserFS_inst_ATS_Sched_DB_axioms parserFS_inst_ATS_Sched_axioms )
  done

lemma parserFS_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> parserFS_get_fixed_scheduler_DB G d n = parserFS_conf_fixed c)))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def get_configuration_def parserFS_get_scheduler_def)
  done

lemma parserFS_inst_ATS_SchedF_SDB_axioms: "
  ATS_SchedF_SDB_axioms valid_parser parserFS_initial_configurations parserFS_step_relation parserFS_conf_fixed parserFS_get_fixed_scheduler_DB "
  apply(simp add: ATS_SchedF_SDB_axioms_def)
  apply(rule parserFS_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler)
  done

lemma parserFS_inst_AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> parserFS_get_unfixed_scheduler (parserFS_set_unfixed_scheduler_DB G d n sUF) = sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n y sUF)(*strict*)
  apply(simp add: parserFS_set_unfixed_scheduler_def parserFS_get_unfixed_scheduler_def parserFS_set_unfixed_scheduler_DB_def get_configuration_def)
  done

lemma parserFS_inst_AX_set_unfixed_scheduler_set_unfixed_scheduler_DB_sound: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> parserFS_set_unfixed_scheduler (the (get_configuration (d n))) sUF = parserFS_set_unfixed_scheduler_DB G d n sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n y sUF)(*strict*)
  apply(simp add: parserFS_get_scheduler_def parserFS_set_unfixed_scheduler_def parserFS_get_fixed_scheduler_DB_def parserFS_get_unfixed_scheduler_def parserFS_set_unfixed_scheduler_DB_def get_configuration_def)
  done

lemma parserFS_inst_AX_state_based_vs_derivation_based_get_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> parserFS_get_unfixed_scheduler_DB G d n = parserFS_get_unfixed_scheduler c)))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_def parserFS_get_unfixed_scheduler_DB_def get_configuration_def)
  done

lemma parserFS_inst_AX_state_based_vs_derivation_based_set_unfixed_scheduler: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n e c. d n = Some (pair e c) \<longrightarrow> (\<forall>sUF. parserFS_set_unfixed_scheduler_DB G d n sUF = parserFS_set_unfixed_scheduler c sUF))))"
  apply(clarsimp)
  apply(rename_tac G d n e c sUF)(*strict*)
  apply(simp add: parserFS_set_unfixed_scheduler_DB_def get_configuration_def parserFS_set_unfixed_scheduler_def)
  done

lemma parserFS_inst_ATS_SchedUF_SDB_axioms: "
  ATS_SchedUF_SDB_axioms valid_parser parserFS_initial_configurations
     parserFS_step_relation parser_unfixed_schedulers
     parser_unfixed_scheduler_extendable parserFS_set_unfixed_scheduler
     parserFS_get_unfixed_scheduler parserFS_set_unfixed_scheduler_DB
     parserFS_get_unfixed_scheduler_DB "
  apply(simp add: ATS_SchedUF_SDB_axioms_def)
  apply(simp add: parserFS_inst_AX_get_unfixed_scheduler_set_unfixed_scheduler_DB_sound parserFS_inst_AX_set_unfixed_scheduler_set_unfixed_scheduler_DB_sound parserFS_inst_AX_state_based_vs_derivation_based_get_unfixed_scheduler parserFS_inst_AX_state_based_vs_derivation_based_set_unfixed_scheduler )
  done

lemma parserFS_inst_AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserFS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (parserFS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] = ATS_SchedUF_SB.get_unfixed_scheduler_nth parserFS_get_unfixed_scheduler d n \<sqsupseteq> [parser_bottom G])))"
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
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def get_configuration_def parserFS.get_unfixed_scheduler_nth_def parserFS_get_unfixed_scheduler_def parserFS_get_scheduler_def)
  done

lemma parserFS_inst_ATS_Sched_SDB_axioms: "
  ATS_Sched_SDB_axioms valid_parser parserFS_initial_configurations
     parserFS_step_relation parser_unfixed_scheduler_extendable
     parserFS_get_unfixed_scheduler parserFS_get_unfixed_scheduler_DB "
  apply(simp add: ATS_Sched_SDB_axioms_def)
  apply(simp add: parserFS_inst_AX_unfixed_scheduler_extendable_get_unfixed_scheduler_equal_get_unfixed_scheduler_DB_on_initial_derivations)
  done

interpretation "parserFS" : loc_autFS_6
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserFS_configurations"
  (* initial_configurations *)
  "parserFS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserFS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserFS_marking_condition"
  (* marked_effect *)
  "parserFS_marked_effect"
  (* unmarked_effect *)
  "parserFS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserFS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserFS_string_state"
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
  "parserFS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler *)
  "parserFS_set_unfixed_scheduler"
  (* get_unfixed_scheduler *)
  "parserFS_get_unfixed_scheduler"
  (* get_fixed_scheduler *)
  "parserFS_conf_fixed"
  (* set_unfixed_scheduler_DB *)
  "parserFS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserFS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserFS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserFS_inst_AX_initial_configuration_belongs parserFS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserFS_inst_ATS_axioms parserFS_inst_ATS_String_State_Modification_axioms parserFS_inst_ATS_Language_by_Finite_Derivations_axioms parserFS_inst_ATS_SchedUF_SB_axioms parserFS_inst_ATS_SchedF_SB_axioms parserFS_inst_ATS_Sched_SB_axioms parserFS_inst_ATS_SchedUF_DB_axioms parserFS_inst_ATS_SchedF_DB_axioms parserFS_inst_ATS_Sched_DB0_axioms parserFS_inst_ATS_Sched_DB_axioms parserFS_inst_ATS_SchedF_SDB_axioms parserFS_inst_ATS_SchedUF_SDB_axioms parserFS_inst_ATS_Sched_SDB_axioms parserFS_inst_ATS_Sched_axioms parserFS_inst_AX_get_scheduler_closed )
  done

theorem parserFS_dependency_between_determinism_properties_main: "
  valid_parser G
  \<Longrightarrow> parserFS.is_forward_target_deterministic_accessible G"
  apply(simp add: parserFS.is_forward_target_deterministic_accessible_def parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e x v)(*strict*)
  apply(case_tac c)
  apply(rename_tac c c1 c2 e x v parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
  apply(case_tac c1)
  apply(rename_tac c c1 c2 e x v parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac c c1 c2 e x v parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa parserFS_conf_fixedb parserFS_conf_stackb parserFS_conf_schedulerb)(*strict*)
  apply(case_tac e)
  apply(rename_tac c c1 c2 e x v parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa parserFS_conf_fixedb parserFS_conf_stackb parserFS_conf_schedulerb rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(clarsimp)
  apply(rename_tac x v parserFS_conf_fixed parserFS_conf_scheduler parserFS_conf_fixeda parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(erule disjE)
   apply(rename_tac x v parserFS_conf_fixed parserFS_conf_scheduler parserFS_conf_fixeda parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(erule disjE)
    apply(rename_tac x v parserFS_conf_fixed parserFS_conf_scheduler parserFS_conf_fixeda parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush)(*strict*)
    apply(clarsimp)
    apply(rename_tac x v parserFS_conf_fixed parserFS_conf_schedulera parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush popnew popnewa)(*strict*)
    apply(subgoal_tac "popnew=popnewa")
     apply(rename_tac x v parserFS_conf_fixed parserFS_conf_schedulera parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush popnew popnewa)(*strict*)
     prefer 2
     apply (metis same_append_eq)
    apply(rename_tac x v parserFS_conf_fixed parserFS_conf_schedulera parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush popnew popnewa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x v parserFS_conf_fixed parserFS_conf_scheduler parserFS_conf_fixeda parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(clarsimp)
  apply(rename_tac x v parserFS_conf_fixed parserFS_conf_scheduler parserFS_conf_fixeda parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(erule disjE)
   apply(rename_tac x v parserFS_conf_fixed parserFS_conf_scheduler parserFS_conf_fixeda parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush)(*strict*)
   apply(clarsimp)
  apply(rename_tac x v parserFS_conf_fixed parserFS_conf_scheduler parserFS_conf_fixeda parserFS_conf_schedulera parserFS_conf_fixedb parserFS_conf_schedulerb rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(clarsimp)
  done

lemmas parserFS_interpretations =
  parser_interpretations
  parserFS_inst_AX_initial_configuration_belongs
  parserFS_inst_AX_step_relation_preserves_belongs
  parserFS_inst_ATS_axioms
  parserFS_inst_ATS_String_State_Modification_axioms
  parserFS_inst_ATS_Language_by_Finite_Derivations_axioms
  parserFS_inst_ATS_SchedUF_SB_axioms
  parserFS_inst_ATS_SchedF_SB_axioms
  parserFS_inst_ATS_Sched_SB_axioms
  parserFS_inst_ATS_SchedUF_DB_axioms
  parserFS_inst_ATS_SchedF_DB_axioms
  parserFS_inst_ATS_Sched_DB0_axioms
  parserFS_inst_ATS_Sched_DB_axioms
  parserFS_inst_ATS_SchedF_SDB_axioms
  parserFS_inst_ATS_SchedUF_SDB_axioms
  parserFS_inst_ATS_Sched_SDB_axioms
  parserFS_inst_ATS_Sched_axioms
  parserFS_inst_AX_get_scheduler_closed

end
