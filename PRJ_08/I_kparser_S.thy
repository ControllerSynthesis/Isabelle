section {*I\_kparser\_S*}
theory
  I_kparser_S

imports
  I_kparser_base

begin

record ('stack, 'event) parserS_conf =
  parserS_conf_stack :: "'stack list"
  parserS_conf_scheduler :: "'event list"

definition parserS_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf set"
  where
    "parserS_configurations G \<equiv>
  {\<lparr>parserS_conf_stack = l, parserS_conf_scheduler = r\<rparr>|
    l r.
    set l \<subseteq> parser_nonterms G
    \<and> set r \<subseteq> parser_events G
    \<and> (\<exists>w. r = w @ [parser_bottom G] \<and> parser_bottom G \<notin> set w)}"

definition parserS_configurations_ALT :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf set"
  where
    "parserS_configurations_ALT G \<equiv>
  {\<lparr>parserS_conf_stack = l, parserS_conf_scheduler = r\<rparr>|
    l r.
    set l \<subseteq> parser_nonterms G
    \<and> r \<in> parser_schedulers G}"

lemma parserS_configurations_ALT_vs_parserS_configurations: "
  valid_parser G
  \<Longrightarrow> parserS_configurations_ALT G = parserS_configurations G"
  apply(simp add: parserS_configurations_ALT_def parserS_configurations_def parser_schedulers_def)
  apply(rule antisym)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac l v)(*strict*)
  apply(simp add: valid_parser_def)
  done

definition parserS_step_relation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> bool"
  where
    "parserS_step_relation M c1 p c2 \<equiv> p \<in> parser_rules M \<and> ((\<exists>x. parserS_conf_stack c1=x@(rule_lpop p) \<and> parserS_conf_stack c2=x@(rule_lpush p)) \<and> (\<exists>x. parserS_conf_scheduler c1=(rule_rpop p)@x \<and> parserS_conf_scheduler c2=(rule_rpush p)@x))"

definition parserS_step_relation_ALT :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> ('stack, 'event) parser_step_label
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> bool"
  where
    "parserS_step_relation_ALT G c1 e c2 \<equiv>
  e \<in> parser_rules G
  \<and> (\<exists>x.
      parserS_conf_stack c1 = x @ rule_lpop e
      \<and> parserS_conf_stack c2 = x @ rule_lpush e)
  \<and> (\<exists>x.
      parserS_conf_scheduler c1 = rule_rpop e @ x
      \<and> parserS_conf_scheduler c2 = rule_rpush e @x)"

lemma parserS_step_relation_ALT_vs_parserS_step_relation: "
  parserS_step_relation_ALT M c1 p c2 = parserS_step_relation M c1 p c2"
  apply(simp add: parserS_step_relation_def parserS_step_relation_ALT_def)
  done

definition parserS_initial_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf set"
  where
    "parserS_initial_configurations G \<equiv>
  {c. parserS_conf_stack c = [parser_initial G]}
  \<inter> parserS_configurations G"

definition parserS_marking_configurations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf set"
  where
    "parserS_marking_configurations G \<equiv>
  {c. \<exists>f \<in> parser_marking G. \<exists>w.
      parserS_conf_stack c = w @ [f]
      \<and> parserS_conf_scheduler c = [parser_bottom G]}
  \<inter> parserS_configurations G"

definition parserS_marking_condition :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf)derivation
  \<Rightarrow> bool"
  where
    "parserS_marking_condition G d \<equiv>
  (\<exists>c. d 0 =Some (pair None c) \<and> c \<in> parserS_configurations G)
  \<and> (\<exists>i e c.
    d i = Some (pair e c)
    \<and> c \<in> parserS_marking_configurations G)"

definition parserS_marking_condition_ALT :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf)derivation
  \<Rightarrow> bool"
  where
    "parserS_marking_condition_ALT G d \<equiv>
  \<exists>i e c.
    d i = Some (pair e c)
    \<and> c \<in> parserS_marking_configurations G"

definition parserS_marked_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf)derivation
  \<Rightarrow> 'event list set"
  where
    "parserS_marked_effect G d \<equiv>
  {w. \<exists>c.
      d 0 = Some (pair None c)
      \<and> w = butlast (parserS_conf_scheduler c)}"

definition parserS_unmarked_effect :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf)derivation
  \<Rightarrow> 'event list set"
  where
    "parserS_unmarked_effect G d \<equiv>
  {w. \<exists>c c' i e v.
      d 0 = Some (pair None c)
      \<and> d i = Some (pair e c')
      \<and> v @ parserS_conf_scheduler c' = parserS_conf_scheduler c
      \<and> w = v @ take (parser_fixed_input_length_recN d i)
                      (butlast (parserS_conf_scheduler c'))}"

definition parserS_get_destinations :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf)derivation_configuration
  \<Rightarrow> ('stack, 'event) parser_destinations set"
  where
    "parserS_get_destinations G der_conf \<equiv>
  case der_conf of pair e c \<Rightarrow>
    state ` set (parserS_conf_stack c)
    \<union> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {rule e'})"

definition parserS_string_state :: "
  ('stack, 'event) parserS_conf
  \<Rightarrow> 'event list"
  where
    "parserS_string_state c \<equiv>
  parserS_conf_scheduler c"

lemma zero_loookahead_no_input_read: "
  valid_bounded_parser P 0
  \<Longrightarrow> parserS_step_relation P c1 e c2
  \<Longrightarrow> e \<in> parser_rules P
  \<Longrightarrow> parserS_conf_scheduler c1 = parserS_conf_scheduler c2"
  apply(subgoal_tac "valid_parser_step_label P e")
   prefer 2
   apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(simp add: valid_parser_step_label_def valid_bounded_parser_def)
  apply(clarsimp)
  apply(rename_tac k w)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac k w)(*strict*)
   apply(simp add: parserS_step_relation_def)
  apply(rename_tac k w)(*strict*)
  apply(force)
  done

lemma at_most_one_lookahead_input_read: "
  valid_bounded_parser P k
  \<Longrightarrow> k \<le> Suc 0
  \<Longrightarrow> parserS_step_relation P c1 e c2
  \<Longrightarrow> e \<in> parser_rules P
  \<Longrightarrow> length(parserS_conf_scheduler c1) > length(parserS_conf_scheduler c2)
  \<Longrightarrow> \<exists>a. parserS_conf_scheduler c1 = a#(parserS_conf_scheduler c2)"
  apply(case_tac k)
   apply(subgoal_tac "parserS_conf_scheduler c1 = parserS_conf_scheduler c2")
    apply(force)
   apply(rule zero_loookahead_no_input_read)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "valid_parser_step_label P e")
   prefer 2
   apply(simp add: valid_bounded_parser_def valid_parser_def)
  apply(simp add: valid_parser_step_label_def valid_bounded_parser_def)
  apply(clarsimp)
  apply(rename_tac k w xa)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac k w xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k w xa)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac k w xa x xb)(*strict*)
  apply(simp add: kPrefix_def)
  apply(case_tac w)
   apply(rename_tac k w xa x xb)(*strict*)
   apply(clarsimp)
  apply(rename_tac k w xa x xb a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac k xa x xb a list)(*strict*)
  apply(case_tac k)
   apply(rename_tac k xa x xb a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac k xa x xb a list nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa x xb a list nat)(*strict*)
  apply(subgoal_tac "nat - length list = 0")
   apply(rename_tac xa x xb a list nat)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac xa x xb a list nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "nat = 0")
   apply(rename_tac xa x xb a list nat)(*strict*)
   prefer 2
   apply(arith)
  apply(rename_tac xa x xb a list nat)(*strict*)
  apply(clarsimp)
  done

lemma parserS_inst_AX_initial_configuration_belongs: "
  \<forall>X. parserS_initial_configurations X \<subseteq> parserS_configurations X"
  apply(simp add: parserS_initial_configurations_def parserS_configurations_def)
  done

lemma parserS_inst_AX_step_relation_preserves_belongs: "
  \<forall>M. valid_parser M \<longrightarrow> (\<forall>c1 e c2. parserS_step_relation M c1 e c2 \<longrightarrow> c1 \<in> parserS_configurations M \<longrightarrow> e \<in> parser_step_labels M \<and> c2 \<in> parserS_configurations M)"
  apply(rule allI)
  apply(rename_tac M)(*strict*)
  apply(rule impI)+
  apply(rule allI)+
  apply(rename_tac M c1 e c2)(*strict*)
  apply(rule impI)+
  apply(simp add: parserS_configurations_def parserS_step_relation_def parser_step_labels_def)
  apply(case_tac c2)
  apply(rename_tac M c1 e c2 parserS_conf_stacka parserS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e x xa w)(*strict*)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac M e x xa w)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   prefer 2
   apply(force)
  apply(rename_tac M e x xa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac M e x xa w k wa xc)(*strict*)
  apply(case_tac e)
  apply(rename_tac M e x xa w k wa xc rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac el1 er1 el2 er2)
  apply(rename_tac M e x xa w k wa xc el1 er1 el2 er2)(*strict*)
  apply(clarsimp)
  apply(rename_tac M x xa w k wa xc el1 el2 er2)(*strict*)
  apply(case_tac xa)
   apply(rename_tac M x xa w k wa xc el1 el2 er2)(*strict*)
   apply(clarsimp)
   apply(rename_tac M x w k wa xc el1 el2 er2)(*strict*)
   apply(case_tac er2)
    apply(rename_tac M x w k wa xc el1 el2 er2)(*strict*)
    apply(clarsimp)
   apply(rename_tac M x w k wa xc el1 el2 er2 a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. er2 = w' @ [x']")
    apply(rename_tac M x w k wa xc el1 el2 er2 a list)(*strict*)
    apply(thin_tac "er2=a#list")
    apply(clarsimp)
    apply(rename_tac M x w k wa xc el1 el2 w' x')(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k - length wa=0")
     apply(rename_tac M x w k wa xc el1 el2 w' x')(*strict*)
     apply(clarsimp)
     apply(case_tac "take k wa")
      apply(rename_tac M x w k wa xc el1 el2 w' x')(*strict*)
      apply(clarsimp)
     apply(rename_tac M x w k wa xc el1 el2 w' x' a list)(*strict*)
     apply(subgoal_tac "\<exists>w' x'. take k wa = w' @ [x']")
      apply(rename_tac M x w k wa xc el1 el2 w' x' a list)(*strict*)
      apply(thin_tac "take k wa=a#list")
      apply(clarsimp)
     apply(rename_tac M x w k wa xc el1 el2 w' x' a list)(*strict*)
     apply(rule NonEmptyListHasTailElem)
     apply(force)
    apply(rename_tac M x w k wa xc el1 el2 w' x')(*strict*)
    apply(clarsimp)
   apply(rename_tac M x w k wa xc el1 el2 er2 a list)(*strict*)
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac M x xa w k wa xc el1 el2 er2 a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
   apply(rename_tac M x xa w k wa xc el1 el2 er2 a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac M x xa w k wa xc el1 el2 er2 a list)(*strict*)
  apply(thin_tac "xa=a#list")
  apply(clarsimp)
  apply(rename_tac M x k wa xc el1 el2 er2 w')(*strict*)
  apply(simp add: kPrefix_def)
  apply(clarsimp)
  apply(case_tac "k - length wa")
   apply(rename_tac M x k wa xc el1 el2 er2 w')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_bottom M \<notin> set (xc@er2)")
    apply(rename_tac M x k wa xc el1 el2 er2 w')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac M x k wa xc el1 el2 er2 w')(*strict*)
   apply(rule_tac
      w="xc"
      and v="er2"
      in elem_set_app)
    apply(rename_tac M x k wa xc el1 el2 er2 w')(*strict*)
    apply(force)
   apply(rename_tac M x k wa xc el1 el2 er2 w')(*strict*)
   apply(force)
  apply(rename_tac M x k wa xc el1 el2 er2 w' nat)(*strict*)
  apply(clarsimp)
  done

interpretation "parserS" : loc_autS_0
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserS_configurations"
  (* initial_configurations *)
  "parserS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserS_marking_condition"
  (* marked_effect *)
  "parserS_marked_effect"
  (* unmarked_effect *)
  "parserS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserS_get_destinations"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserS_inst_AX_initial_configuration_belongs parserS_inst_AX_step_relation_preserves_belongs )
  done

corollary parser_fixed_part_alternative_characterization: "
  valid_parser G
  \<Longrightarrow> parserS.derivation G f
  \<Longrightarrow> f n \<noteq> None
  \<Longrightarrow> parser_fixed_input_length_recN f n = parser_fixed_input_length_foldl f n"
  apply(induct n)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(simp add: parser_fixed_input_length_foldl_def)
   apply(rule_tac
      t="nat_seq (Suc 0) 0"
      and s="[]"
      in ssubst)
    apply(rename_tac y)(*strict*)
    apply(rule nat_seqEmpty)
    apply(force)
   apply(rename_tac y)(*strict*)
   apply(force)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(case_tac "f(Suc n)")
   apply(rename_tac n y)(*strict*)
   apply(clarsimp)
  apply(rename_tac n y a)(*strict*)
  apply(case_tac y)
  apply(rename_tac n y a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n option b)(*strict*)
  apply(subgoal_tac "\<exists>e c. f (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac n option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n b e)(*strict*)
   apply(simp add: parser_fixed_input_length_foldl_def)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc n) = nat_seq (Suc 0) n @ [Suc n]")
    apply(rename_tac n b e)(*strict*)
    apply(clarsimp)
    apply(erule meta_impE)
     apply(rename_tac n b e)(*strict*)
     defer
     apply(rule_tac
      t="foldl (\<lambda>x. case_list undefined (\<lambda>a. case_list undefined (\<lambda>b. case_list (max x a - (a - b)) (\<lambda>aa aaa. undefined)))) 0 (map (\<lambda>n. case f n of Some (pair (Some e) c) \<Rightarrow> [length (rule_rpop e), length (rule_rpush e)]) (nat_seq (Suc 0) n))"
      and s="parser_fixed_input_length_recN f n"
      in ssubst)
      apply(rename_tac n b e)(*strict*)
      apply(force)
     apply(rename_tac n b e)(*strict*)
     apply(force)
    apply(rename_tac n b e)(*strict*)
    apply(rule_tac
      t="[Suc n]"
      and s="(tl(nat_seq n (Suc n)))"
      in ssubst)
     apply(rename_tac n b e)(*strict*)
     apply (metis list.sel(3) natUptTo_n_Sucn)
    apply(rename_tac n b e)(*strict*)
    apply(case_tac n)
     apply(rename_tac n b e)(*strict*)
     apply(clarsimp)
     apply(rename_tac b e)(*strict*)
     apply(rule_tac
      t="nat_seq (Suc 0) (Suc 0)"
      and s="[Suc 0]"
      in ssubst)
      apply(rename_tac b e)(*strict*)
      apply(rule natUptTo_n_n)
     apply(rename_tac b e)(*strict*)
     apply(rule_tac
      t="nat_seq 0 (Suc 0)"
      and s="[0, Suc 0]"
      in ssubst)
      apply(rename_tac b e)(*strict*)
      apply(rule natUptTo_n_Sucn)
     apply(rename_tac b e)(*strict*)
     apply(rule_tac
      t="nat_seq (Suc 0) 0"
      and s="[]"
      in ssubst)
      apply(rename_tac b e)(*strict*)
      apply(rule nat_seqEmpty)
      apply(force)
     apply(rename_tac b e)(*strict*)
     apply(force)
    apply(rename_tac n b e nat)(*strict*)
    apply(rule nat_seq_split)
         apply(rename_tac n b e nat)(*strict*)
         apply(force)
        apply(rename_tac n b e nat)(*strict*)
        apply(force)
       apply(rename_tac n b e nat)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac n b e nat)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n b e nat)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n b e nat)(*strict*)
    apply(force)
   apply(rename_tac n option b)(*strict*)
   apply(rule parserS.pre_some_position_is_some_position_prime)
      apply(rename_tac n option b)(*strict*)
      apply(force)
     apply(rename_tac n option b)(*strict*)
     apply(force)
    apply(rename_tac n option b)(*strict*)
    apply(force)
   apply(rename_tac n option b)(*strict*)
   apply(force)
  apply(rename_tac n b e)(*strict*)
  apply(subgoal_tac "\<exists>e c. f n = Some (pair e c)")
   apply(rename_tac n b e)(*strict*)
   apply(force)
  apply(rename_tac n b e)(*strict*)
  apply(rule parserS.pre_some_position_is_some_position)
    apply(rename_tac n b e)(*strict*)
    apply(force)
   apply(rename_tac n b e)(*strict*)
   apply(force)
  apply(rename_tac n b e)(*strict*)
  apply(force)
  done

definition parserS_entire_input_observed :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> bool"
  where
    "parserS_entire_input_observed G c \<equiv>
  \<exists>d e n.
  parserS.derivation G d
  \<and> parserS.belongs G d
  \<and> parserS.derivation_initial G d
  \<and> maximum_of_domain d n
  \<and> d n = Some (pair e c)
  \<and> parser_fixed_input_length_recN d n = length (parserS_conf_scheduler c)"

definition parserS_entire_input_readable :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> ('stack, 'event) parserS_conf
  \<Rightarrow> bool"
  where
    "parserS_entire_input_readable G c \<equiv>
  \<exists>d e n.
  parserS.derivation G d
  \<and> parserS.belongs G d
  \<and> parserS.derivation_initial G d
  \<and> maximum_of_domain d n
  \<and> d n = Some (pair e c)
  \<and> parserS_conf_scheduler c = [parser_bottom G]"

lemma parserS_inst_AX_string_state_decreases: "
   \<forall>G. valid_parser G \<longrightarrow>
        (\<forall>c1. c1 \<in> parserS_configurations G \<longrightarrow>
              (\<forall>e c2. parserS_step_relation G c1 e c2 \<longrightarrow>
                      (\<exists>w. parserS_string_state c1 = w @ parserS_string_state c2)))"
  apply(clarsimp)
  apply(rename_tac M c1 e c2)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(simp add: parserS_configurations_def)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac M e c2 x xa w)(*strict*)
  apply(simp add: valid_parser_def)
  apply(clarsimp)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac M c1 e c2 x xa)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac M c1 e c2 x xa k w xc)(*strict*)
   apply(rule_tac
      x="xc"
      in exI)
   apply(clarsimp)
  apply(rename_tac M c1 e c2 x xa)(*strict*)
  apply(force)
  done

lemma parserS_inst_lang_sound: "
  (\<forall>M. valid_parser M \<longrightarrow> parserS.unmarked_language M \<subseteq> parser_markers M)"
  apply(simp add: parserS.unmarked_language_def parser_markers_def parserS_unmarked_effect_def parserS_initial_configurations_def parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac M xa d c c' i e v)(*strict*)
  apply(subgoal_tac "parserS.belongs M d")
   apply(rename_tac M xa d c c' i e v)(*strict*)
   prefer 2
   apply(rule parserS.derivation_initial_belongs)
    apply(rename_tac M xa d c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(force)
  apply(rename_tac M xa d c c' i e v)(*strict*)
  apply(subgoal_tac "c \<in> parserS_configurations M")
   apply(rename_tac M xa d c c' i e v)(*strict*)
   prefer 2
   apply(rule parserS.belongs_configurations)
    apply(rename_tac M xa d c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(force)
  apply(rename_tac M xa d c c' i e v)(*strict*)
  apply(subgoal_tac "c' \<in> parserS_configurations M")
   apply(rename_tac M xa d c c' i e v)(*strict*)
   prefer 2
   apply(rule parserS.belongs_configurations)
    apply(rename_tac M xa d c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(force)
  apply(rename_tac M xa d c c' i e v)(*strict*)
  apply(rule_tac
      A="set (butlast(parserS_conf_scheduler c))"
      in set_mp)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(rule_tac
      B="set (parserS_conf_scheduler c)"
      in subset_trans)
    apply(rename_tac M xa d c c' i e v)(*strict*)
    apply(rule trivButLast)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(force)
  apply(rename_tac M xa d c c' i e v)(*strict*)
  apply(erule disjE)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(rule_tac
      A="set v"
      in set_mp)
    apply(rename_tac M xa d c c' i e v)(*strict*)
    apply(rule_tac
      t="parserS_conf_scheduler c"
      and s="v @ parserS_conf_scheduler c'"
      in ssubst)
     apply(rename_tac M xa d c c' i e v)(*strict*)
     apply(force)
    apply(rename_tac M xa d c c' i e v)(*strict*)
    apply(simp add: parserS_configurations_def)
    apply(force)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(force)
  apply(rename_tac M xa d c c' i e v)(*strict*)
  apply(rule_tac
      A="set (take (parser_fixed_input_length_recN d i) (butlast (parserS_conf_scheduler c')))"
      in set_mp)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(rule_tac
      t="parserS_conf_scheduler c"
      and s="v @ parserS_conf_scheduler c'"
      in ssubst)
    apply(rename_tac M xa d c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac M xa d c c' i e v)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
   apply(rename_tac M xa d i e v x l la wa)(*strict*)
   apply(subgoal_tac "x \<in> set wa")
    apply(rename_tac M xa d i e v x l la wa)(*strict*)
    apply(force)
   apply(rename_tac M xa d i e v x l la wa)(*strict*)
   apply(rule_tac
      A="set (take (parser_fixed_input_length_recN d i) wa)"
      in set_mp)
    apply(rename_tac M xa d i e v x l la wa)(*strict*)
    apply(rule set_take_subset)
   apply(rename_tac M xa d i e v x l la wa)(*strict*)
   apply(force)
  apply(rename_tac M xa d c c' i e v)(*strict*)
  apply(force)
  done

definition parserS_get_scheduler :: "
  ('stack, 'event) parserS_conf
  \<Rightarrow> 'event list"
  where
    "parserS_get_scheduler c \<equiv>
  parserS_conf_scheduler c"

definition parserS_get_fixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "parserS_get_fixed_scheduler_DB G d n \<equiv>
  take
    (parser_fixed_input_length_recN d n)
    (parserS_get_scheduler (the (get_configuration (d n))))"

definition parserS_set_unfixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list
  \<Rightarrow> ('stack, 'event) parserS_conf"
  where
    "parserS_set_unfixed_scheduler_DB G d n sUF \<equiv>
  (the (get_configuration (d n)))
    \<lparr>parserS_conf_scheduler := parserS_get_fixed_scheduler_DB G d n @ sUF\<rparr>"

definition parserS_get_unfixed_scheduler_DB :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> 'event list"
  where
    "parserS_get_unfixed_scheduler_DB G d n \<equiv>
  drop
    (parser_fixed_input_length_recN d n)
    (parserS_get_scheduler (the (get_configuration (d n))))"

lemma parserS_inst_AX_marking_condition_implies_existence_of_effect: "
  (\<forall>M. valid_parser M \<longrightarrow>
         (\<forall>f. ATS.derivation_initial parserS_initial_configurations
               parserS_step_relation M f \<longrightarrow>
              parserS_marking_condition M f \<longrightarrow> parserS_marked_effect M f \<noteq> {}))"
  apply(clarsimp)
  apply(rename_tac M f)(*strict*)
  apply(simp add: parserS_marked_effect_def)
  apply(simp add: parserS_marking_condition_def)
  apply(clarsimp)
  done

lemma parser_fixed_input_length_recN_with_derivation_take: "
  i\<le>n
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
  apply(simp add: derivation_take_def)
  apply(case_tac a)
  apply(rename_tac i a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac i option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac i b)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac i option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i b a)(*strict*)
  apply(simp add: derivation_take_def)
  done

lemma parser_fixed_input_length_recN_with_derivation_append: "
  i\<le>n
  \<Longrightarrow> parserS.derivation M d1
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d1 i = Some (pair e1 c1) \<and> d1 (Suc i) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
   apply(rename_tac i a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in parserS.step_detail_before_some_position)
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

lemma parserS_inst_AX_unmarked_effect_persists: "
  \<forall>G. valid_parser G \<longrightarrow>
        (\<forall>d. ATS.derivation_initial parserS_initial_configurations
              parserS_step_relation G d \<longrightarrow>
             (\<forall>n. parserS_unmarked_effect G (derivation_take d n)
                  \<subseteq> parserS_unmarked_effect G d))"
  apply(clarsimp)
  apply(rename_tac G d n x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d n c c' i e v)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac G d n c c' i e v)(*strict*)
   prefer 2
   apply(simp add: derivation_take_def)
  apply(rename_tac G d n c c' i e v)(*strict*)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule conjI)
   apply(rename_tac G d n c c' i e v)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d n c c' i e v)(*strict*)
  apply(rule_tac
      x="c'"
      in exI)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule conjI)
   apply(rename_tac G d n c c' i e v)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac G d n c c' i e v)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(clarsimp)
  apply(rule_tac
      t="(parser_fixed_input_length_recN (derivation_take d n) i)"
      and s="(parser_fixed_input_length_recN d i)"
      in ssubst)
   apply(rename_tac G d n c c' i e v)(*strict*)
   apply(rule parser_fixed_input_length_recN_with_derivation_take)
   apply(force)
  apply(rename_tac G d n c c' i e v)(*strict*)
  apply(force)
  done

lemma parserS_inst_AX_effect_inclusion1: "
  (\<forall>M f. parserS_marking_condition M f \<longrightarrow> parserS_marked_effect M f \<subseteq> parserS_unmarked_effect M f)"
  apply(clarsimp)
  apply(rename_tac M f x)(*strict*)
  apply(simp add: parserS_marking_condition_def parserS_marked_effect_def parserS_unmarked_effect_def parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac M f c i e cb fa w)(*strict*)
  apply(subgoal_tac "\<exists>k\<le>i. (\<forall>i<k. \<not> (\<lambda>i. \<exists>c'. (\<exists>e. f i = Some (pair e c')) \<and> (\<exists>v. v @ parserS_conf_scheduler c' = parserS_conf_scheduler c \<and> butlast (parserS_conf_scheduler c) = v @ take (parser_fixed_input_length_recN f i) (butlast (parserS_conf_scheduler c')))) i) \<and> (\<lambda>i. \<exists>c'. (\<exists>e. f i = Some (pair e c')) \<and> (\<exists>v. v @ parserS_conf_scheduler c' = parserS_conf_scheduler c \<and> butlast (parserS_conf_scheduler c) = v @ take (parser_fixed_input_length_recN f i) (butlast (parserS_conf_scheduler c')))) k")
   apply(rename_tac M f c i e cb fa w)(*strict*)
   prefer 2
   apply(rule ex_least_nat_le_prime)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
  apply(rename_tac M f c i e cb fa w)(*strict*)
  apply(clarsimp)
  apply(rename_tac M f c i e cb fa w k c' ea v)(*strict*)
  apply(rule_tac
      x="c'"
      in exI)
  apply(rule_tac
      x="k"
      in exI)
  apply(clarsimp)
  done

lemma parserS_inst_accept: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserS.derivation_initial G d \<longrightarrow> parserS_marking_condition G d = (\<exists>i e c. d i = Some (pair e c) \<and> c \<in> parserS_marking_configurations G))"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: parserS_marking_condition_def parserS_marking_configurations_def)
  apply(rule order_antisym)
   apply(rename_tac G d)(*strict*)
   apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d i e c f w)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac G d i e c f w)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d i e c f w ca)(*strict*)
   apply(rule parserS.belongs_configurations)
    apply(rename_tac G d i e c f w ca)(*strict*)
    apply(rule parserS.derivation_initial_belongs)
     apply(rename_tac G d i e c f w ca)(*strict*)
     apply(force)
    apply(rename_tac G d i e c f w ca)(*strict*)
    apply(force)
   apply(rename_tac G d i e c f w ca)(*strict*)
   apply(force)
  apply(rename_tac G d i e c f w)(*strict*)
  apply(rule parserS.some_position_has_details_at_0)
  apply(simp add: parserS.derivation_initial_def)
  apply(force)
  done

lemma parserS_inst_AX_marking_can_not_be_disabled: "
  (\<forall>G d. (\<exists>n. parserS_marking_condition G (derivation_take d n)) \<longrightarrow> parserS_marking_condition G d)"
  apply(clarsimp)
  apply(rename_tac G d n)(*strict*)
  apply(simp add: parserS_marking_condition_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac G d n c i e ca)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac G d n c i e ca)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G d n c i e ca)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="ca"
      in exI)
  apply(force)
  done

lemma parserS_inst_AX_marked_effect_persists: "
  (\<forall>G d n. parserS_marked_effect G (derivation_take d n) \<subseteq> parserS_marked_effect G d)"
  apply(simp add: parserS_marked_effect_def derivation_take_def)
  done

lemma parserS_inst_lang_finite: "
  (\<forall>G. valid_parser G \<longrightarrow> parserS.finite_marked_language G = parserS.marked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserS.finite_marked_language_def parserS.marked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G x d c i e ca)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule conjI)
   apply(rename_tac G x d c i e ca)(*strict*)
   apply (metis parserS.derivation_take_preserves_derivation_initial)
  apply(rename_tac G x d c i e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G x d c i e ca)(*strict*)
   apply(simp add: parserS_marked_effect_def derivation_take_def)
  apply(rename_tac G x d c i e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G x d c i e ca)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(simp add: derivation_take_def)
  apply(rename_tac G x d c i e ca)(*strict*)
  apply(rule conjI)
   apply(rename_tac G x d c i e ca)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="ca"
      in exI)
   apply(simp add: derivation_take_def)
  apply(rename_tac G x d c i e ca)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply (metis not_Some_eq maximum_of_domain_derivation_take)
  done

lemma parserS_inst_AX_unmarked_language_finite: "
  (\<forall>G. valid_parser G \<longrightarrow> parserS.finite_unmarked_language G = parserS.unmarked_language G)"
  apply(clarsimp)
  apply(rename_tac G)(*strict*)
  apply(simp add: parserS.finite_unmarked_language_def parserS.unmarked_language_def)
  apply(rule order_antisym)
   apply(rename_tac G)(*strict*)
   apply(clarsimp)
   apply(rename_tac G x d n)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G)(*strict*)
  apply(clarsimp)
  apply(rename_tac G x d)(*strict*)
  apply(simp add: parserS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G d c c' i e v)(*strict*)
  apply(rule_tac
      x="derivation_take d i"
      in exI)
  apply(rule conjI)
   apply(rename_tac G d c c' i e v)(*strict*)
   apply (metis parserS.derivation_take_preserves_derivation_initial)
  apply(rename_tac G d c c' i e v)(*strict*)
  apply(rule conjI)
   apply(rename_tac G d c c' i e v)(*strict*)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac G d c c' i e v)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G d c c' i e v)(*strict*)
   apply(rule_tac
      x="c'"
      in exI)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule conjI)
    apply(rename_tac G d c c' i e v)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac G d c c' i e v)(*strict*)
   apply(rule_tac
      x="v"
      in exI)
   apply(rule conjI)
    apply(rename_tac G d c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac G d c c' i e v)(*strict*)
   apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d i) i"
      and s="parser_fixed_input_length_recN d i"
      in ssubst)
    apply(rename_tac G d c c' i e v)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G d c c' i e v)(*strict*)
   apply (metis parser_fixed_input_length_recN_with_derivation_take le_refl)
  apply(rename_tac G d c c' i e v)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply (metis not_Some_eq maximum_of_domain_derivation_take)
  done

lemma parserS_inst_ATS_axioms: "
  ATS_Language_axioms valid_parser parserS_initial_configurations
     parserS_step_relation parser_markers parserS_marking_condition
     parserS_marked_effect parserS_unmarked_effect "
  apply(simp add: ATS_Language_axioms_def)
  apply(simp add: parserS_inst_AX_marking_condition_implies_existence_of_effect parserS_inst_lang_sound parserS_inst_AX_effect_inclusion1 parserS_inst_AX_unmarked_effect_persists )
  done

lemma parserS_inst_ATS_Language_by_Finite_Derivations_axioms: "
  ATS_Language_by_Finite_Derivations_axioms valid_parser
     parserS_initial_configurations parserS_step_relation
     parserS_marking_condition parserS_marked_effect parserS_unmarked_effect"
  apply(simp add: ATS_Language_by_Finite_Derivations_axioms_def)
  apply(simp add: parserS_inst_lang_finite parserS_inst_AX_unmarked_language_finite )
  done

lemma parserS_inst_ATS_String_State_Modification_axioms: "
  ATS_String_State_Modification_axioms valid_parser parserS_configurations
     parserS_step_relation True parserS_string_state"
  apply(simp add: ATS_String_State_Modification_axioms_def)
  apply(simp add: parserS_inst_AX_string_state_decreases )
  done

interpretation "parserS" : loc_autS_1
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserS_configurations"
  (* initial_configurations *)
  "parserS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserS_marking_condition"
  (* marked_effect *)
  "parserS_marked_effect"
  (* unmarked_effect *)
  "parserS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserS_string_state"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserS_inst_AX_initial_configuration_belongs parserS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserS_inst_ATS_Language_by_Finite_Derivations_axioms parserS_inst_ATS_String_State_Modification_axioms parserS_inst_ATS_axioms )
  done

lemma PARSER_UnseenPartStrictlyDecreases: "
  valid_parser P
  \<Longrightarrow> parserS.belongs P d
  \<Longrightarrow> parserS.derivation P d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> d (i+j) = Some (pair e' c')
  \<Longrightarrow> length (parserS_conf_scheduler c) - (parser_fixed_input_length_recN d i) \<ge> length (parserS_conf_scheduler c') - (parser_fixed_input_length_recN d (i+j))"
  apply(induct j arbitrary: e' c')
   apply(rename_tac e' c')(*strict*)
   apply(clarsimp)
  apply(rename_tac j e' c')(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d (i+j) = Some (pair e1 c1) \<and> d (Suc (i+j)) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
   apply(rename_tac j e' c')(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc (i+j)"
      in parserS.step_detail_before_some_position)
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
      j="length (parserS_conf_scheduler c1) - parser_fixed_input_length_recN d (i + j)"
      in le_trans)
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(thin_tac "length (parserS_conf_scheduler c1) - parser_fixed_input_length_recN d (i + j) \<le> length (parserS_conf_scheduler c) - parser_fixed_input_length_recN d i")
  apply(rename_tac j c' e1 e2 c1)(*strict*)
  apply(subgoal_tac "e2 \<in> parser_rules P")
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: parserS.belongs_def)
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
  apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c')")
   apply(rename_tac j c' e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
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
  apply(simp add: parserS_string_state_def)
  apply(subgoal_tac "length w = (length (rule_rpop e2) - length (rule_rpush e2))")
   apply(rename_tac j c' e1 e2 c1 w)(*strict*)
   apply(force)
  apply(rename_tac j c' e1 e2 c1 w)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac j c' e1 e2 c1 w x xa)(*strict*)
  apply(rule_tac
      t="rule_rpop e2"
      and s="w @ rule_rpush e2"
      in ssubst)
   apply(rename_tac j c' e1 e2 c1 w x xa)(*strict*)
   apply(force)
  apply(rename_tac j c' e1 e2 c1 w x xa)(*strict*)
  apply(rule_tac
      t="length (w@rule_rpush e2)"
      and s="length w + length (rule_rpush e2)"
      in ssubst)
   apply(rename_tac j c' e1 e2 c1 w x xa)(*strict*)
   apply(simp (no_asm_use))
  apply(rename_tac j c' e1 e2 c1 w x xa)(*strict*)
  apply(simp (no_asm_use))
  done

lemma parserS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient: "
  valid_parser G
  \<Longrightarrow> parserS.derivation G d
  \<Longrightarrow> parserS.belongs G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> i \<le> j
  \<Longrightarrow> j \<le> n
  \<Longrightarrow> suffix (parserS_get_unfixed_scheduler_DB G d i) (parserS_get_unfixed_scheduler_DB G d j)"
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
      b="parserS_get_unfixed_scheduler_DB G d (Suc i)"
      in suffix_trans)
   apply(rename_tac x i j y)(*strict*)
   defer
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(thin_tac "parserS_get_unfixed_scheduler_DB G d (Suc i) \<sqsupseteq> parserS_get_unfixed_scheduler_DB G d j")
  apply(simp add: parserS_get_unfixed_scheduler_DB_def suffix_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
   apply(rename_tac x i j y)(*strict*)
   prefer 2
   apply(rule_tac
      m="n"
      in parserS.step_detail_before_some_position)
     apply(rename_tac x i j y)(*strict*)
     apply(force)
    apply(rename_tac x i j y)(*strict*)
    apply(force)
   apply(rename_tac x i j y)(*strict*)
   apply(force)
  apply(rename_tac x i j y)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i j y e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_get_scheduler_def get_configuration_def parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
  apply(subgoal_tac "length (rule_rpop e2) \<ge> length (rule_rpush e2)")
   apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
   prefer 2
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac x i j y e1 e2 c1 c2 xa xb k w xd)(*strict*)
    apply(rule_tac
      j="length (xd @ rule_rpush e2)"
      in le_trans)
     apply(rename_tac x i j y e1 e2 c1 c2 xa xb k w xd)(*strict*)
     apply (metis le_iff_add length_append add.commute)
    apply(rename_tac x i j y e1 e2 c1 c2 xa xb k w xd)(*strict*)
    apply(force)
   apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
   apply(simp add: valid_parser_def)
  apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
  apply(case_tac "(parser_fixed_input_length_recN d i) \<le> length (rule_rpop e2)")
   apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(subgoal_tac "max (parser_fixed_input_length_recN d i) (length (rule_rpop e2)) = parser_fixed_input_length_recN d i")
    apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i j y e1 e2 c1 c2 xa xb)(*strict*)
  apply(clarsimp)
  done

lemma parserS_inst_AX_get_scheduler_closed: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>c. c \<in> parserS_configurations G \<longrightarrow> parserS_get_scheduler c \<in> parser_schedulers G))"
  apply(simp add: parserS_configurations_def parser_schedulers_def parserS_get_scheduler_def)
  apply(clarsimp)
  done

lemma parserS_inst_AX_get_unfixed_scheduler_DB_extendable_on_initial_configuration: "
  \<forall>G. valid_parser G \<longrightarrow>
  (\<forall>d. ATS.derivation_initial parserS_initial_configurations
  parserS_step_relation G d \<longrightarrow>
  parserS_get_unfixed_scheduler_DB G d 0 \<sqsupseteq> [parser_bottom G])"
  apply(clarsimp)
  apply(rename_tac G d)(*strict*)
  apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac G d)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "c \<in> parserS_configurations G")
    apply(rename_tac G d c)(*strict*)
    apply(simp add: parserS_configurations_def parserS_get_scheduler_def)
    apply(clarsimp)
    apply(rename_tac G d l w)(*strict*)
    apply(simp add: suffix_def)
   apply(rename_tac G d c)(*strict*)
   apply (metis parserS.belongs_configurations parserS.derivation_initial_belongs)
  apply(rename_tac G d)(*strict*)
  apply (metis parserS.derivation_initial_is_derivation parserS.some_position_has_details_at_0)
  done

lemma parserS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserS.derivation G d \<longrightarrow> (\<forall>c. d 0 = Some (pair None c) \<longrightarrow> c \<in> parserS_initial_configurations G \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserS_set_unfixed_scheduler_DB G d 0 sUF \<in> parserS_initial_configurations G))))"
  apply(clarsimp)
  apply(rename_tac G d c sUF)(*strict*)
  apply(simp add: suffix_def get_configuration_def parserS_set_unfixed_scheduler_DB_def parserS_initial_configurations_def parserS_configurations_def parserS_get_fixed_scheduler_DB_def parser_unfixed_schedulers_def parser_schedulers_def suffix_closure_def)
  apply(clarsimp)
  done

lemma parserS_inst_AX_unfixed_scheduler_right_quotient_closed_on_extendable_get_unfixed_scheduler_DB: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> (\<forall>j. parserS_get_unfixed_scheduler_DB G d j \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>i\<le>j. j \<le> n \<longrightarrow> the (right_quotient_word (parserS_get_unfixed_scheduler_DB G d i) (parserS_get_unfixed_scheduler_DB G d j)) \<in> parser_scheduler_fragments G)))))"
  apply(clarsimp)
  apply(rename_tac G d n y j i)(*strict*)
  apply(subgoal_tac "suffix (parserS_get_unfixed_scheduler_DB G d i) (parserS_get_unfixed_scheduler_DB G d j)")
   apply(rename_tac G d n y j i)(*strict*)
   prefer 2
   apply(rule parserS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient)
        apply(rename_tac G d n y j i)(*strict*)
        apply(force)
       apply(rename_tac G d n y j i)(*strict*)
       apply(simp add: parserS.derivation_initial_def)
      apply(rename_tac G d n y j i)(*strict*)
      apply (metis parserS.derivation_initial_belongs)
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
   apply(subgoal_tac "cb \<in> parserS_configurations G")
    apply(rename_tac G d n y j i c ca e cb)(*strict*)
    apply(simp add: parser_scheduler_fragments_def parserS_get_unfixed_scheduler_DB_def parserS_get_scheduler_def get_configuration_def parserS_configurations_def)
    apply(clarsimp)
    apply(rename_tac G d n y j i c ca e l w)(*strict*)
    apply(case_tac "(parser_fixed_input_length_recN d i - length w)")
     apply(rename_tac G d n y j i c ca e l w)(*strict*)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac G d n y j i c ca e l w)(*strict*)
      apply(rule_tac
      B="set(ca@c)"
      in subset_trans)
       apply(rename_tac G d n y j i c ca e l w)(*strict*)
       apply(force)
      apply(rename_tac G d n y j i c ca e l w)(*strict*)
      apply(rule_tac
      t="ca @ c"
      and s="drop (parser_fixed_input_length_recN d i) w"
      in ssubst)
       apply(rename_tac G d n y j i c ca e l w)(*strict*)
       apply(force)
      apply(rename_tac G d n y j i c ca e l w)(*strict*)
      apply(rule_tac
      B="set w"
      in subset_trans)
       apply(rename_tac G d n y j i c ca e l w)(*strict*)
       apply(rule set_drop_subset)
      apply(rename_tac G d n y j i c ca e l w)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i c ca e l w)(*strict*)
     apply(rule_tac
      B="set(ca@c)"
      in nset_mp)
      apply(rename_tac G d n y j i c ca e l w)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i c ca e l w)(*strict*)
     apply(rule_tac
      t="ca @ c"
      and s="drop (parser_fixed_input_length_recN d i) w"
      in ssubst)
      apply(rename_tac G d n y j i c ca e l w)(*strict*)
      apply(force)
     apply(rename_tac G d n y j i c ca e l w)(*strict*)
     apply (metis in_set_dropD)
    apply(rename_tac G d n y j i c ca e l w nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G d n y j i c ca e cb)(*strict*)
   apply (metis parserS.belongs_configurations parserS.derivation_initial_belongs)
  apply(rename_tac G d n y j i c ca)(*strict*)
  apply(rule parserS.pre_some_position_is_some_position)
    apply(rename_tac G d n y j i c ca)(*strict*)
    apply(simp add: parserS.derivation_initial_def)
    apply(force)
   apply(rename_tac G d n y j i c ca)(*strict*)
   apply(force)
  apply(rename_tac G d n y j i c ca)(*strict*)
  apply(force)
  done

lemma parserS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserS.derivation G d \<longrightarrow> parserS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserS_get_fixed_scheduler_DB G d n \<in> parser_fixed_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserS_get_fixed_scheduler_DB_def get_configuration_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b)(*strict*)
  apply(subgoal_tac "b \<in> parserS_configurations G")
   apply(rename_tac G d n option b)(*strict*)
   prefer 2
   apply (metis parserS.belongs_configurations)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: parserS_get_scheduler_def parserS_configurations_def parser_fixed_schedulers_def)
  apply(clarsimp)
  apply(rename_tac G d n option l w)(*strict*)
  apply(simp add: prefix_closure_def prefix_def parser_schedulers_def)
  apply(case_tac "(parser_fixed_input_length_recN d n - length w)")
   apply(rename_tac G d n option l w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="take (parser_fixed_input_length_recN d n) w @ [parser_bottom G]"
      in exI)
   apply(clarsimp)
   apply (metis in_set_takeD le_fun_def set_take_subset subset_trans)
  apply(rename_tac G d n option l w nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="w @ [parser_bottom G]"
      in exI)
  apply(clarsimp)
  done

lemma parserS_inst_AX_get_fixed_scheduler_DB_restrict: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>x n. x \<le> n \<longrightarrow> (\<forall>d1. parserS.derivation G d1 \<longrightarrow> (\<forall>d2. parserS_get_fixed_scheduler_DB G (derivation_append d1 d2 n) x = parserS_get_fixed_scheduler_DB G d1 x)))"
  apply(clarsimp)
  apply(rename_tac G x n d1 d2)(*strict*)
  apply(simp add: parserS_get_fixed_scheduler_DB_def parserS_get_scheduler_def)
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
  apply (metis parser_fixed_input_length_recN_with_derivation_append)
  done

lemma parserS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserS.derivation_initial G d \<longrightarrow> (\<forall>n m. n \<le> m \<longrightarrow> parserS_get_unfixed_scheduler_DB G d n = parserS_get_unfixed_scheduler_DB G (derivation_take d m) n))"
  apply(clarsimp)
  apply(rename_tac G d n m)(*strict*)
  apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d m) n"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
   apply(rename_tac G d n m)(*strict*)
   defer
   apply(simp add: derivation_take_def)
  apply(rename_tac G d n m)(*strict*)
  apply (metis parser_fixed_input_length_recN_with_derivation_take)
  done

lemma parserS_inst_AX_get_unfixed_scheduler_DB_closed: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserS.derivation G d \<longrightarrow> parserS.belongs G d \<longrightarrow> (\<forall>n. (\<exists>e c. d n = Some (pair e c)) \<longrightarrow> parserS_get_unfixed_scheduler_DB G d n \<in> parser_unfixed_schedulers G))"
  apply(clarsimp)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parser_unfixed_schedulers_def parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(rule drop_suffix_closure)
  apply(simp add: parserS_get_scheduler_def)
  apply(subgoal_tac "c \<in> parserS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply(rule parserS.belongs_configurations)
    apply(rename_tac G d n e c)(*strict*)
    apply(force)
   apply(rename_tac G d n e c)(*strict*)
   apply(force)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserS_configurations_def parser_schedulers_def)
  apply(clarsimp)
  done

lemma PARSER_possibility_of_restriction_EffectOverhead_prime: "
  valid_parser M
  \<Longrightarrow> parserS.belongs M d
  \<Longrightarrow> parserS.derivation M d
  \<Longrightarrow> d m = Some (pair e c)
  \<Longrightarrow> parser_fixed_input_length_recN d m \<le> length (parserS_conf_scheduler c)"
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d m = Some (pair e1 c1) \<and> d (Suc m) = Some (pair (Some e2) c2) \<and> parserS_step_relation M c1 e2 c2")
   apply(rename_tac m e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc m"
      in parserS.step_detail_before_some_position)
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
   apply(simp add: parserS.belongs_def)
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
  apply(case_tac c1)
  apply(rename_tac m c e1 e2 c1 parserS_conf_stack parserS_conf_schedulera)(*strict*)
  apply(rename_tac c1l c1r)
  apply(rename_tac m c e1 e2 c1 c1l c1r)(*strict*)
  apply(case_tac c)
  apply(rename_tac m c e1 e2 c1 c1l c1r parserS_conf_stack parserS_conf_schedulera)(*strict*)
  apply(rename_tac c2l c2r)
  apply(rename_tac m c e1 e2 c1 c1l c1r c2l c2r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac m c e1 e2 c1 c1l c1r c2l c2r rule_lpop rule_rpopa rule_lpush rule_rpusha)(*strict*)
  apply(rename_tac l1 r1 cons_l2 r2)
  apply(rename_tac m c e1 e2 c1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(clarsimp)
  apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
  apply(case_tac "parser_fixed_input_length_recN d m \<ge> length r1")
   apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
   apply(rule_tac
      t="max (parser_fixed_input_length_recN d m) (length r1)"
      and s="parser_fixed_input_length_recN d m"
      in ssubst)
    apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
    apply(force)
   apply(rename_tac m e1 c1l c1r c2l c2r l1 r1 cons_l2 r2)(*strict*)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac m e1 l1 r1 cons_l2 r2 x xa)(*strict*)
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
  done

lemma parserS_inst_AX_schedF_db_extendable_translates_backwards: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d1. parserS.derivation G d1 \<longrightarrow> parserS.belongs G d1 \<longrightarrow> (\<forall>n x. (\<exists>y. d1 (n + x) = Some y) \<longrightarrow> \<not> parserS_get_fixed_scheduler_DB G d1 (n + x) \<sqsupseteq> [parser_bottom G] \<longrightarrow> \<not> parserS_get_fixed_scheduler_DB G d1 n \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G d1 n x y)(*strict*)
  apply(simp add: parserS_get_fixed_scheduler_DB_def)
  apply(case_tac y)
  apply(rename_tac G d1 n x y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d1 n x option b)(*strict*)
  apply(subgoal_tac "\<exists>e c. d1 n = Some (pair e c)")
   apply(rename_tac G d1 n x option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(subgoal_tac "parser_fixed_input_length_recN d1 n = length (parserS_get_scheduler c)")
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_fixed_input_length_recN d1 (n+x) = length (parserS_get_scheduler b)")
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(subgoal_tac "b \<in> parserS_configurations G")
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(simp add: parserS_configurations_def suffix_def parserS_get_scheduler_def)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply (metis parserS.belongs_configurations)
    apply(rename_tac G d1 n x option b e c)(*strict*)
    prefer 2
    apply(subgoal_tac "c \<in> parserS_configurations G")
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(subgoal_tac "parser_fixed_input_length_recN d1 n \<le> length (parserS_conf_scheduler c)")
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(simp add: parserS_configurations_def suffix_def parserS_get_scheduler_def)
      apply(clarsimp)
      apply(rename_tac G d1 n x option b e ca l w)(*strict*)
      apply(case_tac "parser_fixed_input_length_recN d1 n - length w")
       apply(rename_tac G d1 n x option b e ca l w)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "parser_bottom G \<in> set w")
        apply(rename_tac G d1 n x option b e ca l w)(*strict*)
        apply(force)
       apply(rename_tac G d1 n x option b e ca l w)(*strict*)
       apply (metis butlast_if_match_direct butlast_if_match_direct2_prime in_set_takeD kPrefix_def not_Cons_self2 self_append_conv)
      apply(rename_tac G d1 n x option b e ca l w nat)(*strict*)
      apply(clarsimp)
      apply(rename_tac G d1 n x option b e ca l nat)(*strict*)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac G d1 n x option b e c)(*strict*)
        apply(force)
       apply(rename_tac G d1 n x option b e c)(*strict*)
       apply(force)
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(force)
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply (metis parserS.belongs_configurations)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   prefer 2
   apply(rename_tac G d1 n x option b)(*strict*)
   apply(rule parserS.pre_some_position_is_some_position)
     apply(rename_tac G d1 n x option b)(*strict*)
     apply(simp add: parserS.derivation_initial_def)
    apply(rename_tac G d1 n x option b)(*strict*)
    apply(force)
   apply(rename_tac G d1 n x option b)(*strict*)
   apply(force)
  apply(rename_tac G d1 n x option b e c)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d1 (n+x) \<le> length (parserS_conf_scheduler b)")
   apply(rename_tac G d1 n x option b e c)(*strict*)
   prefer 2
   apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(rename_tac G d1 n x option b e c)(*strict*)
      apply(force)
     apply(rename_tac G d1 n x option b e c)(*strict*)
     apply(force)
    apply(rename_tac G d1 n x option b e c)(*strict*)
    apply(force)
   apply(rename_tac G d1 n x option b e c)(*strict*)
   apply(force)
  apply(rename_tac G d1 n x option b e c)(*strict*)
  apply(subgoal_tac "length (parserS_conf_scheduler c) - (parser_fixed_input_length_recN d1 n) \<ge> length (parserS_conf_scheduler b) - (parser_fixed_input_length_recN d1 (n+x))")
   apply(rename_tac G d1 n x option b e c)(*strict*)
   prefer 2
   apply(rule PARSER_UnseenPartStrictlyDecreases)
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
  apply(simp add: parserS_get_scheduler_def)
  done

lemma parserS_inst_ATS_SchedUF_DB_axioms: "
  ATS_SchedUF_DB_axioms valid_parser parserS_configurations
     parserS_initial_configurations parser_step_labels parserS_step_relation
     parser_scheduler_fragments parser_unfixed_schedulers
     right_quotient_word parser_unfixed_scheduler_extendable
     parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_SchedUF_DB_axioms_def)
  apply(rule conjI)
   apply(simp add: parserS_inst_AX_unfixed_scheduler_right_quotient_closed_on_extendable_get_unfixed_scheduler_DB )
  apply(rule conjI)
   apply(simp add: parserS_inst_AX_get_unfixed_scheduler_DB_extendable_on_initial_configuration )
  apply(rule conjI)
   apply(simp add: parserS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations parserS_inst_AX_get_unfixed_scheduler_DB_closed )
  apply(rule conjI)
   apply(simp add: parserS_inst_AX_set_unfixed_scheduler_DB_preserves_initial_configurations parserS_inst_AX_get_unfixed_scheduler_DB_closed )
  apply(rule parserS_inst_AX_get_unfixed_scheduler_DB_invariant_under_derivation_take)
  done

lemma parserS_inst_ATS_SchedF_DB_axioms: "
  ATS_SchedF_DB_axioms valid_parser parserS_configurations
     parser_step_labels parserS_step_relation parser_fixed_schedulers
     parser_fixed_scheduler_extendable parserS_get_fixed_scheduler_DB"
  apply(simp add: ATS_SchedF_DB_axioms_def)
  apply(simp add: parserS_inst_AX_get_fixed_scheduler_DB_in_fixed_schedulers parserS_inst_AX_get_fixed_scheduler_DB_restrict parserS_inst_AX_schedF_db_extendable_translates_backwards )
  done

lemma parserS_inst_ATS_Sched_axioms: "
  ATS_Sched_axioms valid_parser parserS_configurations
     parser_scheduler_fragments parser_empty_scheduler_fragment (@)
     parser_schedulers parser_schedulers parser_empty_scheduler
     parserS_get_scheduler (@)"
  apply(simp add: ATS_Sched_axioms_def)
  apply(simp add: parser_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed parser_inst_AX_extend_scheduler_closed parser_inst_AX_empty_scheduler_in_schedulers parserS_inst_AX_get_scheduler_closed )
  done

interpretation "parserS" : loc_autS_2
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserS_configurations"
  (* initial_configurations *)
  "parserS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserS_marking_condition"
  (* marked_effect *)
  "parserS_marked_effect"
  (* unmarked_effect *)
  "parserS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserS_string_state"
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
  "parserS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "parserS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserS_inst_AX_initial_configuration_belongs parserS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserS_inst_ATS_Language_by_Finite_Derivations_axioms parserS_inst_ATS_String_State_Modification_axioms parserS_inst_ATS_axioms parserS_inst_ATS_SchedUF_DB_axioms parserS_inst_ATS_SchedF_DB_axioms parserS_inst_ATS_Sched_axioms )
  done

lemma parserS_inst_AX_sched_modification_preserves_steps: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>dh n. maximum_of_domain dh n \<longrightarrow> parserS.derivation G dh \<longrightarrow> parserS.belongs G dh \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> (\<exists>sF. \<not> sF \<sqsupseteq> [parser_bottom G]) \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>m e2 c2. dh (Suc m) = Some (pair (Some e2) c2) \<longrightarrow> (\<forall>e1 c1. dh m = Some (pair e1 c1) \<longrightarrow> parserS_step_relation G c1 e2 c2 \<longrightarrow> parserS_step_relation G (parserS_set_unfixed_scheduler_DB G dh m (the (right_quotient_word (parserS_get_unfixed_scheduler_DB G dh m) (parserS_get_unfixed_scheduler_DB G dh n)) @ sUF)) e2 (parserS_set_unfixed_scheduler_DB G dh (Suc m) (the (right_quotient_word (parserS_get_unfixed_scheduler_DB G dh (Suc m)) (parserS_get_unfixed_scheduler_DB G dh n)) @ sUF))))))"
  apply(clarsimp)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1)(*strict*)
  apply(simp add: get_configuration_def parserS_set_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
  apply(subgoal_tac "Suc m \<le> n")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
   prefer 2
   apply (metis less_eq_Suc_le_raw not_Some_eq not_less_eq parserS.no_some_beyond_maximum_of_domain)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
  apply(subgoal_tac "suffix (parserS_get_unfixed_scheduler_DB G dh m) (parserS_get_unfixed_scheduler_DB G dh (Suc m))")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
   prefer 2
   apply(rule parserS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient)
        apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
        apply(force)
       apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
       apply(force)
      apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
      apply(force)
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
  apply(subgoal_tac "suffix (parserS_get_unfixed_scheduler_DB G dh (Suc m)) (parserS_get_unfixed_scheduler_DB G dh n)")
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
   prefer 2
   apply(rule_tac
      n="n"
      in parserS_inst_hlp_get_unfixed_scheduler_DB_constructs_right_quotient)
        apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
        apply(force)
       apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
       apply(force)
      apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
      apply(force)
     apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
   apply(force)
  apply(rename_tac G dh n sUF sF m e2 c2 e1 c1 x xa)(*strict*)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
  apply(rule_tac
      t="right_quotient_word (ca @ cb @ parserS_get_unfixed_scheduler_DB G dh n) (parserS_get_unfixed_scheduler_DB G dh n)"
      and s="Some (ca@cb)"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
  apply(rule_tac
      t="right_quotient_word (ca @ parserS_get_unfixed_scheduler_DB G dh n) (parserS_get_unfixed_scheduler_DB G dh n)"
      and s="Some ca"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="right_quotient_word (cb @ parserS_get_unfixed_scheduler_DB G dh n) (parserS_get_unfixed_scheduler_DB G dh n)"
      and s="Some cb"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(simp add: parserS_get_scheduler_def)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
  apply(case_tac "parser_fixed_input_length_recN dh m - length (rule_rpop e2)")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "max (parser_fixed_input_length_recN dh m) (length (rule_rpop e2)) = length (rule_rpop e2)")
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb)(*strict*)
   apply(clarsimp)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
   apply(rule_tac
      t="length (xc @ rule_rpush e2) - length (rule_rpush e2)"
      and s="length xc"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
    apply (metis append_length_inc diff_diff_cancel drop_prefix_closureise length_drop)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
   apply(rule_tac
      t="length (xc @ rule_rpush e2) - length xc"
      and s="length(rule_rpush e2)"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
    apply (metis drop_prefix_closureise length_drop)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
   apply(rule_tac
      t="take (length (rule_rpush e2)) (rule_rpush e2)"
      and s="rule_rpush e2"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
    apply (metis le_refl take_all)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
   apply(rule_tac
      x="cb @ c @ [parser_bottom G]"
      in exI)
   apply(clarsimp)
   apply(subgoal_tac "prefix (drop (parser_fixed_input_length_recN dh m) (kPrefix k (w @ [parser_bottom G]))) ca \<or> prefix ca (drop (parser_fixed_input_length_recN dh m) (kPrefix k (w @ [parser_bottom G])))")
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
   apply(erule disjE)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
   apply(subgoal_tac "drop (length (kPrefix k (w @ [parser_bottom G])) - (length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2))) (rule_rpush e2) = []")
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
   apply(rule_tac
      t="length (xc @ rule_rpush e2) - length (rule_rpush e2)"
      and s="length xc"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
    apply (metis append_length_inc diff_diff_cancel drop_prefix_closureise length_drop)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
   apply(rule_tac
      t="length (xc @ rule_rpush e2) - length xc"
      and s="length(rule_rpush e2)"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
    apply (metis drop_prefix_closureise length_drop)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb k w xc cc)(*strict*)
   apply (metis append_Nil2 append_eq_conv_conj)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "max (parser_fixed_input_length_recN dh m) (length (rule_rpop e2)) = parser_fixed_input_length_recN dh m")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat)(*strict*)
  apply(clarsimp)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
  apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
  apply(rule_tac
      t="length (xc @ rule_rpush e2) - length (rule_rpush e2)"
      and s="length xc"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply (metis append_length_inc diff_diff_cancel drop_prefix_closureise length_drop)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
  apply(rule_tac
      t="length xc + length (rule_rpush e2)"
      and s="length (kPrefix k (w @ [parser_bottom G]))"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply (metis length_append)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN dh m - length (kPrefix k (w @ [parser_bottom G]))"
      and s="Suc nat"
      in ssubst)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply(force)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN dh m - length xc \<ge> length (rule_rpush e2)")
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply(subgoal_tac "ca=[]")
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply(subgoal_tac "drop (parser_fixed_input_length_recN dh m - (length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2))) (rule_rpush e2) = []")
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(parser_fixed_input_length_recN dh m - (length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2) + length (rule_rpush e2))) = Suc nat")
     apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
     apply(clarsimp)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
    apply(rule_tac
      t="(length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2) + length (rule_rpush e2))"
      and s="length (kPrefix k (w @ [parser_bottom G]))"
      in ssubst)
     apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
    apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
     apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
     apply(force)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
    apply (metis valid_parser_rules_rhs_gets_shorter parser_step_labels_def le_add_diff_inverse add.commute nat_minus_add_max)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
    apply(force)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply(subgoal_tac "(parser_fixed_input_length_recN dh m - (length (xc @ rule_rpush e2) - length (rule_rpush e2))) \<ge> length (rule_rpush e2)")
    apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
    apply(clarsimp)
   apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
   apply (metis append_length_inc diff_diff_cancel dropPrecise length_drop)
  apply(rename_tac G dh n sF m e2 c2 e1 c1 x xa c ca cb nat k w xc)(*strict*)
  apply (metis diff_diff_left diff_is_0_eq length_append lessI less_zeroE nat_le_linear)
  done

lemma parserS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserS.derivation G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserS_get_fixed_scheduler_DB G d n @ parserS_get_unfixed_scheduler_DB G d n = ATS_Sched.get_scheduler_nth parserS_get_scheduler d n)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserS.get_scheduler_nth_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: parserS_get_fixed_scheduler_DB_def)
  apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  done

lemma parserS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime: "
  (\<forall>G. valid_parser G \<longrightarrow> (\<forall>d. parserS.derivation_initial G d \<longrightarrow> (\<forall>n. (\<exists>y. d n = Some y) \<longrightarrow> parserS_get_fixed_scheduler_DB G d n @ parserS_get_unfixed_scheduler_DB G d n \<in> parser_schedulers G)))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserS_get_fixed_scheduler_DB_def parserS_get_scheduler_def)
  apply(case_tac y)
  apply(rename_tac G d n y option b)(*strict*)
  apply(simp add: get_configuration_def parserS_get_unfixed_scheduler_DB_def parserS_get_scheduler_def)
  apply(subgoal_tac "b \<in> parserS_configurations G")
   apply(rename_tac G d n y option b)(*strict*)
   prefer 2
   apply (metis parserS.belongs_configurations parserS.derivation_initial_belongs)
  apply(rename_tac G d n y option b)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d n option l w)(*strict*)
  apply(simp add: parser_schedulers_def)
  done

lemma parserS_inst_AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB: "
  \<forall>G::('stack, 'event, 'marker) parser.
       valid_parser G \<longrightarrow>
       (\<forall>d::(('stack, 'event) parser_step_label,
                   ('stack, 'event) parserS_conf) derivation.
           parserS.derivation_initial
            G d \<longrightarrow>
           (\<forall>n::nat.
               (\<exists>y::(('stack, 'event) parser_step_label,
                    ('stack, 'event) parserS_conf) derivation_configuration.
                   d n = Some y) \<longrightarrow>
               (\<not> parserS_get_fixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G]) =
               parserS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G]))"
  apply(clarsimp)
  apply(rename_tac G d n y)(*strict*)
  apply(simp add: parserS_get_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
  apply(case_tac y)
  apply(rename_tac G d n y option conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac G d n option conf)(*strict*)
  apply(rename_tac e c)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: suffix_def)
  apply(subgoal_tac "c \<in> parserS_configurations G")
   apply(rename_tac G d n e c)(*strict*)
   prefer 2
   apply (metis parserS.derivation_initial_configurations)
  apply(rename_tac G d n e c)(*strict*)
  apply(rule antisym)
   apply(rename_tac G d n e c)(*strict*)
   apply(clarsimp)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G d n e c ca cb)(*strict*)
   apply(subgoal_tac "parserS_conf_scheduler c = (cb @ [parser_bottom G]) @ (ca @ [parser_bottom G])")
    apply(rename_tac G d n e c ca cb)(*strict*)
    prefer 2
    apply(rule_tac
      t="cb @ [parser_bottom G]"
      and s="take (parser_fixed_input_length_recN d n) (parserS_conf_scheduler c)"
      in ssubst)
     apply(rename_tac G d n e c ca cb)(*strict*)
     apply(force)
    apply(rename_tac G d n e c ca cb)(*strict*)
    apply(rule_tac
      t="ca @ [parser_bottom G]"
      and s="drop (parser_fixed_input_length_recN d n) (parserS_conf_scheduler c)"
      in ssubst)
     apply(rename_tac G d n e c ca cb)(*strict*)
     apply(force)
    apply(rename_tac G d n e c ca cb)(*strict*)
    apply (metis append_Cons append_take_drop_id)
   apply(rename_tac G d n e c ca cb)(*strict*)
   apply(thin_tac "drop (parser_fixed_input_length_recN d n) (parserS_conf_scheduler c) = ca @ [parser_bottom G]")
   apply(thin_tac "take (parser_fixed_input_length_recN d n) (parserS_conf_scheduler c) = cb @ [parser_bottom G]")
   apply(subgoal_tac "c \<notin> parserS_configurations G")
    apply(rename_tac G d n e c ca cb)(*strict*)
    prefer 2
    apply(simp add: parserS_configurations_def)
    apply(force)
   apply(rename_tac G d n e c ca cb)(*strict*)
   apply(force)
  apply(rename_tac G d n e c)(*strict*)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G d n e l w)(*strict*)
  apply(rule_tac
      xs="take (parser_fixed_input_length_recN d n) w @ take (parser_fixed_input_length_recN d n - length w) [parser_bottom G]"
      in rev_cases)
   apply(rename_tac G d n e l w)(*strict*)
   prefer 2
   apply(rename_tac G d n e l w ys y)(*strict*)
   apply(clarsimp)
   apply(case_tac "parser_fixed_input_length_recN d n - length w")
    apply(rename_tac G d n e l w ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac G d n e l w ys y nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac G d n e l w)(*strict*)
  apply(clarsimp)
  done

lemma parserS_inst_ATS_Sched_DB0_axioms: "
  ATS_Sched_DB0_axioms valid_parser parserS_configurations
     parserS_initial_configurations parser_step_labels parserS_step_relation
     parser_fixed_scheduler_extendable parser_unfixed_schedulers
     right_quotient_word (@) parser_unfixed_scheduler_extendable
     parser_schedulers parserS_get_scheduler (@)
     parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB
     parserS_get_fixed_scheduler_DB"
  apply(simp add: ATS_Sched_DB0_axioms_def)
  apply(simp add: parserS_inst_AX_get_fixed_scheduler_DB_and_get_unfixed_scheduler_DB_vs_get_scheduler_nth parserS_inst_AX_join_fixed_scheduler_unfixed_scheduler_closed_prime parserS_inst_AX_sched_modification_preserves_steps parserS_inst_AX_fixed_scheduler_extendable_vs_unfixed_scheduler_extendable_DB )
  done

interpretation "parserS" : loc_autS_3
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserS_configurations"
  (* initial_configurations *)
  "parserS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserS_marking_condition"
  (* marked_effect *)
  "parserS_marked_effect"
  (* unmarked_effect *)
  "parserS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserS_string_state"
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
  "parserS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "parserS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserS_inst_AX_initial_configuration_belongs parserS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserS_inst_ATS_Language_by_Finite_Derivations_axioms parserS_inst_ATS_String_State_Modification_axioms parserS_inst_ATS_axioms parserS_inst_ATS_SchedUF_DB_axioms parserS_inst_ATS_SchedF_DB_axioms parserS_inst_ATS_Sched_DB0_axioms parserS_inst_ATS_Sched_axioms )
  done

lemma parserS_parser_fixed_input_length_recN_equal_by_labels: "
  parserS.derivation G d1
  \<Longrightarrow> parserS.derivation G d2
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

lemma parserS_schedUF_db_decreases: "
  valid_parser G
  \<Longrightarrow> parserS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> \<exists>w. parserS_get_unfixed_scheduler_DB G d i = w @ (parserS_get_unfixed_scheduler_DB G d j)"
  apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G d i"
      and s="drop (parser_fixed_input_length_recN d i) (parserS_conf_scheduler ci)"
      in ssubst)
   apply(simp add: parserS_get_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
  apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G d j"
      and s="drop (parser_fixed_input_length_recN d j) (parserS_conf_scheduler cj)"
      in ssubst)
   apply(simp add: parserS_get_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
  apply(subgoal_tac "length (parserS_conf_scheduler ci) - (parser_fixed_input_length_recN d i) \<ge> length (parserS_conf_scheduler cj) - (parser_fixed_input_length_recN d (i+(j-i)))")
   prefer 2
   apply(rule_tac PARSER_UnseenPartStrictlyDecreases)
       apply(force)
      apply(rule parserS.derivation_initial_belongs)
       apply(force)
      apply(force)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserS_string_state ci = w @ parserS_string_state cj")
   prefer 2
   apply(rule_tac
      j="j-i"
      and d="d"
      in parserS.derivation_monotonically_dec)
        apply(force)
       apply(force)
      apply(rule parserS.derivation_initial_belongs)
       apply(force)
      apply(force)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d j \<le> length (parserS_conf_scheduler cj)")
   apply(rename_tac w)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d i \<le> length (parserS_conf_scheduler ci)")
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parser_fixed_input_length_recN d i - length w \<le> parser_fixed_input_length_recN d j")
     apply(rename_tac w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(rule_tac
      x="(drop (parser_fixed_input_length_recN d i) w) @ (take (parser_fixed_input_length_recN d j - (parser_fixed_input_length_recN d i - length w)) (drop (parser_fixed_input_length_recN d i - length w) (parserS_conf_scheduler cj)))"
      in exI)
    apply(rename_tac w)(*strict*)
    apply(clarsimp)
    apply (metis append_take_drop_id_hlp drop_distrib_append drop_take take_all_length)
   apply(rename_tac w)(*strict*)
   apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(rule parserS.derivation_initial_belongs)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(rule parserS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(rule parserS.derivation_initial_belongs)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule parserS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(force)
  done

lemma parserS_mod_preserves_derivation_prime: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> sUF \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserS.derivation_initial G dh
  \<Longrightarrow> parserS.derivation G (parserS.replace_unfixed_scheduler_DB G dh sUF n)"
  apply(simp add: parserS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
    apply(clarsimp)
   apply(rule parserS.some_position_has_details_at_0)
   apply(simp add: parserS.derivation_initial_def)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "(parserS.replace_unfixed_scheduler_DB G dh sUF n (Suc nat))")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh nat = Some (pair e1 c1) \<and> dh (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
   apply(rename_tac nat option b)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac nat option b)(*strict*)
     apply(simp add: parserS.derivation_initial_def)
    apply(rename_tac nat option b)(*strict*)
    apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
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
  apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(rule conjI)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(simp add: parserS_set_unfixed_scheduler_DB_def get_configuration_def)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_get_unfixed_scheduler_DB G dh nat = w @ (parserS_get_unfixed_scheduler_DB G dh (Suc nat))")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_get_unfixed_scheduler_DB G dh (Suc nat) = w @ (parserS_get_unfixed_scheduler_DB G dh n)")
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa)(*strict*)
    apply(simp add: right_quotient_word_def)
    apply(subgoal_tac "valid_parser_step_label G e2")
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa)(*strict*)
     prefer 2
     apply(simp add: valid_parser_def)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
    apply(simp add: parserS_set_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def parserS_get_scheduler_def get_configuration_def)
    apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
     apply(case_tac "(parser_fixed_input_length_recN dh nat) - (length (kPrefix k (wb @ [parser_bottom G])))")
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "max (parser_fixed_input_length_recN dh nat) (length (kPrefix k (wb @ [parser_bottom G]))) = (length (kPrefix k (wb @ [parser_bottom G])))")
       apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "(length (kPrefix k (wb @ [parser_bottom G])) - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2))) = length (rule_rpush e2)")
       apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
       prefer 2
       apply (metis append_length_inc diff_diff_cancel dropPrecise length_drop)
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
     apply(simp add: suffix_def)
     apply(clarsimp)
     apply(subgoal_tac "max (parser_fixed_input_length_recN dh nat) (length (kPrefix k (wb @ [parser_bottom G]))) = (parser_fixed_input_length_recN dh nat)")
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "take (parser_fixed_input_length_recN dh nat - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2))) (rule_rpush e2) = rule_rpush e2")
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply(rule take_all)
      apply (metis valid_parser_rules_rhs_gets_shorter diff_diff_cancel diff_le_mono Lattices.linorder_class.max.absorb_iff2 Lattices.linorder_class.max.commute)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(parser_fixed_input_length_recN dh nat - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2) + length (rule_rpush e2))) = Suc nata")
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply (metis butn_length butn_prefix_closureise length_append)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
    apply(simp add: suffix_def)
    apply(clarsimp)
    apply(rule parserS.some_position_has_details_before_max_dom)
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
      apply(simp add: parserS.derivation_initial_def)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    prefer 2
    apply(rule parserS.some_position_has_details_before_max_dom)
      apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
      apply(simp add: parserS.derivation_initial_def)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x xa w e c)(*strict*)
   apply(rule parserS_schedUF_db_decreases)
       apply(rename_tac nat e1 e2 c1 c2 x xa w e c)(*strict*)
       apply(force)+
   apply(rename_tac nat e1 e2 c1 c2 x xa w e c)(*strict*)
   defer
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(rule parserS_schedUF_db_decreases)
       apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
       apply(force)+
  apply(rename_tac nat e1 e2 c1 c2 x xa w e c)(*strict*)
  defer
  apply (metis not_None_eq parserS.allPreMaxDomSome_prime parserS.derivation_initial_is_derivation)
  done

lemma parserS_inst_AX_replace_unfixed_scheduler_DB_sound: "
  \<forall>G. valid_parser G \<longrightarrow> (\<forall>d n. maximum_of_domain d n \<longrightarrow> parserS.derivation_initial G d \<longrightarrow> parserS_get_unfixed_scheduler_DB G d n \<sqsupseteq> [parser_bottom G] \<longrightarrow> (\<forall>sUF. sUF \<in> parser_unfixed_schedulers G \<longrightarrow> sUF \<sqsupseteq> [parser_bottom G] \<longrightarrow> parserS_get_unfixed_scheduler_DB G (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB G d sUF n) n = sUF))"
  apply(clarsimp)
  apply(rename_tac G d n sUF)(*strict*)
  apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB G d sUF n) n"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
   apply(rename_tac G d n sUF)(*strict*)
   defer
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>e c. d n = Some (pair e c)")
    apply(rename_tac G d n sUF)(*strict*)
    apply(clarsimp)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply(simp add: get_configuration_def)
    apply(rule_tac
      t="right_quotient_word (parserS_get_unfixed_scheduler_DB G d n) (parserS_get_unfixed_scheduler_DB G d n)"
      and s="Some []"
      in ssubst)
     apply(rename_tac G d n sUF e c)(*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply(clarsimp)
    apply(simp add: parserS_set_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
    apply(subgoal_tac "parser_fixed_input_length_recN d n = length (parserS_get_fixed_scheduler_DB G d n)")
     apply(rename_tac G d n sUF e c)(*strict*)
     apply(force)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply(simp add: parserS_get_fixed_scheduler_DB_def get_configuration_def)
    apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserS_get_scheduler c)")
     apply(rename_tac G d n sUF e c)(*strict*)
     apply(force)
    apply(rename_tac G d n sUF e c)(*strict*)
    apply (metis Nil_is_append_conv append_take_drop_id nat_le_linear not_Cons_self parserS_get_scheduler_def self_append_conv suffix_def take_all)
   apply(rename_tac G d n sUF)(*strict*)
   apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac G d n sUF y)(*strict*)
   apply(case_tac y)
   apply(rename_tac G d n sUF y option b)(*strict*)
   apply(force)
  apply(rename_tac G d n sUF)(*strict*)
  apply(rule parserS_parser_fixed_input_length_recN_equal_by_labels)
    apply(rename_tac G d n sUF)(*strict*)
    defer
    apply(simp add: parserS.derivation_initial_def)
    apply(force)
   apply(rename_tac G d n sUF i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. d i =Some (pair e c)")
    apply(rename_tac G d n sUF i)(*strict*)
    prefer 2
    apply(rule parserS.some_position_has_details_before_max_dom)
      apply(rename_tac G d n sUF i)(*strict*)
      apply(simp add: parserS.derivation_initial_def)
      apply(force)
     apply(rename_tac G d n sUF i)(*strict*)
     apply(force)
    apply(rename_tac G d n sUF i)(*strict*)
    apply(force)
   apply(rename_tac G d n sUF i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G d n sUF i e c)(*strict*)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
   apply(simp add: get_label_def)
  apply(rename_tac G d n sUF)(*strict*)
  apply(rule parserS_mod_preserves_derivation_prime)
     apply(rename_tac G d n sUF)(*strict*)
     apply(force)+
  done

lemma parserS_inst_ATS_Sched_DB_axioms: "
  ATS_Sched_DB_axioms valid_parser parserS_initial_configurations
     parserS_step_relation parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserS_set_unfixed_scheduler_DB
     parserS_get_unfixed_scheduler_DB"
  apply(simp add: ATS_Sched_DB_axioms_def)
  apply(rule parserS_inst_AX_replace_unfixed_scheduler_DB_sound)
  done

interpretation "parserS" : loc_autS_4
  (* TSstructure *)
  "valid_parser"
  (* configurations *)
  "parserS_configurations"
  (* initial_configurations *)
  "parserS_initial_configurations"
  (* step_labels *)
  "parser_step_labels"
  (* step_relation *)
  "parserS_step_relation"
  (* effects *)
  "parser_markers"
  (* marking_condition *)
  "parserS_marking_condition"
  (* marked_effect *)
  "parserS_marked_effect"
  (* unmarked_effect *)
  "parserS_unmarked_effect"
  (* destinations *)
  "parser_destinations"
  (* get_destinations *)
  "parserS_get_destinations"
  (* decreasing *)
  "True"
  (* string_state *)
  "parserS_string_state"
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
  "parserS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler *)
  "append"
  (* extend_scheduler *)
  "append"
  (* set_unfixed_scheduler_DB *)
  "parserS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB *)
  "parserS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB *)
  "parserS_get_fixed_scheduler_DB"
  apply(simp add: LOCALE_DEFS parser_interpretations)
  apply(simp add: parserS_inst_AX_initial_configuration_belongs parserS_inst_AX_step_relation_preserves_belongs )
  apply(simp add: parserS_inst_ATS_Language_by_Finite_Derivations_axioms parserS_inst_ATS_String_State_Modification_axioms parserS_inst_ATS_axioms parserS_inst_ATS_SchedUF_DB_axioms parserS_inst_ATS_SchedF_DB_axioms parserS_inst_ATS_Sched_DB0_axioms parserS_inst_ATS_Sched_DB_axioms parserS_inst_ATS_Sched_axioms )
  done

lemmas parserS_interpretations =
  parser_interpretations
  parserS_inst_ATS_Sched_axioms
  parserS_inst_AX_initial_configuration_belongs
  parserS_inst_AX_step_relation_preserves_belongs
  parserS_inst_ATS_Language_by_Finite_Derivations_axioms
  parserS_inst_ATS_String_State_Modification_axioms
  parserS_inst_ATS_axioms
  parserS_inst_ATS_SchedUF_DB_axioms
  parserS_inst_ATS_SchedF_DB_axioms
  parserS_inst_ATS_Sched_DB0_axioms
  parserS_inst_ATS_Sched_DB_axioms

lemma parserS_mod_preserves_derivation: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> parserS.derivation_initial G dh
  \<Longrightarrow> parserS.derivation G (parserS.replace_unfixed_scheduler_DB G dh sUF n)"
  apply(simp add: parserS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
    apply(clarsimp)
   apply(rule parserS.some_position_has_details_at_0)
   apply(simp add: parserS.derivation_initial_def)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "(parserS.replace_unfixed_scheduler_DB G dh sUF n (Suc nat))")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac nat a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat option b)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh nat = Some (pair e1 c1) \<and> dh (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
   apply(rename_tac nat option b)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac nat option b)(*strict*)
     apply(simp add: parserS.derivation_initial_def)
    apply(rename_tac nat option b)(*strict*)
    apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
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
  apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(rule conjI)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(simp add: parserS_set_unfixed_scheduler_DB_def get_configuration_def)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_get_unfixed_scheduler_DB G dh nat = w @ (parserS_get_unfixed_scheduler_DB G dh (Suc nat))")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_get_unfixed_scheduler_DB G dh (Suc nat) = w @ (parserS_get_unfixed_scheduler_DB G dh n)")
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa)(*strict*)
    apply(simp add: right_quotient_word_def)
    apply(subgoal_tac "valid_parser_step_label G e2")
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa)(*strict*)
     prefer 2
     apply(simp add: valid_parser_def)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
    apply(simp add: parserS_set_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def parserS_get_scheduler_def get_configuration_def)
    apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
     apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
     apply(case_tac "(parser_fixed_input_length_recN dh nat) - (length (kPrefix k (wb @ [parser_bottom G])))")
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "max (parser_fixed_input_length_recN dh nat) (length (kPrefix k (wb @ [parser_bottom G]))) = (length (kPrefix k (wb @ [parser_bottom G])))")
       apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "(length (kPrefix k (wb @ [parser_bottom G])) - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2))) = length (rule_rpush e2)")
       apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
       prefer 2
       apply (metis diff_diff_cancel dropPrecise drop_length_append length_drop)
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c)(*strict*)
      apply(clarsimp)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "max (parser_fixed_input_length_recN dh nat) (length (kPrefix k (wb @ [parser_bottom G]))) = (parser_fixed_input_length_recN dh nat)")
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "take (parser_fixed_input_length_recN dh nat - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2))) (rule_rpush e2) = rule_rpush e2")
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply(rule take_all)
      apply (metis Suc_not_Zero diff_diff_cancel diff_diff_left diff_is_0_eq dropPrecise drop_length_append length_append length_drop nat_le_linear)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "(parser_fixed_input_length_recN dh nat - (length (kPrefix k (wb @ [parser_bottom G])) - length (rule_rpush e2) + length (rule_rpush e2))) = Suc nata")
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
      prefer 2
      apply (metis butn_length butn_prefix_closureise length_append)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc e c nata)(*strict*)
     apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
    apply(rule parserS.some_position_has_details_before_max_dom)
      apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
      apply(simp add: parserS.derivation_initial_def)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa w wa k wb xc)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    prefer 2
    apply(rule parserS.some_position_has_details_before_max_dom)
      apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
      apply(simp add: parserS.derivation_initial_def)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x xa w e c)(*strict*)
   apply(rule parserS_schedUF_db_decreases)
       apply(rename_tac nat e1 e2 c1 c2 x xa w e c)(*strict*)
       apply(force)+
   apply(rename_tac nat e1 e2 c1 c2 x xa w e c)(*strict*)
   defer
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(rule parserS_schedUF_db_decreases)
       apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
       apply(force)+
  apply(rename_tac nat e1 e2 c1 c2 x xa w e c)(*strict*)
  apply (metis not_None_eq parserS.allPreMaxDomSome_prime parserS.derivation_initial_is_derivation)
  done

lemma parserS_marking_condition_ALT_vs_parserS_marking_condition: "
  valid_parser G
  \<Longrightarrow> parserS.derivation_initial G d
  \<Longrightarrow> parserS_marking_condition_ALT G d = parserS_marking_condition G d"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule parserS.derivation_initial_has_configuration_at_position_0)
    apply(force)
   apply(force)
  apply(simp add: parserS_marking_condition_ALT_def parserS_marking_condition_def)
  done

theorem parserS_dependency_between_determinism_properties_main: "
  valid_parser G
  \<Longrightarrow> parserS.is_forward_target_deterministic_accessible G"
  apply(simp add: parserS.is_forward_target_deterministic_accessible_def parserS_step_relation_def)
  apply(clarsimp)
  done

end
