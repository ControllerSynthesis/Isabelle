section {*I\_kparser\_FS\_HFS*}
theory
  I_kparser_FS_HFS

imports
  I_kparser_FS
  I_kparser_HFS

begin

definition parserHFS_to_parserFS_derivation :: "
  (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf)derivation
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf)derivation"
  where
    "parserHFS_to_parserFS_derivation d \<equiv>
  \<lambda>n. case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow>
      Some (pair e
        \<lparr>parserFS_conf_fixed = parserHFS_conf_fixed c,
        parserFS_conf_stack = parserHFS_conf_stack c,
        parserFS_conf_scheduler = drop (length(parserHFS_conf_fixed c))(parserHFS_conf_scheduler c)\<rparr>)"

lemma parserHFS_to_parserFS_derivation_preserves_derivation_initial: "
  valid_parser P
  \<Longrightarrow> parserHFS.derivation_initial P d
  \<Longrightarrow> parserFS.derivation_initial P (parserHFS_to_parserFS_derivation d)"
  apply(simp add: parserHFS_to_parserFS_derivation_def)
  apply(simp add: parserFS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(simp add: parserHFS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: parserFS_initial_configurations_def parserHFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: parserFS_configurations_def parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: parser_fixed_schedulers_def parser_schedulers_def parser_unfixed_schedulers_def prefix_closure_def suffix_closure_def)
   apply(rule conjI)
    apply(rename_tac w)(*strict*)
    apply(rule_tac x="[parser_bottom P]" in exI)
    apply(simp add: prefix_def)
   apply(rename_tac w)(*strict*)
   apply(rule_tac x="(w @ [parser_bottom P])" in exI)
   apply(simp add: suffix_def)
  apply(simp add: parserFS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation P c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "c1 \<in> parserHFS_configurations P")
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule parserHFS.belongs_configurations)
    apply(rename_tac nat e1 e2 c1 c2)(*strict*)
    apply(rule parserHFS.derivation_initial_belongs)
     apply(rename_tac nat e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P e2")
   apply(rename_tac nat e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
   apply(simp add: parserFS_step_relation_def parserHFS_step_relation_def)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserFS_step_relation_def parserHFS_step_relation_def valid_parser_step_label_def parserHFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c2 f h k w xa xb y xc wa)(*strict*)
  apply(case_tac e2)
  apply(rename_tac nat e1 e2 c2 f h k w xa xb y xc wa rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(case_tac c2)
  apply(rename_tac nat e1 e2 c2 f h k w xa xb y xc wa rule_lpopa rule_rpopa rule_lpusha rule_rpusha parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 f h k w xa xb y xc wa rule_lpop rule_lpush rule_rpush)(*strict*)
  apply(rename_tac lpo lpu rpu)
  apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu)(*strict*)
  apply(rule_tac conjI)
   apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu)(*strict*)
   apply(rule_tac x="xc" in exI)
   apply(force)
  apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu c)(*strict*)
  apply(subgoal_tac "prefix f (kPrefix k (w @ [parser_bottom P])) \<or> prefix (kPrefix k (w @ [parser_bottom P])) f")
   apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu c)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu c)(*strict*)
  apply(erule disjE)
   apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu c)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu c ca)(*strict*)
   apply(rule conjI)
    apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu c ca)(*strict*)
    apply (metis drop_append)
   apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu c ca)(*strict*)
   apply (metis drop_length_append)
  apply(rename_tac nat e1 f h k w xa xb y xc wa lpo lpu rpu c)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  done

lemma parserHFS_to_parserFS_derivation_preserves_parser_fixed_input_length_recN: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> parser_fixed_input_length_recN d n = parser_fixed_input_length_recN (parserHFS_to_parserFS_derivation d) n"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d(Suc n)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS_to_parserFS_derivation_def)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac n a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e c)(*strict*)
   apply(simp add: parserHFS_to_parserFS_derivation_def)
  apply(rename_tac n a)(*strict*)
  apply(rule parserHFS.pre_some_position_is_some_position_prime)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  done

lemma parserHFS_to_parserFS_derivation_preserves_step_labels: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>c. (parserHFS_to_parserFS_derivation d) n = Some (pair e c)"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: parserHFS_to_parserFS_derivation_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserHFS.step_detail_before_some_position)
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
  apply(rename_tac n c e1 e2 c1 ca)(*strict*)
  apply(simp add: parserHFS_to_parserFS_derivation_def)
  done

lemma parserHFS_to_parserFS_derivation_preserves_maximum_of_domain: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (parserHFS_to_parserFS_derivation d) n"
  apply(simp add: maximum_of_domain_def parserHFS_to_parserFS_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

definition parserFS_to_parserHFS_derivation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf) derivation
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf)derivation"
  where
    "parserFS_to_parserHFS_derivation G d \<equiv>
  \<lambda>n.
  case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow>
      Some (pair e
        \<lparr>parserHFS_conf_fixed
          = parserFS_conf_fixed c,
        parserHFS_conf_history
          = butlast_if_match ((the (right_quotient_word
                    (parserFS_conf_scheduler
                      (the (get_configuration (d 0))))
                    (parserFS_conf_scheduler c)))) (parser_bottom G),
        parserHFS_conf_stack = parserFS_conf_stack c,
        parserHFS_conf_scheduler = parserFS_conf_fixed c @ parserFS_conf_scheduler c\<rparr>)"

lemma parserFS_to_parserHFS_derivation_preserves_derivation_initial: "
  valid_parser P
  \<Longrightarrow> parserFS.derivation_initial P d
  \<Longrightarrow> parserHFS.derivation_initial P (parserFS_to_parserHFS_derivation P d)"
  apply(simp add: parserFS_to_parserHFS_derivation_def)
  apply(simp add: parserHFS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(simp add: parserFS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: parserFS_initial_configurations_def parserHFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: parserFS_configurations_def parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: right_quotient_word_def)
   apply(simp add: prefix_def)
   apply(simp add: suffix_def butlast_if_match_def parser_schedulers_def parser_unfixed_schedulers_def valid_parser_def)
   apply(clarsimp)
  apply(simp add: parserHFS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserFS_step_relation P c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserFS_step_relation_def parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_at_0)
   apply(simp add: parserFS.derivation_initial_def)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P e2")
   apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
  apply(subgoal_tac "c1 \<in> parserFS_configurations P")
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
   prefer 2
   apply(rule parserFS.belongs_configurations)
    apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
    apply(rule parserFS.derivation_initial_belongs)
     apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_string_state c = w @ (parserFS_string_state c1)")
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
   prefer 2
   apply(rule_tac
      j="nat"
      in parserFS.derivation_monotonically_dec)
        apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
        apply(force)
       apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
  apply(subgoal_tac "parserFS_conf_fixed c = []")
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
   prefer 2
   apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w)(*strict*)
  apply(simp add: parserFS_string_state_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_string_state c1 = w @ (parserFS_string_state c2)")
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc 0"
      in parserFS.derivation_monotonically_dec)
        apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
        apply(force)
       apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
  apply(subgoal_tac "c \<in> parserFS_configurations P")
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
   prefer 2
   apply(rule parserFS.belongs_configurations)
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
    apply(rule parserFS.derivation_initial_belongs)
     apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa)(*strict*)
  apply(simp add: parserFS_string_state_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa wb)(*strict*)
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c2 x xa k w wa wb f la r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac nat e1 e2 c2 x xa k w wa wb f la r parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
  apply(rename_tac f st sc)
  apply(rename_tac nat e1 e2 c2 x xa k w wa wb fa la r f st sc)(*strict*)
  apply(case_tac e2)
  apply(rename_tac nat e1 e2 c2 x xa k w wa wb fa la r f st sc rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
  apply(rename_tac lpo lpu rpo rpu)
  apply(rename_tac nat e1 e2 c2 x xa k w wa wb fa la r f st sc lpo lpu rpo rpu)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 x xa k w wa wb fa la r f sc lpo rpo rpu)(*strict*)
  apply(thin_tac "parserFS.derivation_initial P d")
  apply(thin_tac "d (Suc nat) =
       Some (pair (Some \<lparr>rule_lpop = lpo, rule_rpop = kPrefix k (w @ [parser_bottom P]),
                           rule_lpush = rpo, rule_rpush = rpu\<rparr>)
              \<lparr>parserFS_conf_fixed = f, parserFS_conf_stack = x @ rpo,
                 parserFS_conf_scheduler = sc\<rparr>)")
  apply(thin_tac "d nat =
       Some (pair e1
              \<lparr>parserFS_conf_fixed = fa, parserFS_conf_stack = x @ lpo,
                 parserFS_conf_scheduler = r\<rparr>)")
  apply(thin_tac "\<lparr>rule_lpop = lpo, rule_rpop = kPrefix k (w @ [parser_bottom P]), rule_lpush = rpo,
          rule_rpush = rpu\<rparr>
       \<in> parser_rules P")
  apply(thin_tac "d 0 =
       Some (pair None
              \<lparr>parserFS_conf_fixed = [], parserFS_conf_stack = la,
                 parserFS_conf_scheduler = wa @ wb @ f @ sc\<rparr>)")
  apply(thin_tac "X \<noteq> []" for X)
  apply(thin_tac "X \<noteq> []"  for X)
  apply(thin_tac "set X \<subseteq> parser_nonterms P" for X)
  apply(thin_tac "set X \<subseteq> parser_nonterms P" for X)
  apply(thin_tac "set X \<subseteq> parser_nonterms P" for X)
  apply(thin_tac "set X \<subseteq> parser_nonterms P" for X)
  apply(thin_tac "set X \<subseteq> parser_events P" for X)
  apply(erule disjE)
   apply(rename_tac nat e1 x xa k w wa wb fa la r f sc lpo rpo rpu)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w wa wb fa sc rpu popnew)(*strict*)
   apply(rule_tac t="right_quotient_word (wa @ wb @ rpu @ sc) sc" and s="Some (wa @ wb @ rpu)" in ssubst)
    apply(rename_tac k w wa wb fa sc rpu popnew)(*strict*)
    apply(rule right_quotient_word_Some_by_append)
    apply(force)
   apply(rename_tac k w wa wb fa sc rpu popnew)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "prefix fa wb \<or> prefix wb fa")
    apply(rename_tac k w wa wb fa sc rpu popnew)(*strict*)
    prefer 2
    apply(rule mutual_prefix_prefix)
    apply(force)
   apply(rename_tac k w wa wb fa sc rpu popnew)(*strict*)
   apply(erule disjE)
    apply(rename_tac k w wa wb fa sc rpu popnew)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac k w wa fa sc rpu c)(*strict*)
    apply(rule_tac t="right_quotient_word (wa @ fa @ c @ rpu @ sc) (c @ rpu @ sc)" and s="Some(wa@fa)" in ssubst)
     apply(rename_tac k w wa fa sc rpu c)(*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac k w wa fa sc rpu c)(*strict*)
    apply(clarsimp)
    apply(rule_tac xs="sc" in rev_cases)
     apply(rename_tac k w wa fa sc rpu c)(*strict*)
     prefer 2
     apply(rename_tac k w wa fa sc rpu c ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac k w wa fa rpu c ys y)(*strict*)
     apply(simp add: parser_schedulers_def)
     apply(clarsimp)
     apply(rename_tac k w wa fa rpu c ys)(*strict*)
     apply (metis (no_types, hide_lams) append_Nil2 append_assoc butlast_if_match_pull_out butlast_if_match_reduces drop_butlast_if_match_distrib in_set_conv_decomp)
    apply(rename_tac k w wa fa sc rpu c)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w wa fa rpu c)(*strict*)
    apply(rule_tac xs="rpu" in rev_cases)
     apply(rename_tac k w wa fa rpu c)(*strict*)
     prefer 2
     apply(rename_tac k w wa fa rpu c ys y)(*strict*)
     apply(clarsimp)
     apply(rename_tac k w wa fa c ys y)(*strict*)
     apply(simp add: parser_schedulers_def)
     apply(clarsimp)
     apply(rename_tac k w wa fa c ys)(*strict*)
     apply (metis append_Nil append_assoc butlast_if_match_pull_out butlast_if_match_reduces drop_butlast_if_match_distrib in_set_conv_decomp snoc_eq_iff_butlast)
    apply(rename_tac k w wa fa rpu c)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w wa fa c)(*strict*)
    apply(rule_tac xs="c" in rev_cases)
     apply(rename_tac k w wa fa c)(*strict*)
     apply(clarsimp)
     apply(rename_tac k w wa)(*strict*)
     apply(simp add: kPrefix_def)
     apply(case_tac "k-length w")
      apply(rename_tac k w wa)(*strict*)
      prefer 2
      apply(rename_tac k w wa nat)(*strict*)
      apply(force)
     apply(rename_tac k w wa)(*strict*)
     apply(clarsimp)
     apply(simp add: parser_schedulers_def)
     apply(metis)
    apply(rename_tac k w wa fa c ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac k w wa fa ys y)(*strict*)
    apply(simp add: parser_schedulers_def)
   apply(rename_tac k w wa wb fa sc rpu popnew)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac k w wa wb sc popnew c)(*strict*)
   apply(rule_tac xs="sc" in rev_cases)
    apply(rename_tac k w wa wb sc popnew c)(*strict*)
    prefer 2
    apply(rename_tac k w wa wb sc popnew c ys y)(*strict*)
    apply(simp add: parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac k w wa wb popnew c ys)(*strict*)
    apply(rule_tac t="right_quotient_word (wa @ wb @ c @ popnew @ ys @ [parser_bottom P])
               (popnew @ ys @ [parser_bottom P])" and s="Some (wa@wb@c)" in ssubst)
     apply(rename_tac k w wa wb popnew c ys)(*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac k w wa wb popnew c ys)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (wa @ wb @ c @ popnew) (parser_bottom P) = SSX" for SSX)
     apply(rename_tac k w wa wb popnew c ys)(*strict*)
     prefer 2
     apply(rule butlast_if_match_direct2_prime)
     apply(force)
    apply(rename_tac k w wa wb popnew c ys)(*strict*)
    apply(subgoal_tac "butlast_if_match (wa @ wb @ c) (parser_bottom P) = SSX" for SSX)
     apply(rename_tac k w wa wb popnew c ys)(*strict*)
     prefer 2
     apply(rule butlast_if_match_direct2_prime)
     apply(force)
    apply(rename_tac k w wa wb popnew c ys)(*strict*)
    apply(subgoal_tac "butlast_if_match (wb @ c @ popnew) (parser_bottom P) = SSX" for SSX)
     apply(rename_tac k w wa wb popnew c ys)(*strict*)
     prefer 2
     apply(rule butlast_if_match_direct2_prime)
     apply(force)
    apply(rename_tac k w wa wb popnew c ys)(*strict*)
    apply(force)
   apply(rename_tac k w wa wb sc popnew c)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w wa wb popnew c)(*strict*)
   apply(rule_tac xs="popnew" in rev_cases)
    apply(rename_tac k w wa wb popnew c)(*strict*)
    prefer 2
    apply(rename_tac k w wa wb popnew c ys y)(*strict*)
    apply(simp add: parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac k w wa wb c ys)(*strict*)
    apply(rule_tac t="right_quotient_word (wa @ wb @ c @ ys @ [parser_bottom P])
               (ys @ [parser_bottom P])" and s="Some (wa@wb@c)" in ssubst)
     apply(rename_tac k w wa wb c ys)(*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac k w wa wb c ys)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (wa @ wb @ c @ ys @ [parser_bottom P]) (parser_bottom P) = SSX" for SSX)
     apply(rename_tac k w wa wb c ys)(*strict*)
     prefer 2
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac k w wa wb c ys)(*strict*)
    apply(subgoal_tac "butlast_if_match (wa @ wb @ c) (parser_bottom P) = SSX" for SSX)
     apply(rename_tac k w wa wb c ys)(*strict*)
     prefer 2
     apply(rule butlast_if_match_direct2_prime)
     apply(force)
    apply(rename_tac k w wa wb c ys)(*strict*)
    apply(subgoal_tac "butlast_if_match (wb @ c @ ys @ [parser_bottom P]) (parser_bottom P) = SSX" for SSX)
     apply(rename_tac k w wa wb c ys)(*strict*)
     prefer 2
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac k w wa wb c ys)(*strict*)
    apply(force)
   apply(rename_tac k w wa wb popnew c)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w wa wb c)(*strict*)
   apply(rule_tac xs="c" in rev_cases)
    apply(rename_tac k w wa wb c)(*strict*)
    prefer 2
    apply(rename_tac k w wa wb c ys y)(*strict*)
    apply(simp add: parser_schedulers_def)
    apply(clarsimp)
    apply(rename_tac k w wa wb ys)(*strict*)
    apply(rule_tac t="right_quotient_word (wa @ wb @ ys @ [parser_bottom P])
               []" and s="Some (X)" for X in ssubst)
     apply(rename_tac k w wa wb ys)(*strict*)
     apply(rule right_quotient_word_Some_by_append)
     apply(force)
    apply(rename_tac k w wa wb ys)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (wb @ ys @ [parser_bottom P]) (parser_bottom P) = SSX" for SSX)
     apply(rename_tac k w wa wb ys)(*strict*)
     prefer 2
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac k w wa wb ys)(*strict*)
    apply(force)
   apply(rename_tac k w wa wb c)(*strict*)
   apply(clarsimp)
   apply(rename_tac k w wa)(*strict*)
   apply(simp add: kPrefix_def parser_schedulers_def)
   apply(clarsimp)
  apply(rename_tac nat e1 x xa k w wa wb fa la r f sc lpo rpo rpu)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w wa wb sc rpu remainder)(*strict*)
  apply(rule_tac xs="sc" in rev_cases)
   apply(rename_tac k w wa wb sc rpu remainder)(*strict*)
   prefer 2
   apply(rename_tac k w wa wb sc rpu remainder ys y)(*strict*)
   apply(simp add: parser_schedulers_def)
   apply(clarsimp)
   apply(rename_tac k w wa wb rpu remainder ys)(*strict*)
   apply (metis append_assoc butlast_if_match_reduces drop_length_append in_set_conv_decomp length_append)
  apply(rename_tac k w wa wb sc rpu remainder)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w wa wb rpu remainder)(*strict*)
  apply(rule_tac xs="remainder" in rev_cases)
   apply(rename_tac k w wa wb rpu remainder)(*strict*)
   prefer 2
   apply(rename_tac k w wa wb rpu remainder ys y)(*strict*)
   apply(simp add: parser_schedulers_def)
   apply(clarsimp)
   apply(rename_tac k w wa wb rpu ys)(*strict*)
   apply (metis append_assoc butlast_if_match_reduces drop_length_append insert_subset le_SucI length_append set_append2 set_simps(2))
  apply(rename_tac k w wa wb rpu remainder)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w wa wb rpu)(*strict*)
  apply(rule_tac xs="rpu" in rev_cases)
   apply(rename_tac k w wa wb rpu)(*strict*)
   prefer 2
   apply(rename_tac k w wa wb rpu ys y)(*strict*)
   apply(simp add: parser_schedulers_def)
   apply(clarsimp)
   apply(rename_tac k w wa wb ys)(*strict*)
   apply (metis add_Suc_right butlast_if_match_length_le length_append length_append_singleton)
  apply(rename_tac k w wa wb rpu)(*strict*)
  apply(clarsimp)
  apply(rename_tac k w wa)(*strict*)
  apply(simp add: kPrefix_def parser_schedulers_def)
  apply(clarsimp)
  done

lemma parserFS_to_parserHFS_derivation_preserves_maximum_of_domain: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (parserFS_to_parserHFS_derivation G d) n"
  apply(simp add: maximum_of_domain_def parserFS_to_parserHFS_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

end
