section {*I\_kparser\_S\_FS*}
theory
  I_kparser_S_FS

imports
  I_kparser_S
  I_kparser_FS

begin

definition parserFS_to_parserS_derivation :: "
  (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf)derivation
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf)derivation"
  where
    "parserFS_to_parserS_derivation d \<equiv>
  \<lambda>n.
  case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow>
      Some (pair e
        \<lparr>parserS_conf_stack = parserFS_conf_stack c,
        parserS_conf_scheduler
          = parserFS_conf_fixed c @ parserFS_conf_scheduler c\<rparr>)"

lemma parserFS_to_parserS_derivation_preserves_derivation_initial: "
  valid_parser P
  \<Longrightarrow> parserFS.derivation_initial P d
  \<Longrightarrow> parserS.derivation_initial P (parserFS_to_parserS_derivation d)"
  apply(simp add: parserFS_to_parserS_derivation_def)
  apply(simp add: parserS.derivation_initial_def)
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
   apply(simp add: parserS_initial_configurations_def parserFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def parserFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac r)(*strict*)
   apply(simp add: dom_abbreviation)
   apply(clarsimp)
   apply(rename_tac v vb c)(*strict*)
   apply(simp add: valid_parser_def)
  apply(simp add: parserS.derivation_def)
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
  apply(simp add: parserS_step_relation_def parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x v)(*strict*)
  apply(erule disjE)
   apply(rename_tac nat e1 e2 c1 c2 x v)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x v)(*strict*)
  apply(force)
  done

lemma parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation G d
  \<Longrightarrow> parser_fixed_input_length_recN d n = parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) n"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d(Suc n)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac n a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e c)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n a)(*strict*)
  apply(rule parserFS.pre_some_position_is_some_position_prime)
     apply(rename_tac n a)(*strict*)
     apply(force)
    apply(rename_tac n a)(*strict*)
    apply(force)
   apply(rename_tac n a)(*strict*)
   apply(force)
  apply(rename_tac n a)(*strict*)
  apply(force)
  done

lemma parserFS_to_parserS_derivation_preserves_step_labels: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>c. (parserFS_to_parserS_derivation d) n = Some (pair e c)"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
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
  apply(simp add: parserFS_to_parserS_derivation_def)
  done

lemma parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) n = length (parserFS_conf_fixed (the(get_configuration(d n))))"
  apply(induct n)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(case_tac y)
   apply(rename_tac y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
   apply(simp add: parserFS_initial_configurations_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac n y)(*strict*)
     apply (metis parserFS.derivation_initial_is_derivation)
    apply(rename_tac n y)(*strict*)
    apply(force)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: get_configuration_def get_configuration_def)
  apply(case_tac "parserFS_to_parserS_derivation d (Suc n)")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n e1 e2 c1 c2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac n e1 e2 c1 c2 option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 b a)(*strict*)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 b a x v)(*strict*)
  apply(subgoal_tac "a=e2")
   apply(rename_tac n e1 e2 c1 c2 b a x v)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 b a x v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 b x v)(*strict*)
  apply(erule disjE)
   apply(rename_tac n e1 e2 c1 c2 b x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 b x v popnew)(*strict*)
   apply(case_tac "(length (parserFS_conf_fixed c1)) \<le> (length (rule_rpop e2))")
    apply(rename_tac n e1 e2 c1 c2 b x v popnew)(*strict*)
    apply(subgoal_tac "max (length (parserFS_conf_fixed c1)) (length (rule_rpop e2))=length (rule_rpop e2)")
     apply(rename_tac n e1 e2 c1 c2 b x v popnew)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 b x v popnew)(*strict*)
    apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 b x v popnew)(*strict*)
   apply(subgoal_tac "max (length (parserFS_conf_fixed c1)) (length (rule_rpop e2))=length (parserFS_conf_fixed c1)")
    apply(rename_tac n e1 e2 c1 c2 b x v popnew)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 b x v popnew)(*strict*)
   apply(clarsimp)
   apply (metis append_length_inc length_append)
  apply(rename_tac n e1 e2 c1 c2 b x v)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 b x v remainder)(*strict*)
  apply(case_tac "(length (parserFS_conf_fixed c1)) \<le> (length v + length (rule_rpush e2))")
   apply(rename_tac n e1 e2 c1 c2 b x v remainder)(*strict*)
   apply(subgoal_tac "max (length (parserFS_conf_fixed c1)) (length v + length (rule_rpush e2))=length v + length (rule_rpush e2)")
    apply(rename_tac n e1 e2 c1 c2 b x v remainder)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 b x v remainder)(*strict*)
   apply(clarsimp)
   apply (metis add_eq_self_zero append_assoc append_self_conv butn_prefix_closureise drop_length_append le_antisym length_append)
  apply(rename_tac n e1 e2 c1 c2 b x v remainder)(*strict*)
  apply(subgoal_tac "max (length (parserFS_conf_fixed c1)) (length v + length (rule_rpush e2))=length (parserFS_conf_fixed c1)")
   apply(rename_tac n e1 e2 c1 c2 b x v remainder)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 b x v remainder)(*strict*)
  apply(clarsimp)
  apply (metis diff_add_inverse length_append)
  done

lemma parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> parserFS_get_fixed_scheduler_DB G d n = parserS_get_fixed_scheduler_DB G (parserFS_to_parserS_derivation d) n"
  apply(induct n)
   apply(simp add: parserFS_get_fixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac y)
   apply(rename_tac y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac n y)(*strict*)
     apply (metis parserFS.derivation_initial_is_derivation)
    apply(rename_tac n y)(*strict*)
    apply(force)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
  apply(simp add: get_configuration_def get_configuration_def)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) (Suc n) = length (parserFS_conf_fixed (the(get_configuration(d (Suc n)))))")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
     apply(rename_tac n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def get_configuration_def)
  apply(case_tac "parserFS_to_parserS_derivation d (Suc n)")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n e1 e2 c1 c2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac n e1 e2 c1 c2 option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 b a)(*strict*)
  apply(subgoal_tac "a=e2")
   apply(rename_tac n e1 e2 c1 c2 b a)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) n = length (parserFS_conf_fixed (the(get_configuration(d n))))")
   apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
   prefer 2
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
     apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def get_configuration_def)
  apply(simp add: parserFS_to_parserS_derivation_def parserS_get_scheduler_def)
  apply(clarsimp)
  done

lemma parserFS_to_parserS_derivation_preserves_get_unfixed_scheduler_DB: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> parserFS_get_unfixed_scheduler_DB G d n = parserS_get_unfixed_scheduler_DB G (parserFS_to_parserS_derivation d) n"
  apply(induct n)
   apply(simp add: parserFS_get_unfixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
   apply(clarsimp)
   apply(rename_tac y)(*strict*)
   apply(simp add: get_configuration_def)
   apply(case_tac y)
   apply(rename_tac y option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b)(*strict*)
   apply(simp add: parserFS.derivation_initial_def parserFS_to_parserS_derivation_def)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: parserS_get_scheduler_def parserFS_initial_configurations_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac n y)(*strict*)
     apply (metis parserFS.derivation_initial_is_derivation)
    apply(rename_tac n y)(*strict*)
    apply(force)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def get_configuration_def)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) (Suc n) = length (parserFS_conf_fixed (the(get_configuration(d (Suc n)))))")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
     apply(rename_tac n e1 e2 c1 c2)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def get_configuration_def)
  apply(case_tac "parserFS_to_parserS_derivation d (Suc n)")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac n e1 e2 c1 c2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac n e1 e2 c1 c2 option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 b a)(*strict*)
  apply(subgoal_tac "a=e2")
   apply(rename_tac n e1 e2 c1 c2 b a)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac n e1 e2 c1 c2 b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) n = length (parserFS_conf_fixed (the(get_configuration(d n))))")
   apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
   prefer 2
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
     apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
    apply(force)
   apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
   apply(force)
  apply(rename_tac n e1 e2 c1 c2 b)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def get_configuration_def)
  apply(simp add: parserFS_to_parserS_derivation_def parserS_get_scheduler_def)
  apply(clarsimp)
  done

lemma parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_uniform: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> maximum_of_domain (parserFS_to_parserS_derivation dh) n
  \<Longrightarrow> parserFS.derivation_initial G dc'
  \<Longrightarrow> parserFS_get_unfixed_scheduler_DB G dh n \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> sUF \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> sUF \<in> parser_unfixed_schedulers G
  \<Longrightarrow> parserFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) dc n
  \<Longrightarrow> maximum_of_domain dc' (n+n')
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> parserFS_get_fixed_scheduler_DB G dh x = parserFS_get_fixed_scheduler_DB G dc' x"
  apply(rule_tac
      t="parserFS_get_fixed_scheduler_DB G dc' x"
      and s="parserS_get_fixed_scheduler_DB G (parserFS_to_parserS_derivation dc') x"
      in ssubst)
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB)
     apply(force)
    apply(simp add: parserFS.derivation_initial_def)
   apply(rule parserFS.not_none_before_maximum_of_domain)
      apply(force)
     apply(simp add: parserFS.derivation_initial_def)
    apply(force)
   apply(force)
  apply(rule_tac
      t="parserFS_to_parserS_derivation dc'"
      and s="derivation_append (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) dc n"
      in ssubst)
   apply(force)
  apply(thin_tac "parserFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) dc n")
  apply(rule_tac
      t="parserS_get_fixed_scheduler_DB G (derivation_append (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) dc n) x"
      and s="parserS_get_fixed_scheduler_DB G ((parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) ) x"
      in ssubst)
   apply(rule parserS.AX_get_fixed_scheduler_DB_restrict)
     apply(force)+
   defer
   apply(rule_tac
      t="parserS_get_fixed_scheduler_DB G (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) x"
      and s="parserS_get_fixed_scheduler_DB G (parserFS_to_parserS_derivation dh) x"
      in ssubst)
    defer
    apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB)
      apply(force)
     apply(simp add: parserFS.derivation_initial_def)
    apply(rule parserFS.not_none_before_maximum_of_domain)
       apply(force)
      apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(force)
   apply(subgoal_tac "parserS.derivation_initial G (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n)")
    apply(simp add: parserS.derivation_initial_def)
   apply(rule parserS.sched_modification_preserves_derivation_initial)
         apply(force)
        prefer 6
        apply(simp add: parserS.replace_unfixed_scheduler_DB_def)
       apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
      apply(force)
     apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) n = parser_fixed_input_length_recN dh n")
      apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
       apply(clarsimp)
       apply(rename_tac e c)(*strict*)
       apply(simp add: parserS_get_unfixed_scheduler_DB_def parserFS_get_unfixed_scheduler_DB_def parserFS_to_parserS_derivation_def)
       apply(simp add: get_configuration_def parserS_get_scheduler_def)
       apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) n = length (parserFS_conf_fixed (the(get_configuration(dh n))))")
        apply(rename_tac e c)(*strict*)
        prefer 2
        apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
          apply(rename_tac e c)(*strict*)
          apply(force)
         apply(rename_tac e c)(*strict*)
         apply(force)
        apply(rename_tac e c)(*strict*)
        apply(force)
       apply(rename_tac e c)(*strict*)
       apply(simp add: parserFS_get_fixed_scheduler_DB_def get_configuration_def)
       apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) n = parser_fixed_input_length_recN dh n")
        apply(rename_tac e c)(*strict*)
        apply(force)
       apply(rename_tac e c)(*strict*)
       apply(rule sym)
       apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
        apply(rename_tac e c)(*strict*)
        apply(force)
       apply(rename_tac e c)(*strict*)
       apply(simp add: parserFS.derivation_initial_def)
      apply(simp add: maximum_of_domain_def)
      apply(clarsimp)
      apply(rename_tac y ya)(*strict*)
      apply(case_tac yb)
      apply(rename_tac y ya option b)(*strict*)
      apply(force)
     apply(rule sym)
     apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
      apply(force)
     apply(simp add: parserFS.derivation_initial_def)
    apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dh x= Some (pair e c)")
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: parserS_get_fixed_scheduler_DB_def)
  apply(case_tac "parserFS_to_parserS_derivation dh x")
   apply(simp add: parserFS_to_parserS_derivation_def)
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b e c)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) x"
      and s="parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) x"
      in ssubst)
   apply(rename_tac option b e c)(*strict*)
   apply(thin_tac "parserFS_to_parserS_derivation dh x = Some (pair option b)")
   apply(induct x arbitrary: e c)
    apply(rename_tac option b e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac x option b e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x e c)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh x = Some (pair e1 c1) \<and> dh (Suc x) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
    apply(rename_tac x e c)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc x"
      in parserFS.step_detail_before_some_position)
      apply(rename_tac x e c)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
     apply(rename_tac x e c)(*strict*)
     apply(force)
    apply(rename_tac x e c)(*strict*)
    apply(force)
   apply(rename_tac x e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x c e1 e2 c1)(*strict*)
   apply(erule_tac
      x="e1"
      in meta_allE)
   apply(erule_tac
      x="c1"
      in meta_allE)
   apply(clarsimp)
   apply(rule_tac
      t="parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) x"
      and s="parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) x"
      in ssubst)
    apply(rename_tac x c e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac x c e1 e2 c1)(*strict*)
   apply(thin_tac "parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) x = parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) x")
   apply(rename_tac x c e1 e2 c1)(*strict*)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def)
   apply(simp add: parserS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>c. parserFS_to_parserS_derivation dh (Suc x) = Some (pair (Some e2) c)")
    apply(rename_tac x c e1 e2 c1)(*strict*)
    apply(clarsimp)
   apply(rename_tac x c e1 e2 c1)(*strict*)
   apply(rule parserFS_to_parserS_derivation_preserves_step_labels)
     apply(rename_tac x c e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac x c e1 e2 c1)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
   apply(rename_tac x c e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac option b e c)(*strict*)
  apply(simp add: parserS_get_scheduler_def)
  apply(simp add: parserS.replace_unfixed_scheduler_DB_def)
  apply(simp add: parserS.map_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def)
  apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: parserS_set_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac option b e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac option b e c ea ca)(*strict*)
   apply(subgoal_tac "\<exists>c. parserFS_to_parserS_derivation dh n = Some (pair ea c)")
    apply(rename_tac option b e c ea ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac option b e c ea ca cb)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) x - length (parserS_get_fixed_scheduler_DB G (parserFS_to_parserS_derivation dh) x) = 0")
     apply(rename_tac option b e c ea ca cb)(*strict*)
     apply(clarsimp)
     apply(simp add: parserS_get_fixed_scheduler_DB_def)
     apply(simp add: parserS_set_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
    apply(rename_tac option b e c ea ca cb)(*strict*)
    apply(simp add: parserS_set_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
    apply(simp add: parserS_get_fixed_scheduler_DB_def)
    apply(simp add: parserS_set_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac option b e c ea ca cb)(*strict*)
       apply(force)
      apply(rename_tac option b e c ea ca cb)(*strict*)
      apply(rule parserS.derivation_initial_belongs)
       apply(rename_tac option b e c ea ca cb)(*strict*)
       apply(force)
      apply(rename_tac option b e c ea ca cb)(*strict*)
      apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac option b e c ea ca cb)(*strict*)
     apply(subgoal_tac "parserS.derivation_initial G (parserFS_to_parserS_derivation dh)")
      apply(rename_tac option b e c ea ca cb)(*strict*)
      apply(simp add: parserS.derivation_initial_def)
     apply(rename_tac option b e c ea ca cb)(*strict*)
     apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac option b e c ea ca cb)(*strict*)
    apply(force)
   apply(rename_tac option b e c ea ca)(*strict*)
   apply(rule parserFS_to_parserS_derivation_preserves_step_labels)
     apply(rename_tac option b e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac option b e c ea ca)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
   apply(rename_tac option b e c ea ca)(*strict*)
   apply(force)
  apply(rename_tac option b e c)(*strict*)
  apply(simp add: maximum_of_domain_def)
  apply(clarsimp)
  apply(rename_tac option b e c y ya)(*strict*)
  apply(case_tac c)
  apply(rename_tac option b e c y ya optiona ba)(*strict*)
  apply(force)
  done

lemma parserFS_to_parserS_derivation_preserves_maximum_of_domain: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (parserFS_to_parserS_derivation d) n"
  apply(simp add: maximum_of_domain_def parserFS_to_parserS_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

definition parserS_to_parserFS_derivation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf)derivation
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserFS_conf)derivation"
  where
    "parserS_to_parserFS_derivation G d \<equiv>
  \<lambda>n.
  case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow>
      Some (pair e
        \<lparr>parserFS_conf_fixed
          = take
            (parser_fixed_input_length_recN d n)
            (parserS_conf_scheduler c),
        parserFS_conf_stack = parserS_conf_stack c,
        parserFS_conf_scheduler
          = drop
              (parser_fixed_input_length_recN d n)
              (parserS_conf_scheduler c)\<rparr>)"

lemma parserS_to_parserFS_derivation_preserves_derivation_initial: "
  valid_parser P
  \<Longrightarrow> parserS.derivation_initial P d
  \<Longrightarrow> parserFS.derivation_initial P (parserS_to_parserFS_derivation P d)"
  apply(simp add: parserS_to_parserFS_derivation_def)
  apply(simp add: parserFS.derivation_initial_def)
  apply(rule conjI)
   prefer 2
   apply(simp add: parserS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac b)(*strict*)
   apply(simp add: parserS_initial_configurations_def parserFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def parserFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: dom_abbreviation)
   apply(rule conjI)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      x="w @ [parser_bottom P]"
      in exI)
   apply(force)
  apply(simp add: parserFS.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac "i")
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: parserS.derivation_initial_def)
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation P c1 e2 c2")
   apply(rename_tac nat a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac nat a)(*strict*)
     apply(simp add: parserS.derivation_initial_def)
    apply(rename_tac nat a)(*strict*)
    apply(force)
   apply(rename_tac nat a)(*strict*)
   apply(force)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_step_relation_def parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(simp add: parserS.derivation_initial_def)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "valid_parser_step_label P e2")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(rule conjI)
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
   apply(rule_tac
      x="xc"
      in exI)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(case_tac "parser_fixed_input_length_recN d nat - length (rule_rpop e2)")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   apply(rule disjI1)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
   apply(rule_tac
      x="drop (parser_fixed_input_length_recN d nat) (kPrefix k (w @ [parser_bottom P]))"
      in exI)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "length (rule_rpush e2) \<le> length (rule_rpop e2)")
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
    prefer 2
    apply (metis valid_parser_rules_rhs_gets_shorter)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
   apply(case_tac "(parser_fixed_input_length_recN d nat) \<le> (length (kPrefix k (w @ [parser_bottom P])))")
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
    apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
   apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) (length (kPrefix k (w @ [parser_bottom P]))) = (length (kPrefix k (w @ [parser_bottom P])))")
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa nata)(*strict*)
  apply(rule disjI2)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa nata c k w xc)(*strict*)
  apply(subgoal_tac "length (rule_rpush e2) \<le> length (rule_rpop e2)")
   apply(rename_tac nat e1 e2 c1 c2 x xa nata c k w xc)(*strict*)
   prefer 2
   apply (metis valid_parser_rules_rhs_gets_shorter)
  apply(rename_tac nat e1 e2 c1 c2 x xa nata c k w xc)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) (length (kPrefix k (w @ [parser_bottom P]))) = parser_fixed_input_length_recN d nat")
   apply(rename_tac nat e1 e2 c1 c2 x xa nata c k w xc)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa nata c k w xc)(*strict*)
  apply(clarsimp)
  done

lemma parserS_to_parserFS_derivation_preserves_maximum_of_domain: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (parserS_to_parserFS_derivation G d) n"
  apply(simp add: maximum_of_domain_def parserS_to_parserFS_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma parserFS_parser_fixed_input_length_recN_from_fixed: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> parser_fixed_input_length_recN d n = length (parserFS_conf_fixed (the(get_configuration(d n))))"
  apply (metis parserFS.derivation_initial_is_derivation parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
  done

lemma parser_S_FS_relation_coincide_hlp: "
  valid_parser G2
  \<Longrightarrow> parserFS.derivation_initial G2 d2
  \<Longrightarrow> maximum_of_domain d2 x
  \<Longrightarrow> parserS_to_parserFS_derivation G2 (parserFS_to_parserS_derivation d2) xa = d2 xa"
  apply(induct xa)
   apply(simp add: parserFS_to_parserS_derivation_def parserS_to_parserFS_derivation_def)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(case_tac c)
    apply(rename_tac c parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
    apply(clarsimp)
    apply(rename_tac parserFS_conf_fixed parserFS_conf_stack parserFS_conf_scheduler)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
    apply(clarsimp)
    apply(simp add: parserFS_initial_configurations_def)
   apply (metis parserFS.derivation_initial_is_derivation parserFS.some_position_has_details_at_0)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "d2 (Suc xa)")
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_to_parserS_derivation_def parserS_to_parserFS_derivation_def)
  apply(rename_tac xa a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 xa = Some (pair e1 c1) \<and> d2 (Suc xa) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G2 c1 e2 c2")
   apply(rename_tac xa a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc xa"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac xa a)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
    apply(rename_tac xa a)(*strict*)
    apply(force)
   apply(rename_tac xa a)(*strict*)
   apply(force)
  apply(rename_tac xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_to_parserFS_derivation_def)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) xa = parser_fixed_input_length_recN d2 xa")
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
    apply(rename_tac xa e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) (Suc xa) = parser_fixed_input_length_recN d2 (Suc xa)")
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
    apply(rename_tac xa e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: parserFS_to_parserS_derivation_def parserS_to_parserFS_derivation_def)
  apply(subgoal_tac "\<exists> c. d2 0 = Some (pair None c)")
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: parserFS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d2 0")
    apply(rename_tac xa e1 e2 c1 c2)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa e1 e2 c1 c2 a)(*strict*)
   apply(case_tac a)
   apply(rename_tac xa e1 e2 c1 c2 a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d2 xa = length (parserFS_conf_fixed c1)")
   apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d2 (Suc xa) = length (parserFS_conf_fixed c2)")
    apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. parserFS_string_state c = w @ parserFS_string_state c1")
     apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
     prefer 2
     apply(rule_tac
      d="d2"
      in parserFS.derivation_monotonically_dec)
          apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
          apply(force)
         apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
         apply(force)
        apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
        apply(rule parserFS.derivation_initial_belongs)
         apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
         apply(force)
        apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
        apply(force)
       apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
       apply(simp add: parserFS.derivation_initial_def)
      apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
      apply(force)
     apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
     apply(force)
    apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
    apply(subgoal_tac "\<exists>w. parserFS_string_state c1 = w @ parserFS_string_state c2")
     apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
     prefer 2
     apply(rule_tac
      d="d2"
      and i="xa"
      and j="Suc 0"
      in parserFS.derivation_monotonically_dec)
          apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
          apply(force)
         apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
         apply(force)
        apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
        apply(rule parserFS.derivation_initial_belongs)
         apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
         apply(force)
        apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
        apply(force)
       apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
       apply(simp add: parserFS.derivation_initial_def)
      apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
      apply(force)
     apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
     apply(force)
    apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
    apply(simp add: parserFS_string_state_def)
    apply(simp add: parserFS_step_relation_def)
    apply(subgoal_tac "valid_parser_step_label G2 e2")
     apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
     prefer 2
     apply(simp add: valid_parser_def)
    apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa e1 e2 c1 c2 c w wa xb v)(*strict*)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac xa e1 e2 c1 c2 c w wa xb v k wb)(*strict*)
    apply(case_tac c2)
    apply(rename_tac xa e1 e2 c1 c2 c w wa xb v k wb parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa e1 e2 c1 c w wa xb v k wb parserFS_conf_fixeda parserFS_conf_schedulera)(*strict*)
    apply(erule disjE)
     apply(rename_tac xa e1 e2 c1 c w wa xb v k wb parserFS_conf_fixeda parserFS_conf_schedulera)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa e1 e2 c1 c w wa xb k wb parserFS_conf_schedulera popnew)(*strict*)
     apply (metis append_length_inc length_append)
    apply(rename_tac xa e1 e2 c1 c w wa xb v k wb parserFS_conf_fixeda parserFS_conf_schedulera)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d2 (Suc xa) = length (parserFS_conf_fixed (the(get_configuration(d2 (Suc xa)))))")
    apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
   apply(rule parserFS_parser_fixed_input_length_recN_from_fixed)
     apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
     apply(force)+
  apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d2 xa = length (parserFS_conf_fixed (the(get_configuration(d2 xa))))")
   apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
  apply(rule parserFS_parser_fixed_input_length_recN_from_fixed)
    apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
    apply(force)+
  done

corollary parser_S_FS_relation_coincide: "
  (\<lambda>G1 G2 d1 d2. (valid_parser G1) \<and> (G1=G2) \<and> parserFS.derivation_initial G2 d2 \<and> (\<exists>n. maximum_of_domain d2 n) \<and> parserFS_to_parserS_derivation d2 = d1) = (\<lambda>G1 G2 d1 d2. (valid_parser G1) \<and> (G1=G2) \<and> parserS.derivation_initial G1 d1 \<and> (\<exists>n. maximum_of_domain d1 n) \<and> parserS_to_parserFS_derivation G1 d1 = d2)"
  apply(rule ext)+
  apply(rename_tac G1 G2 d1 d2)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G1 G2 d1 d2)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 d1 x)(*strict*)
    apply (metis parserS_to_parserFS_derivation_preserves_derivation_initial)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 d1 x)(*strict*)
    apply (metis parserS_to_parserFS_derivation_preserves_maximum_of_domain)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(simp add: parserS_to_parserFS_derivation_def parserFS_to_parserS_derivation_def)
   apply(rule ext)
   apply(rename_tac G2 d1 x n)(*strict*)
   apply(case_tac "d1 n")
    apply(rename_tac G2 d1 x n)(*strict*)
    apply(clarsimp)
   apply(rename_tac G2 d1 x n a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac G2 d1 x n a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 G2 d1 d2)(*strict*)
  apply(clarsimp)
  apply(rename_tac G2 d2 x)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 d2 x)(*strict*)
   apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
  apply(rename_tac G2 d2 x)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 d2 x)(*strict*)
   apply (metis parserFS_to_parserS_derivation_preserves_maximum_of_domain)
  apply(rename_tac G2 d2 x)(*strict*)
  apply(rule ext)
  apply(rename_tac G2 d2 x xa)(*strict*)
  apply(rule parser_S_FS_relation_coincide_hlp)
    apply(rename_tac G2 d2 x xa)(*strict*)
    apply(force)+
  done

lemma parserS_vs_parserFS_inst_AX_AX_initial_contained1: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>c1. c1 \<in> parserS_initial_configurations G1 \<longrightarrow> (\<exists>c2. parserFS.derivation_initial G1 (der1 c2) \<and> Ex (maximum_of_domain (der1 c2)) \<and> parserFS_to_parserS_derivation (der1 c2) = der1 c1)))"
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply(rule_tac
      x="\<lparr>parserFS_conf_fixed=[], parserFS_conf_stack = parserS_conf_stack c1, parserFS_conf_scheduler=parserS_conf_scheduler c1\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 c1)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 c1)(*strict*)
    apply(rule parserFS.der1_is_derivation)
   apply(rename_tac G1 c1)(*strict*)
   apply(simp add: der1_def)
   apply(simp add: parserFS_initial_configurations_def parserFS_configurations_def parserS_initial_configurations_def parserS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 w)(*strict*)
   apply(simp add: dom_abbreviation)
   apply(rule conjI)
    apply(rename_tac G1 w)(*strict*)
    apply(force)
   apply(rename_tac G1 w)(*strict*)
   apply(rule_tac
      x="w@[parser_bottom G1]"
      in exI)
   apply(force)
  apply(rename_tac G1 c1)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c1)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply (metis der1_maximum_of_domain)
  apply(rename_tac G1 c1)(*strict*)
  apply(rule ext)
  apply(rename_tac G1 c1 x)(*strict*)
  apply(simp add: parserFS_to_parserS_derivation_def der1_def der1_def)
  done

lemma parserS_vs_parserFS_inst_AX_AX_initial_contained2: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>c2. c2 \<in> parserFS_initial_configurations G1 \<longrightarrow> parserFS.derivation_initial G1 (der1 c2) \<and> Ex (maximum_of_domain (der1 c2)) \<and> (\<exists>c1. parserFS_to_parserS_derivation (der1 c2) = der1 c1)))"
  apply(clarsimp)
  apply(rename_tac G1 c2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c2)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 c2)(*strict*)
    apply(rule parserFS.der1_is_derivation)
   apply(rename_tac G1 c2)(*strict*)
   apply(simp add: der1_def)
  apply(rename_tac G1 c2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c2)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply (metis der1_maximum_of_domain)
  apply(rename_tac G1 c2)(*strict*)
  apply(rule_tac
      x="\<lparr>parserS_conf_stack = parserFS_conf_stack c2, parserS_conf_scheduler=parserFS_conf_fixed c2@parserFS_conf_scheduler c2\<rparr>"
      in exI)
  apply(rule ext)
  apply(rename_tac G1 c2 x)(*strict*)
  apply(simp add: parserFS_to_parserS_derivation_def der1_def der1_def)
  done

lemma parserS_vs_parserFS_inst_AX_on_derivation_initial1: "
  (\<forall>G1 d1. valid_parser G1 \<and> (\<exists>d2. parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<and> parserFS_to_parserS_derivation d2 = d1) \<longrightarrow> parserS.derivation_initial G1 d1)"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
  done

lemma parserS_vs_parserFS_inst_AX_on_finite1: "
  (\<forall>G1 d1. valid_parser G1 \<and> (\<exists>d2. parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<and> parserFS_to_parserS_derivation d2 = d1) \<longrightarrow> Ex (maximum_of_domain d1))"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(rule_tac
      x="x"
      in exI)
  apply (metis parserFS_to_parserS_derivation_preserves_maximum_of_domain)
  done

lemma parserS_vs_parserFS_inst_AX_equal_length: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n1. maximum_of_domain (parserFS_to_parserS_derivation d2) n1 \<longrightarrow> (\<forall>n2. maximum_of_domain d2 n2 \<longrightarrow> n1 = n2)))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n1 x n2)(*strict*)
  apply (metis parserS.derivation_initial_is_derivation parserS.maximum_of_domainUnique parserFS_to_parserS_derivation_preserves_derivation_initial parserFS_to_parserS_derivation_preserves_maximum_of_domain)
  done

lemma parserS_vs_parserFS_inst_AX_simulate12: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (parserFS_to_parserS_derivation d2) n \<longrightarrow> maximum_of_domain d2 n \<longrightarrow> (\<forall>e1 c1'. parserS_step_relation G1 (the (get_configuration (parserFS_to_parserS_derivation d2 n))) e1 c1' \<longrightarrow> (\<exists>c2'. parserFS_step_relation G1 (the (get_configuration (d2 n))) e1 c2' \<and> e1 \<in> parser_rules G1 \<and> (let d2' = derivation_append d2 (der2 (the (get_configuration (d2 n))) e1 c2') n in parserFS.derivation_initial G1 d2' \<and> Ex (maximum_of_domain d2') \<and> parserFS_to_parserS_derivation d2' = derivation_append (parserFS_to_parserS_derivation d2) (der2 (the (get_configuration (parserFS_to_parserS_derivation d2 n))) e1 c1') n)))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x e1 c1')(*strict*)
  apply(subgoal_tac "n=x")
   apply(rename_tac G1 d2 n x e1 c1')(*strict*)
   prefer 2
   apply (metis parserS_vs_parserFS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x e1 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1')(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 x = Some (pair e c)")
   apply(rename_tac G1 d2 x e1 c1')(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x e1 c1')(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x e1 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(subgoal_tac "\<exists>c2'. parserFS_step_relation G1 (the (get_configuration (d2 x))) e1 c2' \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack c2', parserS_conf_scheduler = parserFS_conf_fixed c2'@parserFS_conf_scheduler c2'\<rparr> = c1'")
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
   apply(rule_tac
      x="c2'"
      in exI)
   apply(simp add: Let_def)
   apply(rule conjI)
    apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
    apply(simp add: parserFS_step_relation_def)
   apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
   apply(rule context_conjI)
    apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
     apply(rule parserFS.derivation_append_preserves_derivation)
       apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
      apply (metis parserFS.der2_is_derivation)
     apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def get_configuration_def)
    apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
    apply(simp add: derivation_append_def)
   apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
    apply(rule_tac
      x="x+Suc 0"
      in exI)
    apply (metis Nat.add_0_right add_Suc_right concat_has_max_dom der2_maximum_of_domain)
   apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
   apply(rule ext)
   apply(rename_tac G1 d2 x e1 e c c2' xa)(*strict*)
   apply(simp add: derivation_append_def parserFS_to_parserS_derivation_def derivation_append_def)
   apply(case_tac "xa \<le> x")
    apply(rename_tac G1 d2 x e1 e c c2' xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 x e1 e c c2' xa)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(simp (no_asm) add: get_configuration_def)
  apply(subgoal_tac "parserS_step_relation G1 (the (get_configuration (Some (pair e \<lparr>parserS_conf_stack = parserFS_conf_stack c, parserS_conf_scheduler = parserFS_conf_fixed c@parserFS_conf_scheduler c\<rparr>)))) e1 c1'")
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def get_configuration_def)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)

  apply(thin_tac "parserS_step_relation G1 (the (get_configuration (parserFS_to_parserS_derivation d2 x))) e1 c1'")
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c)
  apply(rename_tac G1 d2 x e1 c1' e c parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
  apply(rename_tac cf ch cl cr)
  apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
  apply(subgoal_tac "c1' \<in> parserS_configurations G1")
   apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G1 e1")
    apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
    prefer 2
    apply(simp add: valid_parser_def parserS_step_relation_def)
   apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
   apply(simp add: parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e1 c1' e ch cr xa xb)(*strict*)
   apply(case_tac c1')
   apply(rename_tac G1 d2 x e1 c1' e ch cr xa xb parserS_conf_stacka parserS_conf_schedulera)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e1 e ch cr xa xb)(*strict*)
   apply(subgoal_tac "prefix ch (rule_rpop e1) \<or> prefix (rule_rpop e1) ch")
    apply(rename_tac G1 d2 x e1 e ch cr xa xb)(*strict*)
    prefer 2
    apply (metis mutual_prefix_prefix)
   apply(rename_tac G1 d2 x e1 e ch cr xa xb)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 d2 x e1 e ch cr xa xb)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac G1 d2 x e1 e ch cr xa xb c)(*strict*)
    apply(case_tac e1)
    apply(rename_tac G1 d2 x e1 e ch cr xa xb c rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 x e ch xa xb c rule_lpop rule_lpush rule_rpush)(*strict*)
    apply(simp add: parserFS_step_relation_def)
    apply(rule_tac
      x="\<lparr>parserFS_conf_fixed = rule_rpush, parserFS_conf_stack = xa @ rule_lpush, parserFS_conf_scheduler = xb\<rparr>"
      in exI)
    apply(rename_tac G1 d2 x e ch xa xb c rule_lpop rule_lpush rule_rpush)(*strict*)
    apply(clarsimp)
    apply(simp add: valid_parser_step_label_def)
    apply(clarsimp)
    apply(rename_tac G1 d2 x e ch xa xb c rule_lpop rule_lpush rule_rpush k w xd)(*strict*)
    apply(rule_tac
      x="xd"
      in exI)
    apply(force)
   apply(rename_tac G1 d2 x e1 e ch cr xa xb)(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e1 e cr xa c)(*strict*)
   apply(case_tac e1)
   apply(rename_tac G1 d2 x e1 e cr xa c rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e cr xa c rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
   apply(simp add: parserFS_step_relation_def)
   apply(rule_tac
      x="\<lparr>parserFS_conf_fixed = rule_rpush@c, parserFS_conf_stack = xa @ rule_lpush, parserFS_conf_scheduler = cr\<rparr>"
      in exI)
   apply(rename_tac G1 d2 x e cr xa c rule_lpop rule_rpop rule_lpush rule_rpush)(*strict*)
   apply(clarsimp)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e cr xa c rule_lpop rule_lpush rule_rpush k w xc)(*strict*)
   apply(rule_tac
      x="xc"
      in exI)
   apply(force)
  apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
  apply(rule parserS.AX_step_relation_preserves_belongsC)
    apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
  apply(rule_tac
      i="x"
      and d="parserFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
   apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
   apply (metis parserS.derivation_initial_belongs parserFS_to_parserS_derivation_preserves_derivation_initial)
  apply(rename_tac G1 d2 x e1 c1' e ch cl cr)(*strict*)
  apply(simp add: parserFS_to_parserS_derivation_def)
  done

lemma parserS_vs_parserFS_inst_AX_simulate21: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (parserFS_to_parserS_derivation d2) n \<longrightarrow> maximum_of_domain d2 n \<longrightarrow> (\<forall>e2 c2'. parserFS_step_relation G1 (the (get_configuration (d2 n))) e2 c2' \<longrightarrow> (\<exists>c1'. parserS_step_relation G1 (the (get_configuration (parserFS_to_parserS_derivation d2 n))) e2 c1' \<and> e2 \<in> parser_rules G1 \<and> (let d2' = derivation_append d2 (der2 (the (get_configuration (d2 n))) e2 c2') n in parserFS.derivation_initial G1 d2' \<and> Ex (maximum_of_domain d2') \<and> parserFS_to_parserS_derivation d2' = derivation_append (parserFS_to_parserS_derivation d2) (der2 (the (get_configuration (parserFS_to_parserS_derivation d2 n))) e2 c1') n)))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x e2 c2')(*strict*)
  apply(subgoal_tac "n=x")
   apply(rename_tac G1 d2 n x e2 c2')(*strict*)
   prefer 2
   apply (metis parserS_vs_parserFS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x e2 c2')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2')(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 x = Some (pair e c)")
   apply(rename_tac G1 d2 x e2 c2')(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x e2 c2')(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x e2 c2')(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x e2 c2')(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x e2 c2')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule_tac
      x="\<lparr>parserS_conf_stack = parserFS_conf_stack c2', parserS_conf_scheduler = parserFS_conf_fixed c2'@parserFS_conf_scheduler c2'\<rparr>"
      in exI)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: parserS_step_relation_def parserFS_step_relation_def get_configuration_def parserFS_to_parserS_derivation_def get_configuration_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e2 c2' e c xa v)(*strict*)
   apply(erule disjE)
    apply(rename_tac G1 d2 x e2 c2' e c xa v)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 x e2 c2' e c xa v)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(simp add: Let_def)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: parserFS_step_relation_def)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
    apply(rule parserFS.derivation_append_preserves_derivation)
      apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
     apply (metis parserFS.der2_is_derivation)
    apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def get_configuration_def)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(rule_tac
      x="x+Suc 0"
      in exI)
   apply (metis Nat.add_0_right add_Suc_right concat_has_max_dom der2_maximum_of_domain)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule ext)
  apply(rename_tac G1 d2 x e2 c2' e c xa)(*strict*)
  apply(simp add: derivation_append_def parserFS_to_parserS_derivation_def derivation_append_def)
  apply(case_tac "xa \<le> x")
   apply(rename_tac G1 d2 x e2 c2' e c xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2' e c xa)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def)
  done

lemma parserS_vs_parserFS_inst_hlp_bisimulation_compatible_with_crop: "
  valid_parser G1
  \<Longrightarrow> parserFS.derivation_initial G1 dh
  \<Longrightarrow> maximum_of_domain dh x
  \<Longrightarrow> maximum_of_domain (parserFS_to_parserS_derivation dh) n
  \<Longrightarrow> derivation_append_fit (parserFS_to_parserS_derivation dh) dc n
  \<Longrightarrow> parserFS.derivation_initial G1 dc'
  \<Longrightarrow> parserFS_to_parserS_derivation dc' = derivation_append (parserFS_to_parserS_derivation dh) dc n
  \<Longrightarrow> maximum_of_domain dc' xb
  \<Longrightarrow> xa \<le> n
  \<Longrightarrow> dh xa = dc' xa"
  apply(subgoal_tac "x=n")
   apply(subgoal_tac "x\<le>xb")
    apply(clarsimp)
    defer
    prefer 2
    apply (metis parserS_vs_parserFS_inst_AX_equal_length)
   apply(rule_tac
      ?d1.0="(parserFS_to_parserS_derivation dh)"
      and ?d2.0="dc"
      in parserS.derivation_append_minimal_maximum_of_domain)
       apply(force)+
      prefer 4
      apply(force)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(rule_tac
      t="derivation_append (parserFS_to_parserS_derivation dh) dc n"
      and s="parserFS_to_parserS_derivation dc'"
      in ssubst)
      apply(force)
     apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rule_tac
      t="derivation_append (parserFS_to_parserS_derivation dh) dc n"
      and s="parserFS_to_parserS_derivation dc'"
      in ssubst)
     apply(force)
    apply (metis parserFS_to_parserS_derivation_preserves_maximum_of_domain)
   apply(force)
  apply(induct xa)
   apply(clarsimp)
   apply(subgoal_tac "parserFS_to_parserS_derivation dc' 0 = derivation_append (parserFS_to_parserS_derivation dh) dc n 0")
    prefer 2
    apply(force)
   apply(thin_tac "parserFS_to_parserS_derivation dc' = derivation_append (parserFS_to_parserS_derivation dh) dc n")
   apply(simp add: parserFS_to_parserS_derivation_def derivation_append_def)
   apply(subgoal_tac "\<exists>c. dc' 0 = Some (pair None c)")
    apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
     apply(clarsimp)
     apply(rename_tac c ca)(*strict*)
     apply(simp add: parserFS.derivation_initial_def parserS.derivation_initial_def)
     apply(clarsimp)
     apply(simp add: parserFS_initial_configurations_def)
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(rule parserFS.some_position_has_details_at_0)
    apply(simp add: parserFS.derivation_initial_def)
    apply(force)
   apply(rule parserFS.some_position_has_details_at_0)
   apply(simp add: parserFS.derivation_initial_def)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parserFS_to_parserS_derivation dc' xa = derivation_append (parserFS_to_parserS_derivation dh) dc n xa")
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(subgoal_tac "parserFS_to_parserS_derivation dc' (Suc xa) = derivation_append (parserFS_to_parserS_derivation dh) dc n (Suc xa)")
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(thin_tac "parserFS_to_parserS_derivation dc' = derivation_append (parserFS_to_parserS_derivation dh) dc n")
  apply(rename_tac xa)(*strict*)
  apply(subgoal_tac "\<exists>e c. dc' (Suc xa) = Some (pair e c)")
   apply(rename_tac xa)(*strict*)
   apply(subgoal_tac "\<exists>e c. dh (Suc xa) = Some (pair e c)")
    apply(rename_tac xa)(*strict*)
    defer
    apply(rule parserFS.some_position_has_details_before_max_dom)
      apply(rename_tac xa)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
      apply(force)
     apply(rename_tac xa)(*strict*)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac xa)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(simp add: parserFS_to_parserS_derivation_def derivation_append_def)
  apply(clarsimp)
  apply(rename_tac xa ea c ca)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh xa = Some (pair e1 c1) \<and> dh (Suc xa) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G1 c1 e2 c2")
   apply(rename_tac xa ea c ca)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc xa"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac xa ea c ca)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
    apply(rename_tac xa ea c ca)(*strict*)
    apply(force)
   apply(rename_tac xa ea c ca)(*strict*)
   apply(force)
  apply(rename_tac xa ea c ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa c ca e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dc' xa = Some (pair e1 c1) \<and> dc' (Suc xa) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G1 c1 e2 c2")
   apply(rename_tac xa c ca e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc xa"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac xa c ca e1 e2 c1)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
    apply(rename_tac xa c ca e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac xa c ca e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac xa c ca e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(simp add: parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac xa c ca e1 e2 c1 x v)(*strict*)
  apply(erule_tac
      P="\<exists>popnew. parserFS_conf_fixed c1 @ popnew = v @ rule_rpush e2 \<and> parserFS_conf_scheduler c1 = popnew @ parserFS_conf_scheduler c \<and> parserFS_conf_fixed c = rule_rpush e2"
      in disjE)
   apply(rename_tac xa c ca e1 e2 c1 x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa c ca e1 e2 c1 x v popnew)(*strict*)
   apply(erule disjE)
    apply(rename_tac xa c ca e1 e2 c1 x v popnew)(*strict*)
    apply(clarsimp)
   apply(rename_tac xa c ca e1 e2 c1 x v popnew)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa c ca e1 e2 c1 x v)(*strict*)
  apply(erule disjE)
   apply(rename_tac xa c ca e1 e2 c1 x v)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa c ca e1 e2 c1 x v remainder popnew)(*strict*)
   prefer 2
   apply(rename_tac xa c ca e1 e2 c1 x v)(*strict*)
   apply(clarsimp)
  apply(rename_tac xa c ca e1 e2 c1 x v remainder popnew)(*strict*)
  apply(case_tac c)
  apply(rename_tac xa c ca e1 e2 c1 x v remainder popnew parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera)(*strict*)
  apply(case_tac ca)
  apply(rename_tac xa c ca e1 e2 c1 x v remainder popnew parserFS_conf_fixeda parserFS_conf_stacka parserFS_conf_schedulera parserFS_conf_fixedaa parserFS_conf_stackaa parserFS_conf_scheduleraa)(*strict*)
  apply(clarsimp)
  done

lemma parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_crop1: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>dh. parserFS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain (parserFS_to_parserS_derivation dh) n \<longrightarrow> (\<forall>dc. derivation_append_fit (parserFS_to_parserS_derivation dh) dc n \<longrightarrow> (\<forall>dc'. parserFS.derivation_initial G1 dc' \<and> Ex (maximum_of_domain dc') \<and> parserFS_to_parserS_derivation dc' = derivation_append (parserFS_to_parserS_derivation dh) dc n \<longrightarrow> (\<forall>x\<le>n. dh x = dc' x))))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x dc dc' xa xb)(*strict*)
  apply(rule parserS_vs_parserFS_inst_hlp_bisimulation_compatible_with_crop)
          apply(rename_tac G1 dh n x dc dc' xa xb)(*strict*)
          apply(force)+
  done

lemma parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_crop2: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>dh. parserFS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain dh n \<longrightarrow> (\<forall>dc'. derivation_append_fit dh dc' n \<longrightarrow> parserFS.derivation_initial G1 (derivation_append dh dc' n) \<and> Ex (maximum_of_domain (derivation_append dh dc' n)) \<longrightarrow> (\<forall>x\<le>n. parserFS_to_parserS_derivation dh x = parserFS_to_parserS_derivation (derivation_append dh dc' n) x)))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(simp add: parserFS_to_parserS_derivation_def)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 dh n x dc' xa xb e c)(*strict*)
   apply(simp add: derivation_append_def)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(subgoal_tac "x=n")
   apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 dh n dc' xa xb)(*strict*)
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh n dc' xa xb)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh n dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(rule parserFS.maximum_of_domainUnique)
    apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
    apply(rule parserFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(force)
  done

lemma parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_unfixed_scheduler_extendable1: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>d2. parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (parserFS_to_parserS_derivation d2) n \<longrightarrow> (\<forall>m\<le>n. parserS_get_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation d2) m \<sqsupseteq> [parser_bottom G1] \<longrightarrow> parserFS_get_unfixed_scheduler_DB G1 d2 m \<sqsupseteq> [parser_bottom G1]))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply(subgoal_tac "parserS_get_fixed_scheduler_DB G1 (parserFS_to_parserS_derivation d2) m = parserFS_get_fixed_scheduler_DB G1 d2 m")
   apply(rename_tac G1 d2 n x m)(*strict*)
   prefer 2
   apply (metis parserFS.derivation_initial_is_derivation parserFS.maximum_of_domainSmaller parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB parserS_vs_parserFS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 n x m c)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d2 m = parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) m")
   apply(rename_tac G1 d2 n x m c)(*strict*)
   prefer 2
   apply (metis parserFS.derivation_initial_is_derivation parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
  apply(rename_tac G1 d2 n x m c)(*strict*)
  apply(subgoal_tac "n=x")
   apply(rename_tac G1 d2 n x m c)(*strict*)
   prefer 2
   apply (metis parserS_vs_parserFS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x m c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x m c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 m = Some (pair e c)")
   apply(rename_tac G1 d2 x m c)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x m c)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x m c)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x m c)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x m c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x m c e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. parserFS_to_parserS_derivation d2 m = Some (pair e c)")
   apply(rename_tac G1 d2 x m c e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
   apply(simp add: get_configuration_def get_configuration_def)
   apply(subgoal_tac "\<exists>c. parserFS_get_scheduler ca = c @ [parser_bottom G1] \<and> parser_bottom G1 \<notin> set c")
    apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
    apply(erule exE)+
    apply(rename_tac G1 d2 x m c e ca ea cb cc)(*strict*)
    apply(rule_tac
      x="drop (parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) m) cc"
      in exI)
    apply(clarsimp)
    apply(simp add: parserFS_get_scheduler_def)
    apply(simp add: parserS_get_scheduler_def)
    apply(subgoal_tac "e = ea \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack ca, parserS_conf_scheduler = cc @ [parser_bottom G1]\<rparr> = cb")
     apply(rename_tac G1 d2 x m c e ca ea cb cc)(*strict*)
     prefer 2
     apply(simp add: parserFS_to_parserS_derivation_def)
    apply(rename_tac G1 d2 x m c e ca ea cb cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 x m c ca ea cc)(*strict*)
    apply(case_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) m - length cc")
     apply(rename_tac G1 d2 x m c ca ea cc)(*strict*)
     apply(clarsimp)
     apply(rename_tac G1 d2 x m ca ea cc)(*strict*)
     apply (metis append_eq_append_conv_if insert_Nil parserFS_get_unfixed_scheduler_def parserFS_get_scheduler_def take_all_length)
    apply(rename_tac G1 d2 x m c ca ea cc nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
   apply(simp add: parserFS_get_scheduler_def)
   apply(subgoal_tac "e = ea \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack ca, parserS_conf_scheduler = parserFS_conf_fixed ca @ parserFS_conf_scheduler ca\<rparr> = cb")
    apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
    prefer 2
    apply(simp add: parserFS_to_parserS_derivation_def)
   apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 x m c ca ea)(*strict*)
   apply(simp add: parserS_get_scheduler_def)
   apply(subgoal_tac "ca \<in> parserFS_configurations G1")
    apply(rename_tac G1 d2 x m c ca ea)(*strict*)
    apply(simp add: parserFS_configurations_def parserFS_get_scheduler_def)
    apply(clarsimp)
    apply(rename_tac G1 d2 x m c ea f l r)(*strict*)
    prefer 2
    apply(rename_tac G1 d2 x m c ca ea)(*strict*)
    apply(rule_tac
      d="d2"
      in parserFS.belongs_configurations)
     apply(rename_tac G1 d2 x m c ca ea)(*strict*)
     apply(rule parserFS.derivation_initial_belongs)
      apply(rename_tac G1 d2 x m c ca ea)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x m c ca ea)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x m c ca ea)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x m c ea f l r)(*strict*)
   prefer 2
   apply(rename_tac G1 d2 x m c e ca)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x m c ea f l r)(*strict*)
  apply(simp add: dom_abbreviation)
  apply(clarsimp)
  done

lemma parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_unfixed_scheduler_extendable2: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>d2. parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (parserFS_to_parserS_derivation d2) n \<longrightarrow> (\<forall>m\<le>n. parserFS_get_unfixed_scheduler_DB G1 d2 m \<sqsupseteq> [parser_bottom G1] \<longrightarrow> parserS_get_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation d2) m \<sqsupseteq> [parser_bottom G1]))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply(subgoal_tac "parserS_get_fixed_scheduler_DB G1 (parserFS_to_parserS_derivation d2) m = parserFS_get_fixed_scheduler_DB G1 d2 m")
   apply(rename_tac G1 d2 n x m)(*strict*)
   prefer 2
   apply (metis parserFS.derivation_initial_is_derivation parserFS.maximum_of_domainSmaller parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB parserS_vs_parserFS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
  apply(simp add: parserFS_get_fixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
  apply(simp add: suffix_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 n x m c)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d2 m = parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) m")
   apply(rename_tac G1 d2 n x m c)(*strict*)
   prefer 2
   apply (metis parserFS.derivation_initial_is_derivation parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
  apply(rename_tac G1 d2 n x m c)(*strict*)
  apply(subgoal_tac "n=x")
   apply(rename_tac G1 d2 n x m c)(*strict*)
   prefer 2
   apply (metis parserS_vs_parserFS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x m c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x m c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 m = Some (pair e c)")
   apply(rename_tac G1 d2 x m c)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x m c)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x m c)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x m c)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x m c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x m c e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. parserFS_to_parserS_derivation d2 m = Some (pair e c)")
   apply(rename_tac G1 d2 x m c e ca)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
   apply(simp add: get_configuration_def get_configuration_def)
   apply(subgoal_tac "\<exists>c. parserFS_get_scheduler ca = c @ [parser_bottom G1] \<and> parser_bottom G1 \<notin> set c")
    apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
    apply(erule exE)+
    apply(rename_tac G1 d2 x m c e ca ea cb cc)(*strict*)
    apply(rule_tac
      x="drop (parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) m) cc"
      in exI)
    apply(clarsimp)
    apply(simp add: parserFS_get_scheduler_def)
    apply(simp add: parserS_get_scheduler_def)
    apply(subgoal_tac "e = ea \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack ca, parserS_conf_scheduler = cc @ [parser_bottom G1]\<rparr> = cb")
     apply(rename_tac G1 d2 x m c e ca ea cb cc)(*strict*)
     prefer 2
     apply(simp add: parserFS_to_parserS_derivation_def)
     apply(clarsimp)
    apply(rename_tac G1 d2 x m c e ca ea cb cc)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 x m c ca ea)(*strict*)
    apply(case_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) m - (length (parserFS_conf_fixed ca) + length c)")
     apply(rename_tac G1 d2 x m c ca ea)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x m c ca ea nat)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
   apply(subgoal_tac "ca \<in> parserFS_configurations G1")
    apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
    apply(simp add: parserFS_configurations_def parserFS_get_scheduler_def)
    apply(clarsimp)
    apply(rename_tac G1 d2 x m c e ea cb l)(*strict*)
    prefer 2
    apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
    apply(rule_tac
      d="d2"
      in parserFS.belongs_configurations)
     apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
     apply(rule parserFS.derivation_initial_belongs)
      apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x m c e ca ea cb)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x m c e ea cb l)(*strict*)
   prefer 2
   apply(rename_tac G1 d2 x m c e ca)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x m c e ea cb l)(*strict*)
  apply(simp add: dom_abbreviation)
  done

lemma parserS_vs_parserFS_inst_AX_accept_id1: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> parserS_marking_condition G1 (parserFS_to_parserS_derivation d2) \<longrightarrow> parserFS_marking_condition G1 d2)"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
   apply(case_tac "d2 i")
    apply(rename_tac G1 d2 x c i e ca)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i e ca a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac G1 d2 x c i e ca a option b)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb)(*strict*)
  apply(simp add: parserFS_marking_condition_def)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c i e ca ea cb)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
    apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(rule_tac
      x="ea"
      in exI)
   apply(rule_tac
      x="cb"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
    apply(simp add: parserFS_to_parserS_derivation_def)
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_marking_configurations_def parserS_marking_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(rule_tac
      x="f"
      in bexI)
     apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
     apply(rule_tac
      x="w"
      in exI)
     apply(simp add: parserFS_to_parserS_derivation_def)
     apply(force)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(simp add: parserFS_to_parserS_derivation_def)
    apply(clarsimp)
   apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
   apply(rule parserFS.belongs_configurations)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(rule parserFS.derivation_initial_belongs)
     apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca ea cb)(*strict*)
  apply (metis parserFS.derivation_initial_is_derivation parserFS.some_position_has_details_at_0)
  done

lemma parserS_vs_parserFS_inst_AX_accept_id2: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> parserFS_marking_condition G1 d2 \<longrightarrow> parserS_marking_condition G1 (parserFS_to_parserS_derivation d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(simp add: parserFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(rule conjI)
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   apply(subgoal_tac "\<exists>c. parserFS_to_parserS_derivation d2 0 = Some (pair None c)")
    apply(rename_tac G1 d2 x c i e ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 x c i e ca cb)(*strict*)
    apply(rule_tac
      d="parserFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
     apply(rename_tac G1 d2 x c i e ca cb)(*strict*)
     apply(rule parserS.derivation_initial_belongs)
      apply(rename_tac G1 d2 x c i e ca cb)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x c i e ca cb)(*strict*)
     apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac G1 d2 x c i e ca cb)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   apply(rule_tac
      M="G1"
      in parserS.some_position_has_details_at_0)
   apply(rule_tac parserS.derivation_initial_is_derivation)
   apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(subgoal_tac "\<exists>e c. parserFS_to_parserS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb)(*strict*)
  apply(simp add: parserFS_marking_configurations_def parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
   apply(rule_tac
      x="f"
      in bexI)
    apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
    apply(rule_tac
      x="w"
      in exI)
    apply(simp add: parserFS_to_parserS_derivation_def)
    apply(clarsimp)
   apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
  apply(rule_tac
      d="parserFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
   apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
   apply(rule parserS.derivation_initial_belongs)
    apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
   apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
  apply(rename_tac G1 d2 x c i e ca ea cb f w)(*strict*)
  apply(force)
  done

lemma parserFS_to_parserS_derivation_reflects_string_state_delta: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> parserS_string_state ci' = w @ parserS_string_state cj'
  \<Longrightarrow> (parserFS_to_parserS_derivation d) i = Some (pair ei ci')
  \<Longrightarrow> (parserFS_to_parserS_derivation d) j = Some (pair ej cj')
  \<Longrightarrow> parserFS_string_state ci = w @ parserFS_string_state cj"
  apply(induct "j-i" arbitrary: j ej cj cj' w)
   apply(rename_tac j ej cj cj' w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x j ej cj cj' w)(*strict*)
  apply(clarsimp)
  apply(case_tac j)
   apply(rename_tac x j ej cj cj' w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x j ej cj cj' w nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x ej cj cj' w nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac x ej cj cj' w nat)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x ej cj cj' w nat)(*strict*)
    apply(force)
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   apply(force)
  apply(rename_tac x ej cj cj' w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>e c. d nat = Some (pair e c)")
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserFS.pre_some_position_is_some_position)
     apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>e c. (parserFS_to_parserS_derivation d) nat = Some (pair e c)")
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
  apply(erule_tac
      x="e"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="c"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserFS_string_state c1 = w @ parserFS_string_state cj")
   apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc 0"
      in parserFS.derivation_monotonically_dec)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(force)
   apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserFS_string_state ci = w @ parserFS_string_state c1")
   apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
   prefer 2
   apply(rule_tac
      j="nat-i"
      in parserFS.derivation_monotonically_dec)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
      apply(rule parserFS.derivation_initial_belongs)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(force)
   apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state cj'")
   apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
   prefer 2
   apply(rule_tac
      d="parserFS_to_parserS_derivation d"
      and j="Suc 0"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
      apply(rule parserS.derivation_initial_belongs)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
      apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
    apply(force)
   apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state ci' = w @ parserS_string_state c")
   apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
   prefer 2
   apply(rule_tac
      d="parserFS_to_parserS_derivation d"
      and j="nat-i"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
      apply(rule parserS.derivation_initial_belongs)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
      apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
    apply(force)
   apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
  apply(erule_tac
      x="wd"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. parserFS_to_parserS_derivation d nat = Some (pair e1 c1) \<and> parserFS_to_parserS_derivation d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
   apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
    apply(force)
   apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
  apply(clarsimp)
  apply(simp add: parserS_string_state_def parserFS_string_state_def parserS_step_relation_def parserFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wd xa xb xc v)(*strict*)
  apply(erule disjE)
   apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wd xa xb xc v)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wd xa xb xc v)(*strict*)
  apply(clarsimp)
  done

lemma parserFS_to_parserS_derivation_preserves_string_state_delta: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> parserFS_string_state ci = w @ parserFS_string_state cj
  \<Longrightarrow> (parserFS_to_parserS_derivation d) i = Some (pair ei ci')
  \<Longrightarrow> (parserFS_to_parserS_derivation d) j = Some (pair ej cj')
  \<Longrightarrow> parserS_string_state ci' = w @ parserS_string_state cj'"
  apply(induct "j-i" arbitrary: j ej cj cj' w)
   apply(rename_tac j ej cj cj' w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x j ej cj cj' w)(*strict*)
  apply(clarsimp)
  apply(case_tac j)
   apply(rename_tac x j ej cj cj' w)(*strict*)
   apply(force)
  apply(rename_tac x j ej cj cj' w nat)(*strict*)
  apply(erule_tac
      x="nat"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac x ej cj cj' w nat)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserFS_step_relation G c1 e2 c2")
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserFS.step_detail_before_some_position)
     apply(rename_tac x ej cj cj' w nat)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac x ej cj cj' w nat)(*strict*)
    apply(force)
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   apply(force)
  apply(rename_tac x ej cj cj' w nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "\<exists>e c. d nat = Some (pair e c)")
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(subgoal_tac "\<exists>e c. (parserFS_to_parserS_derivation d) nat = Some (pair e c)")
    apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(erule_tac
      x="e"
      in meta_allE)
    apply(clarsimp)
    apply(erule_tac
      x="c1"
      in meta_allE)
    apply(clarsimp)
    apply(erule_tac
      x="c"
      in meta_allE)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. parserFS_string_state c1 = w @ parserFS_string_state cj")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     prefer 2
     apply(rule_tac
      j="Suc 0"
      in parserFS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(rule parserFS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
       apply(rule parserFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(subgoal_tac "\<exists>w. parserFS_string_state ci = w @ parserFS_string_state c1")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     prefer 2
     apply(rule_tac
      j="nat-i"
      in parserFS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(rule parserFS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
       apply(rule parserFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(erule_tac
      x="wb"
      in meta_allE)
    apply(clarsimp)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(simp add: parserFS_to_parserS_derivation_def)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. parserFS_to_parserS_derivation d nat = Some (pair e1 c1) \<and> parserFS_to_parserS_derivation d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
       apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(clarsimp)
    apply(simp add: parserS_string_state_def parserFS_string_state_def parserS_step_relation_def parserFS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb xa xb xc v)(*strict*)
    apply(erule disjE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb xa xb xc v)(*strict*)
     apply(clarsimp)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb xa xb xc v)(*strict*)
    apply(clarsimp)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(force)
  done

lemma parserFS_parserS_schedUF_db_decreases: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> \<exists>w. parserS_get_unfixed_scheduler_DB G (parserFS_to_parserS_derivation d) i = w @ (parserS_get_unfixed_scheduler_DB G (parserFS_to_parserS_derivation d) j)"
  apply(subgoal_tac "\<exists>e c. parserFS_to_parserS_derivation d i = Some (pair e c)")
   apply(subgoal_tac "\<exists>e c. parserFS_to_parserS_derivation d j = Some (pair e c)")
    apply(clarsimp)
    apply(rename_tac e ea c ca)(*strict*)
    apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G (parserFS_to_parserS_derivation d) i"
      and s="drop (parser_fixed_input_length_recN d i) (parserS_conf_scheduler c)"
      in ssubst)
     apply(rename_tac e ea c ca)(*strict*)
     apply(simp add: parserS_get_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
     apply(rule_tac
      t="parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) i"
      and s="parser_fixed_input_length_recN d i"
      in subst)
      apply(rename_tac e ea c ca)(*strict*)
      apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
     apply(rename_tac e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca)(*strict*)
    apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G (parserFS_to_parserS_derivation d) j"
      and s="drop (parser_fixed_input_length_recN d j) (parserS_conf_scheduler ca)"
      in ssubst)
     apply(rename_tac e ea c ca)(*strict*)
     apply(simp add: parserS_get_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
     apply(rule_tac
      t="parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) j"
      and s="parser_fixed_input_length_recN d j"
      in subst)
      apply(rename_tac e ea c ca)(*strict*)
      apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
     apply(rename_tac e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c) - (parser_fixed_input_length_recN d i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN d (i+(j-i)))")
     apply(rename_tac e ea c ca)(*strict*)
     prefer 2
     apply(rule_tac
      t="parser_fixed_input_length_recN d (i + (j - i))"
      and s="parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) (i + (j - i))"
      in ssubst)
      apply(rename_tac e ea c ca)(*strict*)
      apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
     apply(rename_tac e ea c ca)(*strict*)
     apply(rule_tac
      t="parser_fixed_input_length_recN d i"
      and s="parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) i"
      in ssubst)
      apply(rename_tac e ea c ca)(*strict*)
      apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
     apply(rename_tac e ea c ca)(*strict*)
     apply(rule_tac
      c="c"
      and c'="ca"
      in PARSER_UnseenPartStrictlyDecreases)
         apply(rename_tac e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac e ea c ca)(*strict*)
        apply(rule parserS.derivation_initial_belongs)
         apply(rename_tac e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac e ea c ca)(*strict*)
        apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
       apply(rename_tac e ea c ca)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ parserS_string_state ca")
     apply(rename_tac e ea c ca)(*strict*)
     prefer 2
     apply(rule_tac
      j="j-i"
      and d="parserFS_to_parserS_derivation d"
      in parserS.derivation_monotonically_dec)
          apply(rename_tac e ea c ca)(*strict*)
          apply(force)
         apply(rename_tac e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac e ea c ca)(*strict*)
        apply(rule parserS.derivation_initial_belongs)
         apply(rename_tac e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac e ea c ca)(*strict*)
        apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
       apply(rename_tac e ea c ca)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca)(*strict*)
    apply(simp add: parserS_string_state_def)
    apply(clarsimp)
    apply(rename_tac e ea c ca w)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN d j \<le> length (parserS_conf_scheduler ca)")
     apply(rename_tac e ea c ca w)(*strict*)
     apply(subgoal_tac "parser_fixed_input_length_recN d i \<le> length (parserS_conf_scheduler c)")
      apply(rename_tac e ea c ca w)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "parser_fixed_input_length_recN d i - length w \<le> parser_fixed_input_length_recN d j")
       apply(rename_tac e ea c ca w)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(rule_tac
      x="(drop (parser_fixed_input_length_recN d i) w) @ (take (parser_fixed_input_length_recN d j - (parser_fixed_input_length_recN d i - length w)) (drop (parser_fixed_input_length_recN d i - length w) (parserS_conf_scheduler ca)))"
      in exI)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(clarsimp)
      apply (metis append_take_drop_id_hlp drop_distrib_append drop_take take_all_length)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(rule_tac
      t="parser_fixed_input_length_recN d i"
      and s="parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) i"
      in ssubst)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca w)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac e ea c ca w)(*strict*)
        apply(force)
       apply(rename_tac e ea c ca w)(*strict*)
       apply(rule parserS.derivation_initial_belongs)
        apply(rename_tac e ea c ca w)(*strict*)
        apply(force)
       apply(rename_tac e ea c ca w)(*strict*)
       apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(rule parserS.derivation_initial_is_derivation)
      apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca w)(*strict*)
    apply(rule_tac
      t="parser_fixed_input_length_recN d j"
      and s="parser_fixed_input_length_recN (parserFS_to_parserS_derivation d) j"
      in ssubst)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(force)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
    apply(rename_tac e ea c ca w)(*strict*)
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac e ea c ca w)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(rule parserS.derivation_initial_belongs)
       apply(rename_tac e ea c ca w)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca w)(*strict*)
      apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply (metis parserFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac e ea c ca w)(*strict*)
    apply(force)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(simp add: parserFS_to_parserS_derivation_def)
  done

lemma parser_S_FS_replace_unfixed_scheduler_DB_preserves_parser_fixed_input_length_recN: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> xa \<le> n
  \<Longrightarrow> parserS.derivation_initial G dh
  \<Longrightarrow> parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G dh sUF n) xa = parser_fixed_input_length_recN dh xa"
  apply(induct xa)
   apply(clarsimp)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. dh (Suc xa)= Some (pair e c)")
   apply(rename_tac xa)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_before_max_dom)
     apply(rename_tac xa)(*strict*)
     apply(simp add: parserS.derivation_initial_def)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(force)
   apply(rename_tac xa)(*strict*)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e c)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh xa = Some (pair e1 c1) \<and> dh (Suc xa) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
   apply(rename_tac xa e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc xa"
      in parserS.step_detail_before_some_position)
     apply(rename_tac xa e c)(*strict*)
     apply(simp add: parserS.derivation_initial_def)
    apply(rename_tac xa e c)(*strict*)
    apply(force)
   apply(rename_tac xa e c)(*strict*)
   apply(force)
  apply(rename_tac xa e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa c e1 e2 c1)(*strict*)
  apply(case_tac "parserS.replace_unfixed_scheduler_DB G dh sUF n (Suc xa)")
   apply(rename_tac xa c e1 e2 c1)(*strict*)
   apply(clarsimp)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
  apply(rename_tac xa c e1 e2 c1 a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac xa c e1 e2 c1 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa c e1 e2 c1 option b)(*strict*)
  apply(case_tac option)
   apply(rename_tac xa c e1 e2 c1 option b)(*strict*)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
  apply(rename_tac xa c e1 e2 c1 option b a)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa c e1 e2 c1 b a)(*strict*)
  apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
  done

lemma parserFS_double_funct_mod_vs_mod: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> xa \<le> n
  \<Longrightarrow> parserFS.derivation_initial G dh
  \<Longrightarrow> parserS_to_parserFS_derivation G (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) xa = parserFS.replace_unfixed_scheduler_DB G dh sUF n xa"
  apply(simp only: parserS_to_parserFS_derivation_def)
  apply(simp add: parserS.replace_unfixed_scheduler_DB_def)
  apply(simp add: parserFS.replace_unfixed_scheduler_DB_def)
  apply(simp add: parserS.map_unfixed_scheduler_DB_def)
  apply(simp add: parserFS.map_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e c)(*strict*)
  apply(subgoal_tac "\<exists>c. parserFS_to_parserS_derivation dh xa = Some (pair e c)")
   apply(rename_tac e c)(*strict*)
   prefer 2
   apply(rule parserFS_to_parserS_derivation_preserves_step_labels)
     apply(rename_tac e c)(*strict*)
     apply(force)
    apply(rename_tac e c)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
   apply(rename_tac e c)(*strict*)
   apply(force)
  apply(rename_tac e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac e c ca)(*strict*)
  apply(simp add: parserFS_set_unfixed_scheduler_DB_def get_configuration_def)
  apply(case_tac c)
  apply(rename_tac e c ca parserFS_conf_fixed parserFS_conf_stack parserFS_conf_scheduler)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ca parserFS_conf_fixed parserFS_conf_stack parserFS_conf_scheduler)(*strict*)
  apply(rename_tac f h l r)
  apply(rename_tac e f h l r)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G (parserFS_to_parserS_derivation dh) sUF n) xa"
      and s="parser_fixed_input_length_recN dh xa"
      in ssubst)
   apply(rename_tac e f h l r)(*strict*)
   defer
   apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) xa = parser_fixed_input_length_recN dh xa")
    apply(rename_tac e f h l r)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
     apply(rename_tac e f h l r)(*strict*)
     apply(force)
    apply(rename_tac e f h l r)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
   apply(rename_tac e f h l r)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) n = parser_fixed_input_length_recN dh n")
    apply(rename_tac e f h l r)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
     apply(rename_tac e f h l r)(*strict*)
     apply(force)
    apply(rename_tac e f h l r)(*strict*)
    apply(simp add: parserFS.derivation_initial_def)
   apply(rename_tac e f h l r)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN dh xa = length h")
    apply(rename_tac e f h l r)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
     apply(rename_tac e f h l r)(*strict*)
     prefer 2
     apply(rule parserFS.some_position_has_details_before_max_dom)
       apply(rename_tac e f h l r)(*strict*)
       apply(simp add: parserFS.derivation_initial_def)
       apply(force)
      apply(rename_tac e f h l r)(*strict*)
      apply(force)
     apply(rename_tac e f h l r)(*strict*)
     apply(force)
    apply(rename_tac e f h l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac e f h l r ea c)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN dh n = length (parserFS_conf_fixed c)")
     apply(rename_tac e f h l r ea c)(*strict*)
     apply(simp add: parserFS_set_unfixed_scheduler_def)
     apply(simp add: parserS_get_unfixed_scheduler_DB_def)
     apply(simp add: parserS_get_scheduler_def)
     apply(subgoal_tac "\<exists>e c. parserFS_to_parserS_derivation dh n = Some (pair e c)")
      apply(rename_tac e f h l r ea c)(*strict*)
      apply(clarsimp)
      apply(rename_tac e f h l r ea c eb ca)(*strict*)
      apply(simp add: get_configuration_def)
      apply(subgoal_tac "\<lparr>parserS_conf_stack = l, parserS_conf_scheduler = h @ r\<rparr> = f")
       apply(rename_tac e f h l r ea c eb ca)(*strict*)
       prefer 2
       apply(simp add: parserFS_to_parserS_derivation_def)
      apply(rename_tac e f h l r ea c eb ca)(*strict*)
      apply(subgoal_tac "ea = eb \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack c, parserS_conf_scheduler = parserFS_conf_fixed c @ parserFS_conf_scheduler c\<rparr> = ca")
       apply(rename_tac e f h l r ea c eb ca)(*strict*)
       prefer 2
       apply(simp add: parserFS_to_parserS_derivation_def)
      apply(rename_tac e f h l r ea c eb ca)(*strict*)
      apply(clarsimp)
      apply(rename_tac e h l r c eb)(*strict*)
      apply(subgoal_tac "\<exists>w. parserFS_conf_scheduler \<lparr>parserFS_conf_fixed = h, parserFS_conf_stack = l, parserFS_conf_scheduler = r\<rparr> = w @ parserFS_conf_scheduler c")
       apply(rename_tac e h l r c eb)(*strict*)
       prefer 2
       apply(rule_tac
      j="n"
      in parserFS_input_decreases)
            apply(rename_tac e h l r c eb)(*strict*)
            apply(force)
           apply(rename_tac e h l r c eb)(*strict*)
           apply(rule parserFS.derivation_initial_is_derivation)
           apply(force)
          apply(rename_tac e h l r c eb)(*strict*)
          apply(rule parserFS.derivation_initial_belongs)
           apply(rename_tac e h l r c eb)(*strict*)
           apply(force)
          apply(rename_tac e h l r c eb)(*strict*)
          apply(force)
         apply(rename_tac e h l r c eb)(*strict*)
         apply(force)
        apply(rename_tac e h l r c eb)(*strict*)
        apply(force)
       apply(rename_tac e h l r c eb)(*strict*)
       apply(force)
      apply(rename_tac e h l r c eb)(*strict*)
      apply(clarsimp)
      apply(rename_tac e h l c eb w)(*strict*)
      apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
      apply(simp add: get_configuration_def)
      apply(rule_tac
      t="right_quotient_word (w @ parserFS_conf_scheduler c) (parserFS_conf_scheduler c)"
      and s="Some w"
      in ssubst)
       apply(rename_tac e h l c eb w)(*strict*)
       apply (metis right_quotient_word_removes_right_addition_hlp)
      apply(rename_tac e h l c eb w)(*strict*)
      apply(clarsimp)
      apply(simp add: get_configuration_def parserFS_to_parserS_derivation_def parserS_set_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def parserS_get_scheduler_def)
     apply(rename_tac e f h l r ea c)(*strict*)
     apply(simp add: parserFS_to_parserS_derivation_def)
    apply(rename_tac e f h l r ea c)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) n = length (parserFS_conf_fixed (the(get_configuration(dh n))))")
     apply(rename_tac e f h l r ea c)(*strict*)
     apply(clarsimp)
     apply(simp add: get_configuration_def)
    apply(rename_tac e f h l r ea c)(*strict*)
    apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
      apply(rename_tac e f h l r ea c)(*strict*)
      apply(force)
     apply(rename_tac e f h l r ea c)(*strict*)
     apply(force)
    apply(rename_tac e f h l r ea c)(*strict*)
    apply(force)
   apply(rename_tac e f h l r)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) xa = length (parserFS_conf_fixed (the(get_configuration(dh xa))))")
    apply(rename_tac e f h l r)(*strict*)
    apply(clarsimp)
    apply(simp add: get_configuration_def)
   apply(rename_tac e f h l r)(*strict*)
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
     apply(rename_tac e f h l r)(*strict*)
     apply(force)
    apply(rename_tac e f h l r)(*strict*)
    apply(force)
   apply(rename_tac e f h l r)(*strict*)
   apply(force)
  apply(rename_tac e f h l r)(*strict*)
  apply (metis parserFS.derivation_initial_is_derivation parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN parserFS_to_parserS_derivation_preserves_derivation_initial parserFS_to_parserS_derivation_preserves_maximum_of_domain parser_S_FS_replace_unfixed_scheduler_DB_preserves_parser_fixed_input_length_recN)
  done

lemma parserFS_get_unfixed_scheduler_DB_on_modification: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> sUF \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserFS.derivation_initial G dh
  \<Longrightarrow> parserFS_get_unfixed_scheduler_DB G (parserFS.replace_unfixed_scheduler_DB G dh sUF n) n = sUF"
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
  apply(simp add: parserFS.replace_unfixed_scheduler_DB_def)
  apply(simp add: parserFS.map_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(simp add: get_configuration_def)
   apply(rule_tac
      t="right_quotient_word (parserFS_get_unfixed_scheduler_DB G dh n) (parserFS_get_unfixed_scheduler_DB G dh n)"
      and s="Some []"
      in ssubst)
    apply(rename_tac e c)(*strict*)
    apply (metis right_quotient_word_full)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(simp add: parserFS_set_unfixed_scheduler_DB_def)
   apply(simp add: get_configuration_def)
   apply(simp add: parserFS_set_unfixed_scheduler_def)
  apply(rule parserFS.some_position_has_details_before_max_dom)
    apply(simp add: parserFS.derivation_initial_def)
    apply(force)
   apply(force)
  apply(force)
  done

lemma parserFS_get_unfixed_scheduler_DB_with_derivation_take: "
  valid_parser G
  \<Longrightarrow> parserFS.derivation G d
  \<Longrightarrow> parserFS_get_unfixed_scheduler_DB G d n = parserFS_get_unfixed_scheduler_DB G (derivation_take d n) n"
  apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d n) n"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
   apply(rule parserFS_parser_fixed_input_length_recN_with_derivation_take)
    apply(force)
   apply(force)
  apply(simp add: derivation_take_def)
  done

lemma derivation_take_distributes_over_parserS_to_parserFS_derivation: "
  derivation_take (parserS_to_parserFS_derivation G d) n = parserS_to_parserFS_derivation G (derivation_take d n)"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def parserS_to_parserFS_derivation_def derivation_take_def)
  apply(case_tac "x\<le>n")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(case_tac "d x")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac x a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x option b)(*strict*)
   apply(fold derivation_take_def parserS_to_parserFS_derivation_def derivation_take_def)
   apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d n) x"
      and s="parser_fixed_input_length_recN d x"
      in ssubst)
    apply(rename_tac x option b)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x option b)(*strict*)
   apply(rule parser_fixed_input_length_recN_with_derivation_take)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma parserS_vs_parserFS_inst_hlp_bisimulation_compatible_with_replace_and_schedF: "
  valid_parser G1
  \<Longrightarrow> parserFS.derivation_initial G1 dh
  \<Longrightarrow> maximum_of_domain dh x
  \<Longrightarrow> maximum_of_domain (parserFS_to_parserS_derivation dh) n
  \<Longrightarrow> parserFS.derivation_initial G1 dc'
  \<Longrightarrow> parserFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n
  \<Longrightarrow> parserFS_get_unfixed_scheduler_DB G1 dh n \<sqsupseteq> [parser_bottom G1]
  \<Longrightarrow> sUF \<sqsupseteq> [parser_bottom G1]
  \<Longrightarrow> sUF \<in> parser_unfixed_schedulers G1
  \<Longrightarrow> maximum_of_domain dc' xb
  \<Longrightarrow> xa \<le> n
  \<Longrightarrow> parserFS_get_fixed_scheduler_DB G1 dh xa = parserFS_get_fixed_scheduler_DB G1 dc' xa \<and> parserFS.replace_unfixed_scheduler_DB G1 dh (parserFS_get_unfixed_scheduler_DB G1 dc' n) n xa = dc' xa"
  apply(subgoal_tac "x=n")
   prefer 2
   apply(rule parserFS.maximum_of_domainUnique)
     prefer 3
     apply(force)
    apply(simp add: parserFS.derivation_initial_def)
    apply(force)
   apply(simp add: parserFS_to_parserS_derivation_def)
   apply(simp add: maximum_of_domain_def maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac y ya yb)(*strict*)
   apply(case_tac "dh n")
    apply(rename_tac y ya yb)(*strict*)
    apply(clarsimp)
   apply(rename_tac y ya yb a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac y ya yb a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac y yb option b)(*strict*)
   apply(case_tac "dh (Suc n)")
    apply(rename_tac y yb option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac y yb option b a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac y yb option b a optiona ba)(*strict*)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>n'. maximum_of_domain dc' (n+n')")
   prefer 2
   apply(subgoal_tac "xb\<ge>n")
    apply(rule_tac
      x="xb-n"
      in exI)
    apply(force)
   apply(case_tac "n>xb")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(subgoal_tac "dc' n = None")
    prefer 2
    apply(rule parserFS.none_position_after_max_dom)
      apply(simp add: parserFS.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "parserFS_to_parserS_derivation dc' n = derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n n")
    prefer 2
    apply(force)
   apply(thin_tac "parserFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n")
   apply(simp add: parserFS_to_parserS_derivation_def derivation_append_def)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
    apply(clarsimp)
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac n')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac n')(*strict*)
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_uniform)
             apply(rename_tac n')(*strict*)
             prefer 9
             apply(force)+
  apply(rename_tac n')(*strict*)
  apply(simp add: parserFS.replace_unfixed_scheduler_DB_def parserFS.map_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   apply(rename_tac n')(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac n')(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n')(*strict*)
    apply(force)
   apply(rename_tac n')(*strict*)
   apply(force)
  apply(rename_tac n')(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac n')(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac n')(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n')(*strict*)
    apply(force)
   apply(rename_tac n')(*strict*)
   apply(force)
  apply(rename_tac n')(*strict*)
  apply(clarsimp)
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(subgoal_tac "dc' = parserS_to_parserFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n)")
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(thin_tac "parserFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n")
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parserS_to_parserFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n) xa = parserS_to_parserFS_derivation G1 ((parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) ) xa")
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parserFS_get_unfixed_scheduler_DB G1 (parserS_to_parserFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n)) n = sUF")
     apply(rename_tac n' e ea c ca)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="parserS_to_parserFS_derivation G1 (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) xa"
      and s=" (parserFS.replace_unfixed_scheduler_DB G1 dh sUF n) xa"
      in ssubst)
      apply(rename_tac n' e ea c ca)(*strict*)
      prefer 2
      apply(simp add: parserFS.replace_unfixed_scheduler_DB_def)
      apply(simp add: parserFS.map_unfixed_scheduler_DB_def)
     apply(rename_tac n' e ea c ca)(*strict*)
     apply(rule parserFS_double_funct_mod_vs_mod)
        apply(rename_tac n' e ea c ca)(*strict*)
        apply(force)+
    apply(rename_tac n' e ea c ca)(*strict*)
    prefer 2
    apply(simp add: parserS_to_parserFS_derivation_def derivation_append_def)
    apply(case_tac "parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n xa")
     apply(rename_tac n' e ea c ca)(*strict*)
     apply(clarsimp)
    apply(rename_tac n' e ea c ca a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac n' e ea c ca a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac n' e ea c ca option b)(*strict*)
    apply(fold derivation_append_def)
    apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n) xa"
      and s="parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) xa"
      in ssubst)
     apply(rename_tac n' e ea c ca option b)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac n' e ea c ca option b)(*strict*)
    apply(rule parser_fixed_input_length_recN_with_derivation_append)
     apply(rename_tac n' e ea c ca option b)(*strict*)
     apply(force)
    apply(rename_tac n' e ea c ca option b)(*strict*)
    apply(rule parserS_mod_preserves_derivation)
      apply(rename_tac n' e ea c ca option b)(*strict*)
      apply(force)+
    apply(rename_tac n' e ea c ca option b)(*strict*)
    apply (rule parserFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac n' e ea c ca option b)(*strict*)
     apply(force)+
   apply(rename_tac n' e ea c ca)(*strict*)
   prefer 2
   apply(rule_tac
      t="dc'"
      and s="parserS_to_parserFS_derivation G1 (parserFS_to_parserS_derivation dc')"
      in subst)
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(rule ext)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(rule parser_S_FS_relation_coincide_hlp)
      apply(rename_tac n' e ea c ca x)(*strict*)
      apply(force)+
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(rule_tac
      t="parserFS_get_unfixed_scheduler_DB G1 (parserS_to_parserFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n)) n"
      and s="parserFS_get_unfixed_scheduler_DB G1 (parserS_to_parserFS_derivation G1 ((parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) )) n"
      in ssubst)
   apply(rename_tac n' e ea c ca)(*strict*)
   defer
   apply(rule_tac
      t="parserS_to_parserFS_derivation G1 (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n)"
      and s="parserFS.replace_unfixed_scheduler_DB G1 dh sUF n"
      in ssubst)
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(rule ext)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(case_tac "x\<le>n")
     apply(rename_tac n' e ea c ca x)(*strict*)
     apply(rule parserFS_double_funct_mod_vs_mod)
        apply(rename_tac n' e ea c ca x)(*strict*)
        apply(force)+
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(subgoal_tac "dh x = None")
     apply(rename_tac n' e ea c ca x)(*strict*)
     apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def parserFS.replace_unfixed_scheduler_DB_def parserFS.map_unfixed_scheduler_DB_def parserS_to_parserFS_derivation_def parserFS_to_parserS_derivation_def)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(rule parserFS.none_position_after_max_dom)
      apply(rename_tac n' e ea c ca x)(*strict*)
      apply(simp add: parserFS.derivation_initial_def)
      apply(force)
     apply(rename_tac n' e ea c ca x)(*strict*)
     apply(force)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(force)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(rule parserFS_get_unfixed_scheduler_DB_on_modification)
      apply(rename_tac n' e ea c ca)(*strict*)
      apply(force)+
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(rule_tac
      t="parserFS_get_unfixed_scheduler_DB G1 (parserS_to_parserFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n)) n"
      and s="parserFS_get_unfixed_scheduler_DB G1 (derivation_take (parserS_to_parserFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n)) n) n"
      in ssubst)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(rule parserFS_get_unfixed_scheduler_DB_with_derivation_take)
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(force)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(rule_tac
      t="derivation_take (parserS_to_parserFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n)) n"
      and s=" (parserS_to_parserFS_derivation G1 (derivation_take (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n) n))"
      in ssubst)
   apply(rename_tac n' e ea c ca)(*strict*)
   prefer 2
   apply(rule_tac
      t="derivation_take (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n) n"
      and s="parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n"
      in ssubst)
    apply(rename_tac n' e ea c ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(rule_tac
      t="derivation_take (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n) n"
      and s="derivation_take ((parserS.replace_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) ) n"
      in ssubst)
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(rule derivation_take_derivation_append_ignore)
    apply(force)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(rule ext)
   apply(rename_tac n' e ea c ca x)(*strict*)
   apply(case_tac "x\<le>n")
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac n' e ea c ca x)(*strict*)
   apply(simp add: derivation_take_def)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def parserFS_to_parserS_derivation_def)
   apply(subgoal_tac "dh x=None")
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(clarsimp)
   apply(rename_tac n' e ea c ca x)(*strict*)
   apply(rule parserFS.none_position_after_max_dom)
     apply(rename_tac n' e ea c ca x)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(force)
   apply(rename_tac n' e ea c ca x)(*strict*)
   apply(force)
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(rule derivation_take_distributes_over_parserS_to_parserFS_derivation)
  done

lemma parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_replace_and_schedF1: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>dh. parserFS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain (parserFS_to_parserS_derivation dh) n \<longrightarrow> parserFS_get_unfixed_scheduler_DB G1 dh n \<sqsupseteq> [parser_bottom G1] \<longrightarrow> (\<forall>sUF. sUF \<sqsupseteq> [parser_bottom G1] \<longrightarrow> sUF \<in> parser_unfixed_schedulers G1 \<longrightarrow> (\<forall>dc dc'. parserFS.derivation_initial G1 dc' \<and> Ex (maximum_of_domain dc') \<and> parserFS_to_parserS_derivation dc' = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) sUF n) dc n \<longrightarrow> (\<forall>x\<le>n. parserFS_get_fixed_scheduler_DB G1 dh x = parserFS_get_fixed_scheduler_DB G1 dc' x \<and> ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh (parserFS_get_unfixed_scheduler_DB G1 dc' n) n x = dc' x))))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x sUF dc dc' xa xb)(*strict*)
  apply(rule parserS_vs_parserFS_inst_hlp_bisimulation_compatible_with_replace_and_schedF)
            apply(rename_tac G1 dh n x sUF dc dc' xa xb)(*strict*)
            apply(force)+
  done

lemma parser_parserFS_parserHFS_parser_fixed_input_length_recN_equal_by_labels: "
  parserS.derivation G d1
  \<Longrightarrow> parserFS.derivation G d2
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

lemma parserFS_parserFS_parserHFS_parser_fixed_input_length_recN_equal_by_labels: "
  parserFS.derivation G d1
  \<Longrightarrow> parserFS.derivation G d2
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

lemma parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_replace_and_schedF2: "
  \<forall>G1. valid_parser G1 \<longrightarrow>
         (\<forall>dh. ATS.derivation_initial parserFS_initial_configurations
                parserFS_step_relation G1 dh \<and>
               Ex (maximum_of_domain dh) \<longrightarrow>
               (\<forall>n. maximum_of_domain dh n \<longrightarrow>
                    parserS_get_unfixed_scheduler_DB G1
                     (parserFS_to_parserS_derivation dh) n \<sqsupseteq>
                    [parser_bottom G1] \<longrightarrow>
                    (\<forall>sUF'.
                        sUF' \<sqsupseteq> [parser_bottom G1] \<longrightarrow>
                        sUF' \<in> parser_unfixed_schedulers G1 \<longrightarrow>
                        (\<forall>dc. (\<exists>dc'. ATS.derivation_initial
                                      parserFS_initial_configurations
                                      parserFS_step_relation G1
                                      (derivation_append
 (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
   parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh
   sUF' n)
 dc' n) \<and>
                                     Ex (maximum_of_domain
   (derivation_append
     (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
       parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1
       dh sUF' n)
     dc' n)) \<and>
                                     parserFS_to_parserS_derivation
                                      (derivation_append
 (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
   parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh
   sUF' n)
 dc' n) =
                                     dc) \<longrightarrow>
                              (\<forall>x\<le>n. parserS_get_fixed_scheduler_DB G1
(parserFS_to_parserS_derivation dh) x =
                                      parserS_get_fixed_scheduler_DB G1 dc
x \<and>
                                      ATS_SchedUF_DB.replace_unfixed_scheduler_DB
right_quotient_word (@) parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB G1
(parserFS_to_parserS_derivation dh) (parserS_get_unfixed_scheduler_DB G1 dc n) n
x =
                                      dc x)))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
  apply(subgoal_tac "n=x")
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   prefer 2
   apply(rule parserFS.maximum_of_domainUnique)
     apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh xa=Some (pair e c)")
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) xa = parser_fixed_input_length_recN (parserFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x)) xa")
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) xa = length(parserFS_conf_fixed(the(get_configuration(dh xa))))")
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(simp add: parserS_get_fixed_scheduler_DB_def parserS_get_scheduler_def parserS_get_unfixed_scheduler_DB_def)
     apply(simp add: parserFS_to_parserS_derivation_def derivation_append_def)
     apply(simp add: parserFS.replace_unfixed_scheduler_DB_def parserFS.map_unfixed_scheduler_DB_def parserFS_to_parserS_derivation_def)
     apply(clarsimp)
     apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
     apply(simp add: get_configuration_def)
     apply(simp add: parserFS_set_unfixed_scheduler_DB_def)
     apply(simp add: get_configuration_def)
     apply(simp add: parserFS_set_unfixed_scheduler_def)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply (metis option.simps(2) parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(rule sym)
   apply(rule_tac
      t="parser_fixed_input_length_recN (parserFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x)) xa"
      and s="parser_fixed_input_length_recN ((derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x))xa "
      in ssubst)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply (metis parserFS.derivation_initial_is_derivation parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(rule_tac
      t="parser_fixed_input_length_recN (parserFS_to_parserS_derivation dh) xa"
      and s="parser_fixed_input_length_recN dh xa"
      in ssubst)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply (metis parserFS.derivation_initial_is_derivation parserFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(rule_tac
      G="G1"
      in parserFS_parserFS_parserHFS_parser_fixed_input_length_recN_equal_by_labels)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply (metis parserFS.derivation_initial_is_derivation)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply (metis parserFS.derivation_initial_is_derivation)
   apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 dh x sUF' dc' xa xb i e c)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: parserFS.replace_unfixed_scheduler_DB_def)
   apply(simp add: parserFS.replace_unfixed_scheduler_DB_def parserFS.map_unfixed_scheduler_DB_def parserFS_to_parserS_derivation_def)
   apply(case_tac "dh i")
    apply(rename_tac G1 dh x sUF' dc' xa xb i e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 dh x sUF' dc' xa xb i e c a)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(case_tac a)
   apply(rename_tac G1 dh x sUF' dc' xa xb i e c a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh x=Some (pair e c)")
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x)) x"
      and s="parserFS_get_unfixed_scheduler_DB G1 ((derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x)) x"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(rule sym)
   apply(rule parserFS_to_parserS_derivation_preserves_get_unfixed_scheduler_DB)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: parserFS.replace_unfixed_scheduler_DB_def parserFS.map_unfixed_scheduler_DB_def parserFS_to_parserS_derivation_def)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule_tac
      t="parserFS_get_unfixed_scheduler_DB G1 (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x) x"
      and s="parserFS_get_unfixed_scheduler_DB G1 ((ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) ) x"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(simp add: parserFS_get_unfixed_scheduler_DB_def derivation_append_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule_tac
      t="parserFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x) xa"
      and s="parserFS_to_parserS_derivation ((ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) ) xa"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(rule_tac
      t="parserFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x) xa"
      and s="parserFS_to_parserS_derivation ((ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) ) xa"
      in ssubst)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(simp add: parserFS_to_parserS_derivation_def derivation_append_def)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def derivation_append_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
  apply(case_tac "parserFS_to_parserS_derivation dh xa")
   apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca a)(*strict*)
  apply(case_tac a)
  apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca option b)(*strict*)
  apply(subgoal_tac "e = option \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack c, parserS_conf_scheduler = parserFS_conf_fixed c @ parserFS_conf_scheduler c\<rparr> = b")
   apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca option b)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
  apply(rule_tac
      t="parserFS_get_unfixed_scheduler_DB G1 (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB G1 dh sUF' x) x"
      and s="sUF'"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
   apply(simp add: parserFS_get_unfixed_scheduler_DB_def)
   apply(simp (no_asm) add: parserFS.replace_unfixed_scheduler_DB_def parserFS.map_unfixed_scheduler_DB_def parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def parserFS_set_unfixed_scheduler_DB_def get_configuration_def parserFS_set_unfixed_scheduler_def parserS_get_fixed_scheduler_DB_def parserS_get_scheduler_def parserS_get_unfixed_scheduler_DB_def)
   apply (metis right_quotient_word_full option.sel)
  apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
  apply(simp (no_asm) add: parserFS.replace_unfixed_scheduler_DB_def parserFS.map_unfixed_scheduler_DB_def parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
  apply(simp (no_asm) add: parserFS_to_parserS_derivation_def)
  apply(clarsimp)
  apply(simp add: parserS_set_unfixed_scheduler_DB_def get_configuration_def)
  apply(rule conjI)
   apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
   apply(simp add: parserFS_set_unfixed_scheduler_DB_def parserFS_set_unfixed_scheduler_def get_configuration_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
  apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) xa"
      and s="parserFS_get_unfixed_scheduler_DB G1 dh xa"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
   apply (metis not_None_eq parserFS_to_parserS_derivation_preserves_get_unfixed_scheduler_DB)
  apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
  apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G1 (parserFS_to_parserS_derivation dh) x"
      and s="parserFS_get_unfixed_scheduler_DB G1 dh x"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
   apply (metis not_None_eq parserFS_to_parserS_derivation_preserves_get_unfixed_scheduler_DB)
  apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
  apply(rule_tac
      t="parserFS_conf_fixed (parserFS_set_unfixed_scheduler_DB G1 dh xa (the (right_quotient_word (parserFS_get_unfixed_scheduler_DB G1 dh xa) (parserFS_get_unfixed_scheduler_DB G1 dh x)) @ sUF'))"
      and s="parserFS_conf_fixed(the(get_configuration(dh xa)))"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
   apply(simp add: parserFS_set_unfixed_scheduler_DB_def get_configuration_def parserFS_set_unfixed_scheduler_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(rule_tac
      t="parserFS_conf_scheduler (parserFS_set_unfixed_scheduler_DB G1 dh xa (the (right_quotient_word (parserFS_get_unfixed_scheduler_DB G1 dh xa) (parserFS_get_unfixed_scheduler_DB G1 dh x)) @ sUF'))"
      and s="the (right_quotient_word (parserFS_get_unfixed_scheduler_DB G1 dh xa) (parserFS_get_unfixed_scheduler_DB G1 dh x)) @ sUF'"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
   apply(simp add: parserFS_set_unfixed_scheduler_DB_def get_configuration_def parserFS_set_unfixed_scheduler_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb ea c ca option)(*strict*)
  apply (metis not_Some_eq parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB parserFS_inst_AX_state_based_vs_derivation_based_get_fixed_scheduler)
  done

lemma parserS_vs_parserFS_inst_AX_unAX_marked_effect_id1: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o1. o1 \<in> parserS_unmarked_effect G1 (parserFS_to_parserS_derivation d2) \<longrightarrow> o1 \<in> parserFS_unmarked_effect G1 d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o1 x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def parserFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i e v)(*strict*)
  apply(subgoal_tac "i\<le>x")
   apply(rename_tac G1 d2 x c c' i e v)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
   apply(case_tac "d2 i")
    apply(rename_tac G1 d2 x c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c c' i e v a)(*strict*)
   apply(clarsimp)
   apply(rule parserFS.allPreMaxDomSome_prime)
     apply(rename_tac G1 d2 x c c' i e v a)(*strict*)
     apply(rule parserFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 d2 x c c' i e v a)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c c' i e v a)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c c' i e v)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c c' i e v)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x c c' i e v)(*strict*)
     apply(simp add: parserFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x c c' i e v)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c c' i e v)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c c' i e v)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c c' i e v)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_at_0)
   apply(simp add: parserFS.derivation_initial_def)
   apply(force)
  apply(rename_tac G1 d2 x c c' i e v)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
  apply(subgoal_tac "ea = e \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack cb, parserS_conf_scheduler = parserFS_conf_fixed cb @ parserFS_conf_scheduler cb\<rparr> = c'")
   apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e v ca cb)(*strict*)
  apply(rule_tac
      x="cb"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 d2 x c i e v ca cb)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c i e v ca cb)(*strict*)
  apply(subgoal_tac "\<lparr>parserS_conf_stack = parserFS_conf_stack ca, parserS_conf_scheduler = parserFS_conf_fixed ca @ parserFS_conf_scheduler ca\<rparr> = c")
   apply(rename_tac G1 d2 x c i e v ca cb)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e v ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) i = length (parserFS_conf_fixed (the(get_configuration(d2 i))))")
   apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
   prefer 2
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
     apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "cb \<in> parserFS_configurations G1")
   apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
   prefer 2
   apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
  apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
  apply(subgoal_tac "v = butlast_if_match v (parser_bottom G1)")
   apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
   apply(case_tac "parserFS_conf_fixed cb")
    apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 x i e v ca cb a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. parserFS_conf_fixed cb = w' @ [x']")
    apply(rename_tac G1 d2 x i e v ca cb a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G1 d2 x i e v ca cb a list)(*strict*)
   apply(thin_tac "parserFS_conf_fixed cb = a # list")
   apply(clarsimp)
   apply(rename_tac G1 d2 x i e v ca cb w' x')(*strict*)
   apply(case_tac "parserFS_conf_scheduler cb")
    apply(rename_tac G1 d2 x i e v ca cb w' x')(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="parserFS_conf_fixed ca @ parserFS_conf_scheduler ca"
      and s="(v @ w') @ [x']"
      in ssubst)
     apply(rename_tac G1 d2 x i e v ca cb w' x')(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x i e v ca cb w' x')(*strict*)
    apply(subgoal_tac "x'=parser_bottom G1")
     apply(rename_tac G1 d2 x i e v ca cb w' x')(*strict*)
     apply (metis butlast_if_match_direct)
    apply(rename_tac G1 d2 x i e v ca cb w' x')(*strict*)
    apply(simp add: parserFS_configurations_def)
    apply(clarsimp)
    apply(rename_tac G1 d2 x i e v ca w' x' l)(*strict*)
    apply(simp add: dom_abbreviation)
   apply(rename_tac G1 d2 x i e v ca cb w' x' a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. parserFS_conf_scheduler cb = w' @ [x']")
    apply(rename_tac G1 d2 x i e v ca cb w' x' a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac G1 d2 x i e v ca cb w' x' a list)(*strict*)
   apply(thin_tac "parserFS_conf_scheduler cb = a # list")
   apply(clarsimp)
   apply(rename_tac G1 d2 x i e v ca cb w' x' w'a x'a)(*strict*)
   apply(subgoal_tac "x'\<noteq>parser_bottom G1")
    apply(rename_tac G1 d2 x i e v ca cb w' x' w'a x'a)(*strict*)
    apply (metis ConsApp Cons_eq_appendI Nat.add_0_right add_Suc_right append_assoc butlast_if_match_direct2 butlast_if_match_pull_out butlast_snoc_2 lengthDec2 list.simps(3) takePrecise)
   apply(rename_tac G1 d2 x i e v ca cb w' x' w'a x'a)(*strict*)
   apply(simp add: parserFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x i e v ca w' w'a x'a l)(*strict*)
   apply(simp add: dom_abbreviation)
  apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
  apply(subgoal_tac "parser_bottom G1 \<notin> set v")
   apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
   apply (metis butlast_if_match_direct2_prime)
  apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
  apply(subgoal_tac "ca \<in> parserFS_configurations G1")
   apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
   prefer 2
   apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
  apply(rename_tac G1 d2 x i e v ca cb)(*strict*)
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e v f fa l la r ra)(*strict*)
  apply(simp add: dom_abbreviation)
  apply(clarsimp)
  done

lemma parserS_vs_parserFS_inst_AX_unAX_marked_effect_id2: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o2. o2 \<in> parserFS_unmarked_effect G1 d2 \<longrightarrow> o2 \<in> parserS_unmarked_effect G1 (parserFS_to_parserS_derivation d2)))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o2 x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def parserFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i v e)(*strict*)
  apply(subgoal_tac "\<exists>e c. parserFS_to_parserS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c c' i v e)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c c' i v e)(*strict*)
  apply(subgoal_tac "\<exists>c. parserFS_to_parserS_derivation d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c c' i v e)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c c' i v e)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i v e ea ca cb)(*strict*)
  apply(rule_tac
      x="cb"
      in exI)
  apply(rule_tac
      x="i"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "e = ea \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack c', parserS_conf_scheduler = parserFS_conf_fixed c' @ parserFS_conf_scheduler c'\<rparr> = cb")
   apply(rename_tac G1 d2 x c c' i v e ea ca cb)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c c' i v e ea ca cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i v ea ca)(*strict*)
  apply(subgoal_tac "\<lparr>parserS_conf_stack = parserFS_conf_stack c, parserS_conf_scheduler = parserFS_conf_fixed c @ parserFS_conf_scheduler c\<rparr> = ca")
   apply(rename_tac G1 d2 x c c' i v ea ca)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c c' i v ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
  apply(rule_tac
      x="v"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
   apply(simp add: parserFS.derivation_initial_def)
   apply(simp add: parserFS_initial_configurations_def)
  apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserFS_to_parserS_derivation d2) i = length (parserFS_conf_fixed (the(get_configuration(d2 i))))")
   apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
   prefer 2
   apply(rule parserFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_length)
     apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "c' \<in> parserFS_configurations G1")
   apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
   prefer 2
   apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
  apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
  apply(subgoal_tac "c \<in> parserFS_configurations G1")
   apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
   prefer 2
   apply (metis parserFS.belongs_configurations parserFS.derivation_initial_belongs)
  apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
  apply(subgoal_tac "v = butlast_if_match v (parser_bottom G1)")
   apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
   prefer 2
   apply(subgoal_tac "parser_bottom G1 \<notin> set v")
    apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
    apply (metis butlast_if_match_direct2_prime)
   apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
   apply(simp add: parserFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x i v ea f fa l la r)(*strict*)
   apply(simp add: dom_abbreviation)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
  apply(case_tac "parserFS_conf_fixed c'")
   apply(rename_tac G1 d2 x c c' i v ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i v ea a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. parserFS_conf_fixed c' = w' @ [x']")
   apply(rename_tac G1 d2 x c c' i v ea a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G1 d2 x c c' i v ea a list)(*strict*)
  apply(thin_tac "parserFS_conf_fixed c' = a # list")
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i v ea w' x')(*strict*)
  apply(case_tac "parserFS_conf_scheduler c'")
   apply(rename_tac G1 d2 x c c' i v ea w' x')(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "x'=parser_bottom G1")
    apply(rename_tac G1 d2 x c c' i v ea w' x')(*strict*)
    apply (metis append_is_Nil_conv butlast_if_match_direct butlast_if_match_pull_out not_Cons_self parserFS_get_unfixed_scheduler_def)
   apply(rename_tac G1 d2 x c c' i v ea w' x')(*strict*)
   apply(simp add: parserFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x i v ea w' x' fa l la)(*strict*)
   apply(simp add: dom_abbreviation)
  apply(rename_tac G1 d2 x c c' i v ea w' x' a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. parserFS_conf_scheduler c' = w' @ [x']")
   apply(rename_tac G1 d2 x c c' i v ea w' x' a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac G1 d2 x c c' i v ea w' x' a list)(*strict*)
  apply(thin_tac "parserFS_conf_scheduler c' = a # list")
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i v ea w' x' w'a x'a)(*strict*)
  apply(subgoal_tac "x'\<noteq>parser_bottom G1")
   apply(rename_tac G1 d2 x c c' i v ea w' x' w'a x'a)(*strict*)
   apply (metis ConsApp Cons_eq_appendI Nat.add_0_right add_Suc_right append_assoc butlast_if_match_direct2 butlast_if_match_pull_out butlast_snoc_2 lengthDec2 list.simps(3) takePrecise)
  apply(rename_tac G1 d2 x c c' i v ea w' x' w'a x'a)(*strict*)
  apply(simp add: parserFS_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i v ea w' w'a x'a fa l la)(*strict*)
  apply(simp add: dom_abbreviation)
  done

lemma parserS_vs_parserFS_inst_AX_marked_effect_id1: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o1. o1 \<in> parserS_marked_effect G1 (parserFS_to_parserS_derivation d2) \<longrightarrow> parserS_marking_condition G1 (parserFS_to_parserS_derivation d2) \<longrightarrow> o1 \<in> parserFS_marked_effect G1 d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o1 x)(*strict*)
  apply(simp add: parserS_marked_effect_def parserFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
   apply(case_tac "d2 i")
    apply(rename_tac G1 d2 x c i e ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 x c i e ca a)(*strict*)
   apply(case_tac a)
   apply(rename_tac G1 d2 x c i e ca a option b)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_at_0)
   apply(rule parserFS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(subgoal_tac "ea = e \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack cc, parserS_conf_scheduler = parserFS_conf_fixed cc @ parserFS_conf_scheduler cc\<rparr> = ca")
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e cb cc)(*strict*)
  apply(subgoal_tac "\<lparr>parserS_conf_stack = parserFS_conf_stack cb, parserS_conf_scheduler = parserFS_conf_fixed cb @ parserFS_conf_scheduler cb\<rparr> = c")
   apply(rename_tac G1 d2 x c i e cb cc)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e cb cc)(*strict*)
  apply(subgoal_tac "parserFS_conf_fixed cb=[]")
   apply(rename_tac G1 d2 x i e cb cc)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x i e cb cc)(*strict*)
  apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
  done

lemma parserS_vs_parserFS_inst_AX_marked_effect_id2: "
  \<forall>G1 d2. valid_parser G1 \<and> parserFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o2. o2 \<in> parserFS_marked_effect G1 d2 \<longrightarrow> parserFS_marking_condition G1 d2 \<longrightarrow> o2 \<in> parserS_marked_effect G1 (parserFS_to_parserS_derivation d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o2 x)(*strict*)
  apply(simp add: parserS_marked_effect_def parserFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c)(*strict*)
  apply(simp add: parserFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. parserFS_to_parserS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(rule parserFS.some_position_has_details_at_0)
   apply(rule parserFS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>c. parserFS_to_parserS_derivation d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(case_tac "d2 0")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca a)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(subgoal_tac "\<lparr>parserS_conf_stack = parserFS_conf_stack c, parserS_conf_scheduler = parserFS_conf_fixed c @ parserFS_conf_scheduler c\<rparr> = cb \<and> e = ea \<and> \<lparr>parserS_conf_stack = parserFS_conf_stack ca, parserS_conf_scheduler = parserFS_conf_fixed ca @ parserFS_conf_scheduler ca\<rparr> = cc")
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   prefer 2
   apply(simp add: parserFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i ca ea)(*strict*)
  apply(subgoal_tac "parserFS_conf_fixed c=[]")
   apply(rename_tac G1 d2 x c i ca ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c i ca ea)(*strict*)
  apply(simp add: parserFS.derivation_initial_def parserFS_initial_configurations_def)
  done

lemma parserS_vs_FS_inst_ATS_Bisimulation_Derivation_Strong2_axioms: "
  ATS_Bisimulation_Derivation_Strong2_axioms valid_parser parserS_initial_configurations
     parser_step_labels parserS_step_relation parserS_marking_condition parserS_marked_effect
     parserS_unmarked_effect parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserS_set_unfixed_scheduler_DB
     parserS_get_unfixed_scheduler_DB parserS_get_fixed_scheduler_DB valid_parser
     parserFS_initial_configurations parser_step_labels parserFS_step_relation
     parserFS_marking_condition parserFS_marked_effect parserFS_unmarked_effect
     parser_unfixed_schedulers right_quotient_word (@) parser_unfixed_scheduler_extendable
     parserFS_set_unfixed_scheduler_DB parserFS_get_unfixed_scheduler_DB
     parserFS_get_fixed_scheduler_DB (\<lambda>G1 G2. valid_parser G1 \<and> G1 = G2)
     (\<lambda>G1 G2 o1 o2. G1 = G2 \<and> o1 = o2) (\<lambda>G1 G2 e1 e2. e1 = e2 \<and> e1 \<in> parser_rules G1)
     (\<lambda>G1 G2 d1 d2.
         valid_parser G1 \<and>
         G1 = G2 \<and>
         parserFS.derivation_initial G2
          d2 \<and>
         Ex (maximum_of_domain d2) \<and> parserFS_to_parserS_derivation d2 = d1)  "
  apply(simp add: ATS_Bisimulation_Derivation_Strong2_axioms_def)
  apply (simp add: parser_step_labels_def parserS_vs_parserFS_inst_AX_accept_id1 parserS_vs_parserFS_inst_AX_accept_id2 parserS_vs_parserFS_inst_AX_unAX_marked_effect_id1 parserS_vs_parserFS_inst_AX_unAX_marked_effect_id2 parserS_vs_parserFS_inst_AX_marked_effect_id1 parserS_vs_parserFS_inst_AX_marked_effect_id2 parserS_vs_parserFS_inst_AX_AX_initial_contained1 parserS_vs_parserFS_inst_AX_AX_initial_contained2 parserS_vs_parserFS_inst_AX_on_derivation_initial1 parserS_vs_parserFS_inst_AX_on_finite1 parserS_vs_parserFS_inst_AX_equal_length parserS_vs_parserFS_inst_AX_simulate12 parserS_vs_parserFS_inst_AX_simulate21 parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_crop1 parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_crop2 parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_unfixed_scheduler_extendable1 parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_unfixed_scheduler_extendable2 parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_replace_and_schedF1 parserS_vs_parserFS_inst_AX_bisimulation_compatible_with_replace_and_schedF2)
  done

interpretation "parserS_vs_parserFS" : ATS_Bisimulation_Derivation_Strong2
  (* TSstructure1 *)
  "valid_parser"
  (* configurations1 *)
  "parserS_configurations"
  (* initial_configurations1 *)
  "parserS_initial_configurations"
  (* step_labels1 *)
  "parser_step_labels"
  (* step_relation1 *)
  "parserS_step_relation"
  (* effects1 *)
  "parser_markers"
  (* marking_condition1 *)
  "parserS_marking_condition"
  (* marked_effect1 *)
  "parserS_marked_effect"
  (* unmarked_effect1 *)
  "parserS_unmarked_effect"
  (* fixed_schedulers1 *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler1 *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable1 *)
  "parser_fixed_scheduler_extendable"
  (* scheduler_fragments1 *)
  "parser_scheduler_fragments"
  (* empty_scheduler_fragment1 *)
  "parser_empty_scheduler_fragment"
  (* join_scheduler_fragments1 *)
  "append"
  (* unfixed_schedulers1 *)
  "parser_unfixed_schedulers"
  (* empty_unfixed_scheduler1 *)
  "parser_empty_unfixed_scheduler"
  (* unfixed_scheduler_right_quotient1 *)
  "right_quotient_word"
  (* extend_unfixed_scheduler1 *)
  "append"
  (* unfixed_scheduler_extendable1 *)
  "parser_unfixed_scheduler_extendable"
  (* schedulers1 *)
  "parser_schedulers"
  (* initial_schedulers1 *)
  "parser_schedulers"
  (* empty_scheduler1 *)
  "parser_empty_scheduler"
  (* get_scheduler1 *)
  "parserS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler1 *)
  "append"
  (* join_scheduler_fragments1_sched *)
  "append"
  (* set_unfixed_scheduler_DB1 *)
  "parserS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB1 *)
  "parserS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB1 *)
  "parserS_get_fixed_scheduler_DB"
  (* TSstructure2 *)
  "valid_parser"
  (* configurations2 *)
  "parserFS_configurations"
  (* initial_configurations2 *)
  "parserFS_initial_configurations"
  (* step_labels2 *)
  "parser_step_labels"
  (* step_relation2 *)
  "parserFS_step_relation"
  (* effects2 *)
  "parser_markers"
  (* marking_condition2 *)
  "parserFS_marking_condition"
  (* marked_effect2 *)
  "parserFS_marked_effect"
  (* unmarked_effect2 *)
  "parserFS_unmarked_effect"
  (* fixed_schedulers2 *)
  "parser_fixed_schedulers"
  (* empty_fixed_scheduler2 *)
  "parser_empty_fixed_scheduler"
  (* fixed_scheduler_extendable2 *)
  "parser_fixed_scheduler_extendable"
  (* scheduler_fragments2 *)
  "parser_scheduler_fragments"
  (* empty_scheduler_fragment2 *)
  "parser_empty_scheduler_fragment"
  (* join_scheduler_fragments2 *)
  "append"
  (* unfixed_schedulers2 *)
  "parser_unfixed_schedulers"
  (* empty_unfixed_scheduler2 *)
  "parser_empty_unfixed_scheduler"
  (* unfixed_scheduler_right_quotient2 *)
  "right_quotient_word"
  (* extend_unfixed_scheduler2 *)
  "append"
  (* unfixed_scheduler_extendable2 *)
  "parser_unfixed_scheduler_extendable"
  (* schedulers2 *)
  "parser_schedulers"
  (* initial_schedulers2 *)
  "parser_schedulers"
  (* empty_scheduler2 *)
  "parser_empty_scheduler"
  (* get_scheduler2 *)
  "parserFS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler2 *)
  "append"
  (* extend_scheduler2 *)
  "append"
  (* set_unfixed_scheduler_DB2 *)
  "parserFS_set_unfixed_scheduler_DB"
  (* get_unfixed_scheduler_DB2 *)
  "parserFS_get_unfixed_scheduler_DB"
  (* get_fixed_scheduler_DB2 *)
  "parserFS_get_fixed_scheduler_DB"
  (* TSstructure_rel *)
  "\<lambda>G1 G2. valid_parser G1 \<and> G1=G2"
  (* effect_rel *)
  "\<lambda>G1 G2 o1 o2. G1=G2 \<and> o1=o2"
  (* label_relation *)
  "\<lambda>G1 G2 e1 e2. e1=e2 \<and> e1 \<in> parser_rules G1"
  "\<lambda>G1 G2 d1 d2. (valid_parser G1)
  \<and> (G1=G2)
  \<and> parserFS.derivation_initial G2 d2
  \<and> (\<exists>n. maximum_of_domain d2 n)
  \<and> parserFS_to_parserS_derivation d2 = d1"
  apply(simp add: LOCALE_DEFS parserS_interpretations parserFS_interpretations LOCALE_DEFS)
  apply(simp add: parserS_vs_FS_inst_ATS_Bisimulation_Derivation_Strong2_axioms)
  done

lemma parserS_vs_parserFS_inst_AX_step_labels_unique1: "
  (\<forall>G1 G2 e1 e21 e22. valid_parser G1 \<and> G1 = G2 \<longrightarrow> e1 \<in> parser_step_labels G1 \<longrightarrow> e21 \<in> parser_step_labels G2 \<longrightarrow> e22 \<in> parser_step_labels G2 \<longrightarrow> e1 = e21 \<and> e1 \<in> parser_rules G1 \<longrightarrow> e1 = e22 \<and> e1 \<in> parser_rules G1 \<longrightarrow> e21 = e22)"
  apply(clarsimp)
  done

lemma parserS_vs_parserFS_inst_AX_step_labels_unique2: "
  (\<forall>G1 G2 e11 e12 e2. valid_parser G1 \<and> G1 = G2 \<longrightarrow> e11 \<in> parser_step_labels G1 \<longrightarrow> e12 \<in> parser_step_labels G1 \<longrightarrow> e2 \<in> parser_step_labels G2 \<longrightarrow> e11 = e2 \<and> e11 \<in> parser_rules G1 \<longrightarrow> e12 = e2 \<and> e12 \<in> parser_rules G1 \<longrightarrow> e11 = e12)"
  apply(clarsimp)
  done

lemma parserS_vs_parserFS_inst_AX_step_labels_exists1: "
  (\<forall>G1 G2 e1. valid_parser G1 \<and> G1 = G2 \<longrightarrow> e1 \<in> parser_step_labels G1 \<longrightarrow> (\<exists>e2\<in> parser_step_labels G2. e1 = e2 \<and> e1 \<in> parser_rules G1))"
  apply(clarsimp)
  apply(rename_tac G1 e1)(*strict*)
  apply(simp add: parser_step_labels_def)
  done

lemma parserS_vs_parserFS_inst_AX_step_labels_exists2: "
  (\<forall>G1 G2 e2. valid_parser G1 \<and> G1 = G2 \<longrightarrow> e2 \<in> parser_step_labels G2 \<longrightarrow> (\<exists>e1\<in> parser_step_labels G1. e1 = e2 \<and> e1 \<in> parser_rules G1))"
  apply(clarsimp)
  apply(rename_tac G1 e2)(*strict*)
  apply(simp add: parser_step_labels_def)
  done

theorem parserS_vs_parserFS_Nonblockingness_and_lang_transfer: "
  valid_parser G
  \<Longrightarrow> (parserFS.Nonblockingness_linear_DB G \<longleftrightarrow> parserS.Nonblockingness_linear_DB G)
  \<and> parserFS.unmarked_language G = parserS.unmarked_language G
  \<and> parserFS.marked_language G = parserS.marked_language G"
  apply(rule conjI)
   apply (metis parserS_vs_parserFS.Nonblockingness_translation1 parserS_vs_parserFS.Nonblockingness_translation2)
  apply(rule conjI)
   apply(rule order_antisym)
    apply(rule_tac
      t="parserFS.unmarked_language G"
      and s="parserFS.finite_unmarked_language G"
      in ssubst)
     apply (metis parserFS.AX_unmarked_language_finite)
    apply (metis parserS_vs_parserFS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation2 subsetI)
   apply(rule_tac
      t="parserS.unmarked_language G"
      and s="parserS.finite_unmarked_language G"
      in ssubst)
    apply (metis parserS.AX_unmarked_language_finite)
   apply (metis parserS_vs_parserFS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation1 subsetI)
  apply(rule order_antisym)
   apply(rule_tac
      t="parserFS.marked_language G"
      and s="parserFS.finite_marked_language G"
      in ssubst)
    apply (metis parserFS.AX_marked_language_finite)
   apply (metis parserS_vs_parserFS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation2 subsetI)
  apply(rule_tac
      t="parserS.marked_language G"
      and s="parserS.finite_marked_language G"
      in ssubst)
   apply (metis parserS.AX_marked_language_finite)
  apply (metis parserS_vs_parserFS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation1 subsetI)
  done

theorem parserS_vs_parserFS_is_forward_deterministic_accessible_preserved: "
  valid_parser G
  \<Longrightarrow> parserS.is_forward_deterministic_accessible G
  \<Longrightarrow> parserFS.is_forward_deterministic_accessible G"
  apply(simp add: parserS.is_forward_deterministic_accessible_def parserFS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rule parserFS_dependency_between_determinism_properties_main)
   apply(force)
  apply(clarsimp)
  apply (metis parserS_vs_parserFS.preserve_FEdetermR1)
  done

end
