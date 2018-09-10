section {*I\_kparser\_S\_HFS*}
theory
  I_kparser_S_HFS

imports
  I_kparser_S
  I_kparser_HFS

begin

definition parserHFS_to_parserS_derivation :: "
  (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf)derivation
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf)derivation"
  where
    "parserHFS_to_parserS_derivation d \<equiv>
  \<lambda>n. case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow>
      Some (pair e
        \<lparr>parserS_conf_stack = parserHFS_conf_stack c,
        parserS_conf_scheduler = parserHFS_conf_scheduler c\<rparr>)"

lemma parserHFS_to_parserS_derivation_preserves_derivation_initial: "
  valid_parser P
  \<Longrightarrow> parserHFS.derivation_initial P d
  \<Longrightarrow> parserS.derivation_initial P (parserHFS_to_parserS_derivation d)"
  apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(simp add: parserS.derivation_initial_def)
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
   apply(simp add: parserS_initial_configurations_def parserHFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def parserHFS_configurations_def)
   apply(clarsimp)
  apply(simp add: parserS.derivation_def)
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
  apply(simp add: parserS_step_relation_def parserHFS_step_relation_def)
  apply(clarsimp)
  done

lemma parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> parser_fixed_input_length_recN d n = parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d) n"
  apply(induct n)
   apply(clarsimp)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(case_tac "d(Suc n)")
   apply(rename_tac n)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(rename_tac n a)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e c. d (Suc n) = Some (pair (Some e) c)")
   apply(rename_tac n a)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e c)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
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

lemma parserHFS_to_parserS_derivation_preserves_step_labels: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> \<exists>c. (parserHFS_to_parserS_derivation d) n = Some (pair e c)"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
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
  apply(simp add: parserHFS_to_parserS_derivation_def)
  done

lemma parserHFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> d n \<noteq> None
  \<Longrightarrow> parserHFS_get_fixed_scheduler_DB G d n = parserS_get_fixed_scheduler_DB G (parserHFS_to_parserS_derivation d) n"
  apply(induct n)
   apply(simp add: parserHFS_get_fixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
  apply(rename_tac n)(*strict*)
  apply(clarsimp)
  apply(rename_tac n y)(*strict*)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac n y)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac n y)(*strict*)
     apply(force)
    apply(rename_tac n y)(*strict*)
    apply(force)
   apply(rename_tac n y)(*strict*)
   apply(force)
  apply(rename_tac n y)(*strict*)
  apply(clarsimp)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "\<exists>c. parserHFS_to_parserS_derivation d (Suc n) = Some (pair (Some e2) c)")
   apply(rename_tac n e1 e2 c1 c2)(*strict*)
   apply(clarsimp)
   apply(rename_tac n e1 e2 c1 c2 c)(*strict*)
   apply(simp add: get_configuration_def get_configuration_def)
   apply(subgoal_tac "\<exists>c. parserHFS_to_parserS_derivation d n = Some (pair e1 c)")
    apply(rename_tac n e1 e2 c1 c2 c)(*strict*)
    apply(clarsimp)
    apply(rename_tac n e1 e2 c1 c2 c ca)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d) n = parser_fixed_input_length_recN d n")
     apply(rename_tac n e1 e2 c1 c2 c ca)(*strict*)
     apply(clarsimp)
     apply(simp add: parserHFS_step_relation_def)
     apply(subgoal_tac "valid_parser_step_label G e2")
      apply(rename_tac n e1 e2 c1 c2 c ca)(*strict*)
      prefer 2
      apply(simp add: valid_parser_def)
     apply(rename_tac n e1 e2 c1 c2 c ca)(*strict*)
     apply(clarsimp)
     apply(rename_tac n e1 e2 c1 c2 c ca x xa y)(*strict*)
     apply(simp add: valid_parser_step_label_def)
     apply(clarsimp)
     apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
     apply(simp add: parserHFS_get_scheduler_def parserS_get_scheduler_def)
     apply(rule_tac
      t="length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2)"
      and s="length xc"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
      apply (metis butn_length butn_prefix_closureise)
     apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
     apply(case_tac "(parser_fixed_input_length_recN d n)- (length (kPrefix k (w @ [parser_bottom G])))")
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "max (parser_fixed_input_length_recN d n) (length (kPrefix k (w @ [parser_bottom G])))=(length (kPrefix k (w @ [parser_bottom G])))")
       apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      t="(length (kPrefix k (w @ [parser_bottom G])) - length xc)"
      and s="length (rule_rpush e2)"
      in ssubst)
       apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
       apply (metis dropPrecise length_drop)
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
      apply(rule_tac
      t="take (length (rule_rpush e2)) (rule_rpush e2)"
      and s="rule_rpush e2"
      in ssubst)
       apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
       apply(force)
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
      apply(rule_tac
      t="(length (kPrefix k (w @ [parser_bottom G])) - (length xc + length (rule_rpush e2)))"
      and s="0"
      in ssubst)
       apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
       apply (metis diff_self_eq_0 length_append)
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc)(*strict*)
      apply(clarsimp)
      apply(simp add: parserHFS_to_parserS_derivation_def)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
     apply(subgoal_tac "max (parser_fixed_input_length_recN d n) (length (kPrefix k (w @ [parser_bottom G])))=parser_fixed_input_length_recN d n")
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="(length (kPrefix k (w @ [parser_bottom G])) - length xc)"
      and s="length (rule_rpush e2)"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
      apply (metis dropPrecise length_drop)
     apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
     apply(rule_tac
      t="take (length (rule_rpush e2)) (rule_rpush e2)"
      and s="rule_rpush e2"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
      apply(force)
     apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
     apply(rule_tac
      t="(length (kPrefix k (w @ [parser_bottom G])) - (length xc + length (rule_rpush e2)))"
      and s="0"
      in ssubst)
      apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
      apply (metis diff_self_eq_0 length_append)
     apply(rename_tac n e1 e2 c1 c2 c ca x xa y k w xc nat)(*strict*)
     apply(simp add: parserHFS_to_parserS_derivation_def)
     apply(force)
    apply(rename_tac n e1 e2 c1 c2 c ca)(*strict*)
    apply (metis parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
   apply(rename_tac n e1 e2 c1 c2 c)(*strict*)
   apply (metis parserHFS_to_parserS_derivation_preserves_step_labels)
  apply(rename_tac n e1 e2 c1 c2)(*strict*)
  apply (metis parserHFS_to_parserS_derivation_preserves_step_labels)
  done

lemma parserHFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_uniform: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G dh
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> maximum_of_domain (parserHFS_to_parserS_derivation dh) n
  \<Longrightarrow> parserHFS.derivation_initial G dc'
  \<Longrightarrow> parserHFS_get_unfixed_scheduler_DB G dh n \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> sUF \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> sUF \<in> parser_unfixed_schedulers G
  \<Longrightarrow> parserHFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) dc n
  \<Longrightarrow> maximum_of_domain dc' (n+n')
  \<Longrightarrow> x \<le> n
  \<Longrightarrow> parserHFS_get_fixed_scheduler_DB G dh x = parserHFS_get_fixed_scheduler_DB G dc' x"
  apply(rule_tac
      t="parserHFS_get_fixed_scheduler_DB G dc' x"
      and s="parserS_get_fixed_scheduler_DB G (parserHFS_to_parserS_derivation dc') x"
      in ssubst)
   apply(rule parserHFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB)
     apply(force)
    apply(simp add: parserHFS.derivation_initial_def)
   apply(rule parserHFS.not_none_before_maximum_of_domain)
      apply(force)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(force)
   apply(force)
  apply(rule_tac
      t="parserHFS_to_parserS_derivation dc'"
      and s="derivation_append (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) dc n"
      in ssubst)
   apply(force)
  apply(thin_tac "parserHFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) dc n")
  apply(rule_tac
      t="parserS_get_fixed_scheduler_DB G (derivation_append (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) dc n) x"
      and s="parserS_get_fixed_scheduler_DB G ((parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) ) x"
      in ssubst)
   apply(rule parserS.AX_get_fixed_scheduler_DB_restrict)
     apply(force)+
   defer
   apply(rule_tac
      t="parserS_get_fixed_scheduler_DB G (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) x"
      and s="parserS_get_fixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) x"
      in ssubst)
    defer
    apply(rule parserHFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB)
      apply(force)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rule parserHFS.not_none_before_maximum_of_domain)
       apply(force)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(force)
    apply(force)
   apply(subgoal_tac "parserS.derivation_initial G (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n)")
    apply(simp add: parserS.derivation_initial_def)
   apply(rule parserS.sched_modification_preserves_derivation_initial)
         apply(force)
        prefer 6
        apply(simp add: parserS.replace_unfixed_scheduler_DB_def)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(force)
     apply(subgoal_tac "parserHFS_get_unfixed_scheduler_DB G dh n \<sqsupseteq> [parser_bottom G]")
      apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
       apply(clarsimp)
       apply(rename_tac e c)(*strict*)
       apply(subgoal_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) n = parser_fixed_input_length_recN dh n")
        apply(rename_tac e c)(*strict*)
        apply(simp add: parserS_get_unfixed_scheduler_DB_def parserHFS_to_parserS_derivation_def)
        apply(simp add: get_configuration_def parserS_get_scheduler_def)
        apply(simp add: parserHFS_get_unfixed_scheduler_DB_def)
        apply(simp add: get_configuration_def parserHFS_get_scheduler_def)
       apply(rename_tac e c)(*strict*)
       apply(rule sym)
       apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
        apply(rename_tac e c)(*strict*)
        apply(force)
       apply(rename_tac e c)(*strict*)
       apply(simp add: parserHFS.derivation_initial_def)
      apply(simp add: maximum_of_domain_def)
      apply(clarsimp)
      apply(rename_tac y ya)(*strict*)
      apply(case_tac yb)
      apply(rename_tac y ya option b)(*strict*)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>e c. dh x= Some (pair e c)")
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(simp add: parserHFS.derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: parserS_get_fixed_scheduler_DB_def)
  apply(case_tac "parserHFS_to_parserS_derivation dh x")
   apply(simp add: parserHFS_to_parserS_derivation_def)
   apply(clarsimp)
  apply(rename_tac a)(*strict*)
  apply(case_tac a)
  apply(rename_tac a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac option b e c)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) x"
      and s="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) x"
      in ssubst)
   apply(rename_tac option b e c)(*strict*)
   apply(thin_tac "parserHFS_to_parserS_derivation dh x = Some (pair option b)")
   apply(induct x arbitrary: e c)
    apply(rename_tac option b e c)(*strict*)
    apply(clarsimp)
   apply(rename_tac x option b e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac x e c)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh x = Some (pair e1 c1) \<and> dh (Suc x) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
    apply(rename_tac x e c)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc x"
      in parserHFS.step_detail_before_some_position)
      apply(rename_tac x e c)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
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
      t="parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) x"
      and s="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) x"
      in ssubst)
    apply(rename_tac x c e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac x c e1 e2 c1)(*strict*)
   apply(thin_tac "parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) x = parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) x")
   apply(rename_tac x c e1 e2 c1)(*strict*)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def)
   apply(simp add: parserS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>c. parserHFS_to_parserS_derivation dh (Suc x) = Some (pair (Some e2) c)")
    apply(rename_tac x c e1 e2 c1)(*strict*)
    apply(clarsimp)
   apply(rename_tac x c e1 e2 c1)(*strict*)
   apply(rule parserHFS_to_parserS_derivation_preserves_step_labels)
     apply(rename_tac x c e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac x c e1 e2 c1)(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
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
   apply(subgoal_tac "\<exists>c. parserHFS_to_parserS_derivation dh n = Some (pair ea c)")
    apply(rename_tac option b e c ea ca)(*strict*)
    apply(clarsimp)
    apply(rename_tac option b e c ea ca cb)(*strict*)
    apply(subgoal_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) x - length (parserS_get_fixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) x) = 0")
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
      apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac option b e c ea ca cb)(*strict*)
     apply(subgoal_tac "parserS.derivation_initial G (parserHFS_to_parserS_derivation dh)")
      apply(rename_tac option b e c ea ca cb)(*strict*)
      apply(simp add: parserS.derivation_initial_def)
     apply(rename_tac option b e c ea ca cb)(*strict*)
     apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac option b e c ea ca cb)(*strict*)
    apply(force)
   apply(rename_tac option b e c ea ca)(*strict*)
   apply(rule parserHFS_to_parserS_derivation_preserves_step_labels)
     apply(rename_tac option b e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac option b e c ea ca)(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
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

lemma parserHFS_to_parserS_derivation_preserves_maximum_of_domain: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (parserHFS_to_parserS_derivation d) n"
  apply(simp add: maximum_of_domain_def parserHFS_to_parserS_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

definition parserS_to_parserHFS_derivation :: "
  ('stack, 'event, 'marker) parser
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserS_conf) derivation
  \<Rightarrow> (('stack, 'event) parser_step_label, ('stack, 'event) parserHFS_conf)derivation"
  where
    "parserS_to_parserHFS_derivation G d \<equiv>
  \<lambda>n.
  case d n of
  None \<Rightarrow> None
  | Some (pair e c) \<Rightarrow>
      Some (pair e
        \<lparr>parserHFS_conf_fixed
          = take
              (parser_fixed_input_length_recN d n)
              (parserS_conf_scheduler c),
        parserHFS_conf_history
          = (the (right_quotient_word
                    (parserS_conf_scheduler
                      (the (get_configuration (d 0))))
                    (parserS_conf_scheduler c)))
            @ (butlast_if_match
                (take
                  (parser_fixed_input_length_recN d n)
                  (parserS_conf_scheduler c))
                (parser_bottom G)),
        parserHFS_conf_stack = parserS_conf_stack c,
        parserHFS_conf_scheduler = parserS_conf_scheduler c\<rparr>)"

lemma parserS_to_parserHFS_derivation_preserves_derivation_initial: "
  valid_parser P
  \<Longrightarrow> parserS.derivation_initial P d
  \<Longrightarrow> parserHFS.derivation_initial P (parserS_to_parserHFS_derivation P d)"
  apply(simp add: parserS_to_parserHFS_derivation_def)
  apply(simp add: parserHFS.derivation_initial_def)
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
   apply(simp add: parserS_initial_configurations_def parserHFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: parserS_configurations_def parserHFS_configurations_def)
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: right_quotient_word_def)
   apply(simp add: prefix_def)
   apply(simp add: suffix_def butlast_if_match_def)
  apply(simp add: parserHFS.derivation_def)
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
  apply(simp add: parserS_step_relation_def parserHFS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
  apply(subgoal_tac "\<exists>c. d 0 = Some (pair None c)")
   apply(rename_tac nat e1 e2 c1 c2 x xa)(*strict*)
   prefer 2
   apply(rule parserS.some_position_has_details_at_0)
   apply(simp add: parserS.derivation_initial_def)
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
  apply(rule conjI)
   apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
   apply(subgoal_tac "c2 \<in> parserS_configurations P")
    apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
    apply(simp add: parserS_configurations_def)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 x xa c k w wa xc)(*strict*)
    apply(rule_tac
      x="wa"
      in exI)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
   apply(rule parserS.belongs_configurations)
    apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
    apply(rule parserS.derivation_initial_belongs)
     apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa c)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c = w @ (parserS_string_state c1)")
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
   prefer 2
   apply(rule_tac
      j="nat"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
        apply(force)
       apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
      apply(rule parserS.derivation_initial_belongs)
       apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
     apply(simp add: parserS.derivation_initial_def)
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserS_string_state c1 = w @ (parserS_string_state c2)")
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
   prefer 2
   apply(rule_tac
      j="Suc 0"
      in parserS.derivation_monotonically_dec)
        apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
        apply(force)
       apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
      apply(rule parserS.derivation_initial_belongs)
       apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
       apply(force)
      apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
     apply(simp add: parserS.derivation_initial_def)
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
  apply(subgoal_tac "c \<in> parserS_configurations P")
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
   prefer 2
   apply(rule parserS.belongs_configurations)
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
    apply(rule parserS.derivation_initial_belongs)
     apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w xc wa)(*strict*)
  apply(simp add: parserS_string_state_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa c k w wa wb)(*strict*)
  apply(simp add: right_quotient_word_def)
  apply(simp add: parserS_configurations_def)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc)(*strict*)
  apply(case_tac "(\<exists>x. x @ [parser_bottom P] = wb @ rule_rpush e2)")
   apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc xb xc)(*strict*)
   apply(case_tac e2)
   apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc xb xc rule_lpopa rule_rpopa rule_lpusha rule_rpusha)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 c1 c2 x xa k w wa wb l wc xb rule_lpop rule_lpush)(*strict*)
   apply(subgoal_tac "xa=[]")
    apply(rename_tac nat e1 c1 c2 x xa k w wa wb l wc xb rule_lpop rule_lpush)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
    apply(simp add: kPrefix_def)
    apply(case_tac "k-length w")
     apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom P \<in> set w")
      apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
      apply(subgoal_tac "parser_bottom P \<notin> set w")
       apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
       apply(force)
      apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
      apply(force)
     apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
     apply(rule_tac
      A="set (take k w)"
      in set_mp)
      apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
      apply(rule set_take_subset)
     apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
     apply(rule_tac
      t="take k w"
      and s="wb @ xb @ [parser_bottom P]"
      in ssubst)
      apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
      apply(force)
     apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush)(*strict*)
     apply(simp (no_asm))
    apply(rename_tac nat e1 c1 c2 x k w wa wb l xb rule_lpop rule_lpush nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 c1 c2 x k wa wb l xb rule_lpop rule_lpush nata)(*strict*)
    apply(subgoal_tac "k=Suc nata+length wb+length xb")
     apply(rename_tac nat e1 c1 c2 x k wa wb l xb rule_lpop rule_lpush nata)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac nat e1 c1 c2 x k wa wb l xb rule_lpop rule_lpush nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
    apply(subgoal_tac "butlast_if_match (wb @ xb @ [parser_bottom P]) (parser_bottom P) = wb@xb")
     apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "butlast_if_match (xb @ [parser_bottom P]) (parser_bottom P) = xb")
      apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
      apply(clarsimp)
      apply(case_tac "parser_fixed_input_length_recN d nat - (length wb + length xb)")
       apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "min (Suc (length wb + length xb)) (parser_fixed_input_length_recN d nat)=parser_fixed_input_length_recN d nat")
        apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
        prefer 2
        apply(force)
       apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
       apply(subgoal_tac "butlast_if_match (take (parser_fixed_input_length_recN d nat) wb @ take (parser_fixed_input_length_recN d nat - length wb) xb) (parser_bottom P) = take (parser_fixed_input_length_recN d nat) wb @ take (parser_fixed_input_length_recN d nat - length wb) xb")
        apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
        prefer 2
        apply(rule butlast_if_match_direct2_prime)
        apply(rule_tac
      B="set(wb@xb)"
      in nset_mp)
         apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
         prefer 2
         apply(force)
        apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
        apply(simp (no_asm))
        apply(subgoal_tac "set (take (parser_fixed_input_length_recN d nat) wb) \<subseteq> set wb")
         apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
         prefer 2
         apply(rule set_take_subset)
        apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
        apply(subgoal_tac "set (take (parser_fixed_input_length_recN d nat - length wb) xb) \<subseteq> set xb")
         apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
         prefer 2
         apply(rule set_take_subset)
        apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
        apply(force)
       apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
       apply(clarsimp)
       apply(case_tac "parser_fixed_input_length_recN d nat - length wb")
        apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
        apply(clarsimp)
       apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush nata)(*strict*)
       apply(clarsimp)
      apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush nata)(*strict*)
      apply(clarsimp)
     apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
     apply(rule butlast_if_match_direct)
     apply(force)
    apply(rename_tac nat e1 c1 c2 x wa wb l xb rule_lpop rule_lpush)(*strict*)
    apply(rule butlast_if_match_direct)
    apply(force)
   apply(rename_tac nat e1 c1 c2 x xa k w wa wb l wc xb rule_lpop rule_lpush)(*strict*)
   apply(case_tac xa)
    apply(rename_tac nat e1 c1 c2 x xa k w wa wb l wc xb rule_lpop rule_lpush)(*strict*)
    apply(force)
   apply(rename_tac nat e1 c1 c2 x xa k w wa wb l wc xb rule_lpop rule_lpush a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
    apply(rename_tac nat e1 c1 c2 x xa k w wa wb l wc xb rule_lpop rule_lpush a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac nat e1 c1 c2 x xa k w wa wb l wc xb rule_lpop rule_lpush a list)(*strict*)
   apply(thin_tac "xa=a#list")
   apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc)(*strict*)
  apply(clarsimp)
  apply(case_tac xa)
   apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc)(*strict*)
   apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l wc)(*strict*)
   apply(case_tac "wb @ rule_rpush e2")
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l wc)(*strict*)
    apply(clarsimp)
    apply(rename_tac nat e1 e2 c1 c2 x k w l wc)(*strict*)
    apply(simp add: butlast_if_match_def)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l wc a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. wb @ rule_rpush e2 = w' @ [x']")
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l wc a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l wc a list)(*strict*)
   apply(thin_tac "wb @ rule_rpush e2=a#list")
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
   apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x xa k w wa wb l wc a list)(*strict*)
  apply(thin_tac "xa=a#list")
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
  apply(case_tac "parser_fixed_input_length_recN d nat - (length wb + length (rule_rpush e2) + length w')")
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
   apply(subgoal_tac "min (Suc (length wb + length (rule_rpush e2) + length w')) (parser_fixed_input_length_recN d nat) = (parser_fixed_input_length_recN d nat)")
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
   apply(clarsimp)
   apply(case_tac "parser_fixed_input_length_recN d nat - (length wb + length (rule_rpush e2))")
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (rule_rpush e2) (parser_bottom P)= rule_rpush e2")
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "butlast_if_match (take (parser_fixed_input_length_recN d nat) wb @ take (parser_fixed_input_length_recN d nat - length wb) (rule_rpush e2)) (parser_bottom P) = take (parser_fixed_input_length_recN d nat) wb @ take (parser_fixed_input_length_recN d nat - length wb) (rule_rpush e2)")
      apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
      apply(clarsimp)
      apply(subgoal_tac "butlast_if_match (wb @ rule_rpush e2) (parser_bottom P) = wb @ rule_rpush e2")
       apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
       apply(clarsimp)
       apply(case_tac "parser_fixed_input_length_recN d nat - length wb")
        apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
        apply(clarsimp)
       apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
       apply(clarsimp)
      apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
      apply(rule butlast_if_match_direct2_prime)
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(rule_tac
      B="set(wb@rule_rpush e2)"
      in nset_mp)
      apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
     apply(simp (no_asm))
     apply(subgoal_tac "set (take (parser_fixed_input_length_recN d nat) wb) \<subseteq> set wb")
      apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
      prefer 2
      apply(rule set_take_subset)
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
     apply(subgoal_tac "set (take (parser_fixed_input_length_recN d nat - length wb) (rule_rpush e2)) \<subseteq> set (rule_rpush e2)")
      apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
      prefer 2
      apply(rule set_take_subset)
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w')(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "max (parser_fixed_input_length_recN d nat) (length wb + length (rule_rpush e2)) = (parser_fixed_input_length_recN d nat)")
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="butlast_if_match (rule_rpush e2 @ take (Suc nata) w') (parser_bottom P)"
      and s="(rule_rpush e2 @ take (Suc nata) w')"
      in ssubst)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(rule_tac
      B="set(rule_rpush e2@w')"
      in nset_mp)
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(simp (no_asm))
    apply(subgoal_tac "set (take (Suc nata) w') \<subseteq> set (w')")
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
     prefer 2
     apply(rule set_take_subset)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(force)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
   apply(rule_tac
      t="butlast_if_match (wb @ rule_rpush e2 @ take (Suc nata) w') (parser_bottom P)"
      and s="(wb @ rule_rpush e2 @ take (Suc nata) w')"
      in ssubst)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(clarsimp)
    apply(subgoal_tac "parser_bottom P \<notin> set (take (Suc nata) w')")
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(rule_tac
      B="set(w')"
      in nset_mp)
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(rule set_take_subset)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="butlast_if_match (wb @ rule_rpush e2) (parser_bottom P)"
      and s="(wb @ rule_rpush e2)"
      in ssubst)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "butlast_if_match (rule_rpush e2 @ w' @ [parser_bottom P]) (parser_bottom P)=rule_rpush e2 @ w'")
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast_if_match (wb @ rule_rpush e2 @ w' @ [parser_bottom P]) (parser_bottom P) = wb @ rule_rpush e2 @ w'")
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast_if_match (wb @ rule_rpush e2) (parser_bottom P)=wb @ rule_rpush e2")
     apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply(clarsimp)
   apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
   apply(rule butlast_if_match_direct)
   apply(force)
  apply(rename_tac nat e1 e2 c1 c2 x k w wa wb l w' nata)(*strict*)
  apply(rule butlast_if_match_direct)
  apply(force)
  done

lemma parserS_to_parserHFS_derivation_preserves_maximum_of_domain: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> maximum_of_domain (parserS_to_parserHFS_derivation G d) n"
  apply(simp add: maximum_of_domain_def parserS_to_parserHFS_derivation_def)
  apply(clarsimp)
  apply(rename_tac y)(*strict*)
  apply(case_tac y)
  apply(rename_tac y option b)(*strict*)
  apply(clarsimp)
  done

lemma parser_S_HFS_relation_coincide_hlp: "
  valid_parser G2
  \<Longrightarrow> parserHFS.derivation_initial G2 d2
  \<Longrightarrow> maximum_of_domain d2 x
  \<Longrightarrow> parserS_to_parserHFS_derivation G2 (parserHFS_to_parserS_derivation d2) xa = d2 xa"
  apply(induct xa)
   apply(simp add: parserHFS_to_parserS_derivation_def parserS_to_parserHFS_derivation_def)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(clarsimp)
    apply(rename_tac c)(*strict*)
    apply(case_tac c)
    apply(rename_tac c parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
    apply(clarsimp)
    apply(rename_tac parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
    apply(clarsimp)
    apply(simp add: parserHFS_initial_configurations_def)
    apply(clarsimp)
    apply(rename_tac parserHFS_conf_scheduler)(*strict*)
    apply(simp add: get_configuration_def)
    apply(simp add: butlast_if_match_def right_quotient_word_def)
   apply(simp add: parserHFS.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac "d2 0")
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac a option b)(*strict*)
   apply(force)
  apply(rename_tac xa)(*strict*)
  apply(clarsimp)
  apply(case_tac "d2 (Suc xa)")
   apply(rename_tac xa)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS_to_parserS_derivation_def parserS_to_parserHFS_derivation_def)
  apply(rename_tac xa a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d2 xa = Some (pair e1 c1) \<and> d2 (Suc xa) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G2 c1 e2 c2")
   apply(rename_tac xa a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc xa"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac xa a)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac xa a)(*strict*)
    apply(force)
   apply(rename_tac xa a)(*strict*)
   apply(force)
  apply(rename_tac xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(simp add: parserS_to_parserHFS_derivation_def)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) xa = parser_fixed_input_length_recN d2 xa")
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
    apply(rename_tac xa e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   apply(simp add: parserHFS.derivation_initial_def)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) (Suc xa) = parser_fixed_input_length_recN d2 (Suc xa)")
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
    apply(rename_tac xa e1 e2 c1 c2)(*strict*)
    apply(force)
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   apply(simp add: parserHFS.derivation_initial_def)
  apply(rename_tac xa e1 e2 c1 c2)(*strict*)
  apply(clarsimp)
  apply(simp add: parserHFS_to_parserS_derivation_def parserS_to_parserHFS_derivation_def)
  apply(subgoal_tac "\<exists> c. d2 0 = Some (pair None c)")
   apply(rename_tac xa e1 e2 c1 c2)(*strict*)
   prefer 2
   apply(simp add: parserHFS.derivation_initial_def)
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
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state c = w @ parserHFS_string_state c1")
   apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in parserHFS.derivation_monotonically_dec)
        apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
        apply(force)
       apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
       apply(force)
      apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
       apply(force)
      apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
      apply(force)
     apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
    apply(force)
   apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
   apply(force)
  apply(rename_tac xa e1 e2 c1 c2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state c1 = w @ parserHFS_string_state c2")
   apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      and i="xa"
      and j="Suc 0"
      in parserHFS.derivation_monotonically_dec)
        apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
        apply(force)
       apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
       apply(force)
      apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
       apply(force)
      apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
      apply(force)
     apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
    apply(force)
   apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
   apply(force)
  apply(rename_tac xa e1 e2 c1 c2 c w)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
  apply(simp add: parserHFS_string_state_def)
  apply(simp add: parserHFS_step_relation_def)
  apply(subgoal_tac "valid_parser_step_label G2 e2")
   apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac xa e1 e2 c1 c2 c w wa)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c2 c w wa xb xba y)(*strict*)
  apply(simp add: valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c2 c w wa xb xba y k wb xd)(*strict*)
  apply(case_tac c2)
  apply(rename_tac xa e1 e2 c2 c w wa xb xba y k wb xd parserHFS_conf_fixeda parserHFS_conf_historya parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c w wa xb xba y k wb xd)(*strict*)
  apply(subgoal_tac "wa=xd")
   apply(rename_tac xa e1 e2 c w wa xb xba y k wb xd)(*strict*)
   prefer 2
   apply (metis append_injective1)
  apply(rename_tac xa e1 e2 c w wa xb xba y k wb xd)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(subgoal_tac "right_quotient_word (w @ xd @ rule_rpush e2 @ xba) (rule_rpush e2 @ xba) =Some (w@xd)")
   apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
   prefer 2
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(clarsimp)
  apply(thin_tac "right_quotient_word (w @ xd @ rule_rpush e2 @ xba) (rule_rpush e2 @ xba) =Some (w@xd)")
  apply(subgoal_tac "right_quotient_word (w @ xd @ rule_rpush e2 @ xba) (xd@rule_rpush e2 @ xba) =Some w")
   apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
   prefer 2
   apply(rule right_quotient_word_Some_by_append)
   apply(force)
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(clarsimp)
  apply(thin_tac "right_quotient_word (w @ xd @ rule_rpush e2 @ xba) (xd@rule_rpush e2 @ xba) =Some w")
  apply(subgoal_tac "length (kPrefix k (wb @ [parser_bottom G2])) - length (rule_rpush e2) = length xd")
   apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
   prefer 2
   apply (metis diff_add_inverse2 length_append)
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(clarsimp)
  apply(thin_tac "length (kPrefix k (wb @ [parser_bottom G2])) - length (rule_rpush e2) = length xd")
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(thin_tac "d2 (Suc xa) = Some (pair (Some e2) \<lparr>parserHFS_conf_fixed = rule_rpush e2 @ drop (length (kPrefix k (wb @ [parser_bottom G2])) - min (length xd) (parser_fixed_input_length_recN d2 xa)) (take (parser_fixed_input_length_recN d2 xa - length xd) (rule_rpush e2)) @ drop (length (kPrefix k (wb @ [parser_bottom G2])) - (min (length xd) (parser_fixed_input_length_recN d2 xa) + min (length (rule_rpush e2)) (parser_fixed_input_length_recN d2 xa - length xd))) (take (parser_fixed_input_length_recN d2 xa - (length xd + length (rule_rpush e2))) xba), parserHFS_conf_history = w @ butlast_if_match (take (parser_fixed_input_length_recN d2 xa) xd @ take (parser_fixed_input_length_recN d2 xa - length xd) (rule_rpush e2) @ take (parser_fixed_input_length_recN d2 xa - (length xd + length (rule_rpush e2))) xba) (parser_bottom G2) @ drop (min (length xd) (parser_fixed_input_length_recN d2 xa) + (min (length (rule_rpush e2)) (parser_fixed_input_length_recN d2 xa - length xd) + min (length xba) (parser_fixed_input_length_recN d2 xa - (length xd + length (rule_rpush e2))))) (butlast_if_match (kPrefix k (wb @ [parser_bottom G2])) (parser_bottom G2)), parserHFS_conf_stack = xb @ rule_lpush e2, parserHFS_conf_scheduler = rule_rpush e2 @ xba\<rparr>)")
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(thin_tac "d2 xa = Some (pair e1 \<lparr>parserHFS_conf_fixed = take (parser_fixed_input_length_recN d2 xa) xd @ take (parser_fixed_input_length_recN d2 xa - length xd) (rule_rpush e2) @ take (parser_fixed_input_length_recN d2 xa - (length xd + length (rule_rpush e2))) xba, parserHFS_conf_history = w @ butlast_if_match (take (parser_fixed_input_length_recN d2 xa) xd @ take (parser_fixed_input_length_recN d2 xa - length xd) (rule_rpush e2) @ take (parser_fixed_input_length_recN d2 xa - (length xd + length (rule_rpush e2))) xba) (parser_bottom G2), parserHFS_conf_stack = xb @ rule_lpop e2, parserHFS_conf_scheduler = xd @ rule_rpush e2 @ xba\<rparr>)")
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(thin_tac "parser_fixed_input_length_recN (\<lambda>n. case_option None (case_derivation_configuration (\<lambda>e c. Some (pair e \<lparr>parserS_conf_stack = parserHFS_conf_stack c, parserS_conf_scheduler = parserHFS_conf_scheduler c\<rparr>))) (d2 n)) xa = parser_fixed_input_length_recN d2 xa")
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(rule conjI)
   apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
   apply(case_tac "(parser_fixed_input_length_recN d2 xa) -(length (kPrefix k (wb @ [parser_bottom G2])))")
    apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
    apply(clarsimp)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(subgoal_tac "max (parser_fixed_input_length_recN d2 xa) (length (kPrefix k (wb @ [parser_bottom G2]))) = (length (kPrefix k (wb @ [parser_bottom G2])))")
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(clarsimp)
    apply (metis append_Nil2 diff_self_eq_0 drop_length_append kPrefix_def le_diff_conv2 le_refl length_append add.commute take_0 take_all)
   apply(rename_tac xa e1 e2 c w xb xba y k wb xd nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(subgoal_tac "max (parser_fixed_input_length_recN d2 xa) (length (kPrefix k (wb @ [parser_bottom G2]))) = (parser_fixed_input_length_recN d2 xa)")
    apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parser_fixed_input_length_recN d2 xa = Suc nat+ length (kPrefix k (wb @ [parser_bottom G2]))")
    apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="kPrefix k (wb @ [parser_bottom G2])"
      and s="xd @ rule_rpush e2"
      in ssubst)
    apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(thin_tac "xd @ rule_rpush e2=kPrefix k (wb @ [parser_bottom G2])")
   apply(clarsimp)
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
  apply(case_tac "(parser_fixed_input_length_recN d2 xa) -(length (kPrefix k (wb @ [parser_bottom G2])))")
   apply(rename_tac xa e1 e2 c w xb xba y k wb xd)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
   apply(subgoal_tac "max (parser_fixed_input_length_recN d2 xa) (length (kPrefix k (wb @ [parser_bottom G2]))) = (length (kPrefix k (wb @ [parser_bottom G2])))")
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
   apply(clarsimp)
   apply(thin_tac "max (parser_fixed_input_length_recN d2 xa) (length (kPrefix k (wb @ [parser_bottom G2]))) = (length (kPrefix k (wb @ [parser_bottom G2])))")
   apply(rule_tac
      t="kPrefix k (wb @ [parser_bottom G2])"
      and s="xd @ rule_rpush e2"
      in ssubst)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
   apply(subgoal_tac "length (xd @ rule_rpush e2) - length xd = length (rule_rpush e2)")
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    prefer 2
    apply(simp (no_asm))
   apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="min (length xd) (parser_fixed_input_length_recN d2 xa) + min (length (rule_rpush e2)) (parser_fixed_input_length_recN d2 xa - length xd)"
      and s="parser_fixed_input_length_recN d2 xa"
      in ssubst)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
   apply(rule_tac
      t="kPrefix k (wb @ [parser_bottom G2])"
      and s="xd @ rule_rpush e2"
      in ssubst)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
   apply(rule_tac
      t="take (parser_fixed_input_length_recN d2 xa) xd @ take (parser_fixed_input_length_recN d2 xa - length xd) (rule_rpush e2)"
      and s="take (parser_fixed_input_length_recN d2 xa) (xd @ rule_rpush e2)"
      in ssubst)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(simp (no_asm))
   apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
   apply(case_tac xb)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(rule_tac
      t="butlast_if_match (rule_rpush e2) (parser_bottom G2)"
      and s="y"
      in ssubst)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply (metis append_Nil2 butlast_if_match_direct)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(rule_tac
      t="butlast_if_match (xd @ rule_rpush e2) (parser_bottom G2)"
      and s="xd @ y"
      in ssubst)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply (metis butlast_append last_append Nil_is_append_conv append_butlast_last_id butlast_if_match_direct butlast_if_match_direct2_prime butlast_snoc impossible_Cons last_snoc le0 length_pos_if_in_set list.size(3) self_append_conv)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(rule_tac
      t="butlast_if_match (take (parser_fixed_input_length_recN d2 xa) (xd @ rule_rpush e2)) (parser_bottom G2)"
      and s="take (parser_fixed_input_length_recN d2 xa) (xd @ y)"
      in ssubst)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     prefer 2
     apply (metis append_take_drop_id_hlp kPrefix_def)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(rule_tac
      t="rule_rpush e2"
      and s="y @ [parser_bottom G2]"
      in ssubst)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply(force)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(case_tac "parser_fixed_input_length_recN d2 xa \<ge> length (xd @ y @ [parser_bottom G2])")
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply(rule_tac
      t="take (parser_fixed_input_length_recN d2 xa) (xd @ y @ [parser_bottom G2])"
      and s="xd @ y @ [parser_bottom G2]"
      in ssubst)
      apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
      apply(force)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply(rule_tac
      t="take (parser_fixed_input_length_recN d2 xa) (xd @ y)"
      and s="xd@y"
      in ssubst)
      apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
      apply (metis Nil_is_append_conv append_Nil2 append_butlast_last_id butlast_snoc concat_asso drop_length_append impossible_Cons kPrefix_def le_antisym le_refl list.size(3) take_all)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply (metis butlast_append last_append Nil_is_append_conv append_butlast_last_id butlast_if_match_direct butlast_if_match_direct2_prime butlast_snoc impossible_Cons last_snoc le0 length_pos_if_in_set list.size(3) self_append_conv)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(rule_tac
      t="take (parser_fixed_input_length_recN d2 xa) (xd @ y @ [parser_bottom G2])"
      and s="take (parser_fixed_input_length_recN d2 xa) (xd @ y)"
      in ssubst)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply(rule_tac
      w="xd @ y"
      and v="parser_bottom G2"
      in take_shorter_butlast)
       apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
       prefer 3
       apply(force)
      apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
      apply(force)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply(force)
    apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
    apply(rule butlast_if_match_direct2_prime)
    apply (metis ConsApp butlast_append option.sel append_Nil2 butlast_only_tail_contra butlast_snoc concat_asso ext in_set_takeD kPrefix_append2 kPrefix_def kPrefix_idemp snoc_eq_iff_butlast triv_compl)
   apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
   apply(subgoal_tac "\<exists>w' x'. xb = w' @ [x']")
    apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
   apply(thin_tac "xb = a # list")
   apply(subgoal_tac "c \<in> parserHFS_configurations G2")
    apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
    apply(rule_tac
      t="butlast_if_match (rule_rpush e2) (parser_bottom G2)"
      and s="rule_rpush e2"
      in ssubst)
     apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(simp add: parserHFS_configurations_def)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply(force)
    apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
    apply(rule_tac
      t="butlast_if_match (xd @ rule_rpush e2) (parser_bottom G2)"
      and s="xd @ rule_rpush e2"
      in ssubst)
     apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(simp add: parserHFS_configurations_def)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa e2 w k wb xd w' f h l)(*strict*)
     apply (metis not_set_append)
    apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
    apply(rule_tac
      t="butlast_if_match (take (parser_fixed_input_length_recN d2 xa) (xd @ rule_rpush e2)) (parser_bottom G2)"
      and s="take (parser_fixed_input_length_recN d2 xa) (xd @ rule_rpush e2)"
      in ssubst)
     apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
     apply(rule butlast_if_match_direct2_prime)
     apply(simp add: parserHFS_configurations_def)
     apply(rename_tac xa e2 c w xb y k wb xd)(*strict*)
     apply(clarsimp)
     apply(rename_tac xa e2 w k wb xd w' f h l)(*strict*)
     apply (metis in_set_takeD kPrefix_def not_set_append)
    apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
    apply(force)
   apply(rename_tac xa e2 c w xb y k wb xd a list)(*strict*)
   apply (metis parserHFS.belongs_configurations parserHFS.derivation_initial_belongs)
  apply(rename_tac xa e1 e2 c w xb xba y k wb xd nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(subgoal_tac "max (parser_fixed_input_length_recN d2 xa) (length (kPrefix k (wb @ [parser_bottom G2]))) = parser_fixed_input_length_recN d2 xa")
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(clarsimp)
  apply(thin_tac "max (parser_fixed_input_length_recN d2 xa) (length (kPrefix k (wb @ [parser_bottom G2]))) = parser_fixed_input_length_recN d2 xa")
  apply(rule_tac
      t="kPrefix k (wb @ [parser_bottom G2])"
      and s="xd @ rule_rpush e2"
      in ssubst)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(force)
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(subgoal_tac "length (xd @ rule_rpush e2) - length xd = length (rule_rpush e2)")
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   prefer 2
   apply(simp (no_asm))
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="parser_fixed_input_length_recN d2 xa - (length xd + length (rule_rpush e2))"
      and s="Suc nat"
      in ssubst)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply (metis length_append)
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(subgoal_tac "parser_fixed_input_length_recN d2 xa = Suc nat + length (kPrefix k (wb @ [parser_bottom G2]))")
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="kPrefix k (wb @ [parser_bottom G2])"
      and s="xd @ rule_rpush e2"
      in ssubst)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(force)
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(rule_tac
      t="Suc (nat + length (xd @ rule_rpush e2)) - length xd"
      and s="Suc (nat+length(rule_rpush e2))"
      in ssubst)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(rule_tac
      t="min (length (rule_rpush e2)) (Suc (nat + length (rule_rpush e2)))"
      and s="length (rule_rpush e2)"
      in ssubst)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(rule_tac
      t="min (length xd) (Suc (nat + length (xd @ rule_rpush e2)))"
      and s="length xd"
      in ssubst)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(simp (no_asm))
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(rule_tac
      t="drop (length xd + (length (rule_rpush e2) + min (length xb) (Suc nat))) (butlast_if_match (xd @ rule_rpush e2) (parser_bottom G2))"
      and s="[]"
      in ssubst)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(rule drop_entire_butlast_if_match)
   apply(force)
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(rule_tac
      t="take (Suc (nat + length (xd @ rule_rpush e2))) xd"
      and s="xd"
      in ssubst)
   apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
   apply(rule take_all)
   apply(simp (no_asm))
  apply(rename_tac xa e2 c w xb y k wb xd nat)(*strict*)
  apply(simp (no_asm))
  apply(rule sym, rule butlast_if_match_pull_out)
  apply(force)
  done

corollary parser_S_HFS_relation_coincide: "
  (\<lambda>G1 G2 d1 d2. (valid_parser G1) \<and> (G1=G2) \<and> parserHFS.derivation_initial G2 d2 \<and> (\<exists>n. maximum_of_domain d2 n) \<and> parserHFS_to_parserS_derivation d2 = d1) = (\<lambda>G1 G2 d1 d2. (valid_parser G1) \<and> (G1=G2) \<and> parserS.derivation_initial G1 d1 \<and> (\<exists>n. maximum_of_domain d1 n) \<and> parserS_to_parserHFS_derivation G1 d1 = d2)"
  apply(rule ext)+
  apply(rename_tac G1 G2 d1 d2)(*strict*)
  apply(rule order_antisym)
   apply(rename_tac G1 G2 d1 d2)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 d1 x)(*strict*)
    apply (metis parserS_to_parserHFS_derivation_preserves_derivation_initial)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(rule conjI)
    apply(rename_tac G2 d1 x)(*strict*)
    apply (metis parserS_to_parserHFS_derivation_preserves_maximum_of_domain)
   apply(rename_tac G2 d1 x)(*strict*)
   apply(simp add: parserS_to_parserHFS_derivation_def parserHFS_to_parserS_derivation_def)
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
   apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
  apply(rename_tac G2 d2 x)(*strict*)
  apply(rule conjI)
   apply(rename_tac G2 d2 x)(*strict*)
   apply (metis parserHFS_to_parserS_derivation_preserves_maximum_of_domain)
  apply(rename_tac G2 d2 x)(*strict*)
  apply(rule ext)
  apply(rename_tac G2 d2 x xa)(*strict*)
  apply(rule parser_S_HFS_relation_coincide_hlp)
    apply(rename_tac G2 d2 x xa)(*strict*)
    apply(force)+
  done

lemma parserS_vs_parserHFS_inst_AX_initial_contained1: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>c1. c1 \<in> parserS_initial_configurations G1 \<longrightarrow> (\<exists>c2. parserHFS.derivation_initial G1 (der1 c2) \<and> Ex (maximum_of_domain (der1 c2)) \<and> parserHFS_to_parserS_derivation (der1 c2) = der1 c1)))"
  apply(clarsimp)
  apply(rename_tac G1 c1)(*strict*)
  apply(rule_tac
      x="\<lparr>parserHFS_conf_fixed=[], parserHFS_conf_history=[], parserHFS_conf_stack = parserS_conf_stack c1, parserHFS_conf_scheduler=parserS_conf_scheduler c1\<rparr>"
      in exI)
  apply(rule conjI)
   apply(rename_tac G1 c1)(*strict*)
   apply(simp add: parserHFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 c1)(*strict*)
    apply(rule parserHFS.der1_is_derivation)
   apply(rename_tac G1 c1)(*strict*)
   apply(simp add: der1_def)
   apply(simp add: parserHFS_initial_configurations_def parserHFS_configurations_def parserS_initial_configurations_def parserS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 w)(*strict*)
   apply(simp add: prefix_def)
   apply(simp add: suffix_def)
   apply (metis butlast_if_match_direct2_prime empty_iff list.set(1))
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
  apply(simp add: parserHFS_to_parserS_derivation_def der1_def der1_def)
  done

lemma parserS_vs_parserHFS_inst_AX_initial_contained2: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>c2. c2 \<in> parserHFS_initial_configurations G1 \<longrightarrow> parserHFS.derivation_initial G1 (der1 c2) \<and> Ex (maximum_of_domain (der1 c2)) \<and> (\<exists>c1. parserHFS_to_parserS_derivation (der1 c2) = der1 c1)))"
  apply(clarsimp)
  apply(rename_tac G1 c2)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 c2)(*strict*)
   apply(simp add: parserHFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 c2)(*strict*)
    apply(rule parserHFS.der1_is_derivation)
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
      x="\<lparr>parserS_conf_stack = parserHFS_conf_stack c2, parserS_conf_scheduler=parserHFS_conf_scheduler c2\<rparr>"
      in exI)
  apply(rule ext)
  apply(rename_tac G1 c2 x)(*strict*)
  apply(simp add: parserHFS_to_parserS_derivation_def der1_def der1_def)
  done

lemma parserS_vs_parserHFS_inst_AX_on_derivation_initial1: "
  (\<forall>G1 d1. valid_parser G1 \<and> (\<exists>d2. parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<and> parserHFS_to_parserS_derivation d2 = d1) \<longrightarrow> parserS.derivation_initial G1 d1)"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
  done

lemma parserS_vs_parserHFS_inst_AX_on_finite1: "
  (\<forall>G1 d1. valid_parser G1 \<and> (\<exists>d2. parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<and> parserHFS_to_parserS_derivation d2 = d1) \<longrightarrow> Ex (maximum_of_domain d1))"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(rule_tac
      x="x"
      in exI)
  apply (metis parserHFS_to_parserS_derivation_preserves_maximum_of_domain)
  done

lemma parserS_vs_parserHFS_inst_AX_equal_length: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n1. maximum_of_domain (parserHFS_to_parserS_derivation d2) n1 \<longrightarrow> (\<forall>n2. maximum_of_domain d2 n2 \<longrightarrow> n1 = n2)))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n1 x n2)(*strict*)
  apply (metis parserS.derivation_initial_is_derivation parserS.maximum_of_domainUnique parserHFS_to_parserS_derivation_preserves_derivation_initial parserHFS_to_parserS_derivation_preserves_maximum_of_domain)
  done

lemma parserS_vs_parserHFS_inst_AX_simulate12: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (parserHFS_to_parserS_derivation d2) n \<longrightarrow> maximum_of_domain d2 n \<longrightarrow> (\<forall>e1 c1'. parserS_step_relation G1 (the (get_configuration (parserHFS_to_parserS_derivation d2 n))) e1 c1' \<longrightarrow> (\<exists>c2'. parserHFS_step_relation G1 (the (get_configuration (d2 n))) e1 c2' \<and> e1 \<in> parser_rules G1 \<and> (let d2' = derivation_append d2 (der2 (the (get_configuration (d2 n))) e1 c2') n in parserHFS.derivation_initial G1 d2' \<and> Ex (maximum_of_domain d2') \<and> parserHFS_to_parserS_derivation d2' = derivation_append (parserHFS_to_parserS_derivation d2) (der2 (the (get_configuration (parserHFS_to_parserS_derivation d2 n))) e1 c1') n)))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x e1 c1')(*strict*)
  apply(subgoal_tac "n=x")
   apply(rename_tac G1 d2 n x e1 c1')(*strict*)
   prefer 2
   apply (metis parserS_vs_parserHFS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x e1 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1')(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 x = Some (pair e c)")
   apply(rename_tac G1 d2 x e1 c1')(*strict*)
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x e1 c1')(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x e1 c1')(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x e1 c1')(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x e1 c1')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(subgoal_tac "\<exists>c2'. parserHFS_step_relation G1 (the (get_configuration (d2 x))) e1 c2' \<and> \<lparr>parserS_conf_stack = parserHFS_conf_stack c2', parserS_conf_scheduler = parserHFS_conf_scheduler c2'\<rparr> = c1'")
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
   apply(rule_tac
      x="c2'"
      in exI)
   apply(simp add: Let_def)
   apply(rule conjI)
    apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
    apply(simp add: parserHFS_step_relation_def)
   apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
   apply(rule context_conjI)
    apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
     apply(rule parserHFS.derivation_append_preserves_derivation)
       apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x e1 e c c2')(*strict*)
      apply (metis parserHFS.der2_is_derivation)
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
   apply(simp add: derivation_append_def parserHFS_to_parserS_derivation_def derivation_append_def)
   apply(case_tac "xa \<le> x")
    apply(rename_tac G1 d2 x e1 e c c2' xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 x e1 e c c2' xa)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def der2_def)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(subgoal_tac "parserS_step_relation G1 (the (get_configuration (Some (pair e \<lparr>parserS_conf_stack = parserHFS_conf_stack c, parserS_conf_scheduler = parserHFS_conf_scheduler c\<rparr>)))) e1 c1'")
   apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
   prefer 2
   apply(simp add: parserHFS_to_parserS_derivation_def get_configuration_def)
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(thin_tac "parserS_step_relation G1        (the (case parserHFS_to_parserS_derivation d2 x of None \<Rightarrow> None              | Some (pair e c) \<Rightarrow> Some c))        e1 c1'")
  apply(rename_tac G1 d2 x e1 c1' e c)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c)
  apply(rename_tac G1 d2 x e1 c1' e c parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stacka parserHFS_conf_schedulera)(*strict*)
  apply(rename_tac cf ch cl cr)
  apply(rename_tac G1 d2 x e1 c1' e c cf ch cl cr)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
  apply(subgoal_tac "c1' \<in> parserS_configurations G1")
   apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G1 e1")
    apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
    prefer 2
    apply(simp add: valid_parser_def parserS_step_relation_def)
   apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
   apply(simp add: valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr k w xb)(*strict*)
   apply(rule_tac
      x="\<lparr>parserHFS_conf_fixed = rule_rpush e1 @ drop (length (kPrefix k (w @ [parser_bottom G1]))) cf, parserHFS_conf_history = ch @ drop (length cf) (butlast_if_match (kPrefix k (w @ [parser_bottom G1])) (parser_bottom G1)), parserHFS_conf_stack = parserS_conf_stack c1', parserHFS_conf_scheduler = parserS_conf_scheduler c1'\<rparr>"
      in exI)
   apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr k w xb)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS_step_relation_def parserS_step_relation_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e1 c1' e cf ch k w xb xa xc)(*strict*)
   apply(simp add: parserS_configurations_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x e1 e cf ch k w xb xa xc wa)(*strict*)
   apply(rule_tac
      x="wa"
      in exI)
   apply(force)
  apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
  apply(rule parserS.AX_step_relation_preserves_belongsC)
    apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
  apply(subgoal_tac "\<lparr>parserHFS_conf_fixed = cf, parserHFS_conf_history = ch, parserHFS_conf_stack = cl, parserHFS_conf_scheduler = cr\<rparr> \<in> parserHFS_configurations G1")
   apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
   apply(simp add: parserHFS_configurations_def parserS_configurations_def)
  apply(rename_tac G1 d2 x e1 c1' e cf ch cl cr)(*strict*)
  apply (metis parserHFS.belongs_configurations parserHFS.derivation_initial_belongs)
  done

lemma parserS_vs_parserHFS_inst_AX_simulate21: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (parserHFS_to_parserS_derivation d2) n \<longrightarrow> maximum_of_domain d2 n \<longrightarrow> (\<forall>e2 c2'. parserHFS_step_relation G1 (the (get_configuration (d2 n))) e2 c2' \<longrightarrow> (\<exists>c1'. parserS_step_relation G1 (the (get_configuration (parserHFS_to_parserS_derivation d2 n))) e2 c1' \<and> e2 \<in> parser_rules G1 \<and> (let d2' = derivation_append d2 (der2 (the (get_configuration (d2 n))) e2 c2') n in parserHFS.derivation_initial G1 d2' \<and> Ex (maximum_of_domain d2') \<and> parserHFS_to_parserS_derivation d2' = derivation_append (parserHFS_to_parserS_derivation d2) (der2 (the (get_configuration (parserHFS_to_parserS_derivation d2 n))) e2 c1') n)))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x e2 c2')(*strict*)
  apply(subgoal_tac "n=x")
   apply(rename_tac G1 d2 n x e2 c2')(*strict*)
   prefer 2
   apply (metis parserS_vs_parserHFS_inst_AX_equal_length)
  apply(rename_tac G1 d2 n x e2 c2')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2')(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 x = Some (pair e c)")
   apply(rename_tac G1 d2 x e2 c2')(*strict*)
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 d2 x e2 c2')(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
     apply(force)
    apply(rename_tac G1 d2 x e2 c2')(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x e2 c2')(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x e2 c2')(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule_tac
      x="\<lparr>parserS_conf_stack = parserHFS_conf_stack c2', parserS_conf_scheduler = parserHFS_conf_scheduler c2'\<rparr>"
      in exI)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: parserS_step_relation_def parserHFS_step_relation_def get_configuration_def parserHFS_to_parserS_derivation_def get_configuration_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(simp add: Let_def)
  apply(rule conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: parserHFS_step_relation_def)
  apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
   apply(simp add: parserHFS.derivation_initial_def)
   apply(rule conjI)
    apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
    apply(rule parserHFS.derivation_append_preserves_derivation)
      apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x e2 c2' e c)(*strict*)
     apply (metis parserHFS.der2_is_derivation)
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
  apply(simp add: derivation_append_def parserHFS_to_parserS_derivation_def derivation_append_def)
  apply(case_tac "xa \<le> x")
   apply(rename_tac G1 d2 x e2 c2' e c xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x e2 c2' e c xa)(*strict*)
  apply(clarsimp)
  apply(simp add: der2_def der2_def)
  done

lemma parserS_vs_parserHFS_inst_hlp_bisimulation_compatible_with_crop: "
  valid_parser G1
  \<Longrightarrow> parserHFS.derivation_initial G1 dh
  \<Longrightarrow> maximum_of_domain dh x
  \<Longrightarrow> maximum_of_domain (parserHFS_to_parserS_derivation dh) n
  \<Longrightarrow> derivation_append_fit (parserHFS_to_parserS_derivation dh) dc n
  \<Longrightarrow> parserHFS.derivation_initial G1 dc'
  \<Longrightarrow> parserHFS_to_parserS_derivation dc' = derivation_append (parserHFS_to_parserS_derivation dh) dc n
  \<Longrightarrow> maximum_of_domain dc' xb
  \<Longrightarrow> xa \<le> n
  \<Longrightarrow> dh xa = dc' xa"
  apply(subgoal_tac "x=n")
   apply(subgoal_tac "x\<le>xb")
    apply(clarsimp)
    apply(induct xa)
     apply(clarsimp)
     apply(subgoal_tac "parserHFS_to_parserS_derivation dc' 0 = derivation_append (parserHFS_to_parserS_derivation dh) dc n 0")
      prefer 2
      apply(force)
     apply(thin_tac "parserHFS_to_parserS_derivation dc' = derivation_append (parserHFS_to_parserS_derivation dh) dc n")
     apply(simp add: parserHFS_to_parserS_derivation_def derivation_append_def)
     apply(subgoal_tac "\<exists>c. dc' 0 = Some (pair None c)")
      apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
       apply(clarsimp)
       apply(rename_tac c ca)(*strict*)
       apply(simp add: parserHFS.derivation_initial_def parserS.derivation_initial_def)
       apply(clarsimp)
       apply(simp add: parserHFS_initial_configurations_def)
      apply(clarsimp)
      apply(rename_tac c)(*strict*)
      apply(rule parserHFS.some_position_has_details_at_0)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(rule parserHFS.some_position_has_details_at_0)
     apply(simp add: parserHFS.derivation_initial_def)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parserHFS_to_parserS_derivation dc' xa = derivation_append (parserHFS_to_parserS_derivation dh) dc n xa")
     apply(rename_tac xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(subgoal_tac "parserHFS_to_parserS_derivation dc' (Suc xa) = derivation_append (parserHFS_to_parserS_derivation dh) dc n (Suc xa)")
     apply(rename_tac xa)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(thin_tac "parserHFS_to_parserS_derivation dc' = derivation_append (parserHFS_to_parserS_derivation dh) dc n")
    apply(rename_tac xa)(*strict*)
    apply(subgoal_tac "\<exists>e c. dc' (Suc xa) = Some (pair e c)")
     apply(rename_tac xa)(*strict*)
     apply(subgoal_tac "\<exists>e c. dh (Suc xa) = Some (pair e c)")
      apply(rename_tac xa)(*strict*)
      apply(simp add: parserHFS_to_parserS_derivation_def derivation_append_def)
      apply(clarsimp)
      apply(rename_tac xa ea c ca)(*strict*)
      apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh xa = Some (pair e1 c1) \<and> dh (Suc xa) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G1 c1 e2 c2")
       apply(rename_tac xa ea c ca)(*strict*)
       prefer 2
       apply(rule_tac
      m="Suc xa"
      in parserHFS.step_detail_before_some_position)
         apply(rename_tac xa ea c ca)(*strict*)
         apply(simp add: parserHFS.derivation_initial_def)
        apply(rename_tac xa ea c ca)(*strict*)
        apply(force)
       apply(rename_tac xa ea c ca)(*strict*)
       apply(force)
      apply(rename_tac xa ea c ca)(*strict*)
      apply(clarsimp)
      apply(rename_tac xa c ca e1 e2 c1)(*strict*)
      apply(subgoal_tac "\<exists>e1 e2 c1 c2. dc' xa = Some (pair e1 c1) \<and> dc' (Suc xa) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G1 c1 e2 c2")
       apply(rename_tac xa c ca e1 e2 c1)(*strict*)
       prefer 2
       apply(rule_tac
      m="Suc xa"
      in parserHFS.step_detail_before_some_position)
         apply(rename_tac xa c ca e1 e2 c1)(*strict*)
         apply(simp add: parserHFS.derivation_initial_def)
        apply(rename_tac xa c ca e1 e2 c1)(*strict*)
        apply(force)
       apply(rename_tac xa c ca e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac xa c ca e1 e2 c1)(*strict*)
      apply(clarsimp)
      apply(simp add: parserHFS_step_relation_def)
      apply(clarsimp)
     apply(rename_tac xa)(*strict*)
     apply(rule parserHFS.some_position_has_details_before_max_dom)
       apply(rename_tac xa)(*strict*)
       apply(simp add: parserHFS.derivation_initial_def)
       apply(force)
      apply(rename_tac xa)(*strict*)
      apply(force)
     apply(rename_tac xa)(*strict*)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(rule parserHFS.some_position_has_details_before_max_dom)
      apply(rename_tac xa)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(rename_tac xa)(*strict*)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(rule_tac
      j="n"
      in le_trans)
     apply(rename_tac xa)(*strict*)
     apply(force)
    apply(rename_tac xa)(*strict*)
    apply(force)
   apply(clarsimp)
   apply(rule_tac
      ?d1.0="(parserHFS_to_parserS_derivation dh)"
      and ?d2.0="dc"
      in parserS.derivation_append_minimal_maximum_of_domain)
       apply(force)+
      prefer 4
      apply(force)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(rule_tac
      t="derivation_append (parserHFS_to_parserS_derivation dh) dc n"
      and s="parserHFS_to_parserS_derivation dc'"
      in ssubst)
      apply(force)
     apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rule_tac
      t="derivation_append (parserHFS_to_parserS_derivation dh) dc n"
      and s="parserHFS_to_parserS_derivation dc'"
      in ssubst)
     apply(force)
    apply (metis parserHFS_to_parserS_derivation_preserves_maximum_of_domain)
   apply(force)
  apply (metis parserS_vs_parserHFS_inst_AX_equal_length)
  done

lemma parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_crop1: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>dh. parserHFS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain (parserHFS_to_parserS_derivation dh) n \<longrightarrow> (\<forall>dc. derivation_append_fit (parserHFS_to_parserS_derivation dh) dc n \<longrightarrow> (\<forall>dc'. parserHFS.derivation_initial G1 dc' \<and> Ex (maximum_of_domain dc') \<and> parserHFS_to_parserS_derivation dc' = derivation_append (parserHFS_to_parserS_derivation dh) dc n \<longrightarrow> (\<forall>x\<le>n. dh x = dc' x))))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x dc dc' xa xb)(*strict*)
  apply(rule parserS_vs_parserHFS_inst_hlp_bisimulation_compatible_with_crop)
          apply(rename_tac G1 dh n x dc dc' xa xb)(*strict*)
          apply(force)+
  done

lemma parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_crop2: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>dh. parserHFS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain dh n \<longrightarrow> (\<forall>dc'. derivation_append_fit dh dc' n \<longrightarrow> parserHFS.derivation_initial G1 (derivation_append dh dc' n) \<and> Ex (maximum_of_domain (derivation_append dh dc' n)) \<longrightarrow> (\<forall>x\<le>n. parserHFS_to_parserS_derivation dh x = parserHFS_to_parserS_derivation (derivation_append dh dc' n) x)))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(simp add: parserHFS_to_parserS_derivation_def)
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
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh n dc' xa xb)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh n dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(rule parserHFS.maximum_of_domainUnique)
    apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
    apply(rule parserHFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh n x dc' xa xb)(*strict*)
  apply(force)
  done

lemma parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_unfixed_scheduler_extendable1: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>d2. parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (parserHFS_to_parserS_derivation d2) n \<longrightarrow> (\<forall>m\<le>n. parserS_get_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation d2) m \<sqsupseteq> [parser_bottom G1] \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G1 d2 m \<sqsupseteq> [parser_bottom G1]))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply(subgoal_tac "parserS_get_fixed_scheduler_DB G1 (parserHFS_to_parserS_derivation d2) m = parserHFS_get_fixed_scheduler_DB G1 d2 m")
   apply(rename_tac G1 d2 n x m)(*strict*)
   apply(simp add: parserHFS_get_unfixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
   apply(simp add: parserHFS_get_fixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 n x m c)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d2 m = parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) m")
    apply(rename_tac G1 d2 n x m c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e c. d2 m = Some (pair e c)")
     apply(rename_tac G1 d2 n x m c)(*strict*)
     apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation d2 m = Some (pair e c)")
      apply(rename_tac G1 d2 n x m c)(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
      apply(simp add: get_configuration_def get_configuration_def)
      apply(subgoal_tac "\<exists>c. parserHFS_get_scheduler ca = c @ [parser_bottom G1] \<and> parser_bottom G1 \<notin> set c")
       apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
       apply(erule exE)+
       apply(rename_tac G1 d2 n x m c e ea ca cb cc)(*strict*)
       apply(rule_tac
      x="drop (parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) m) cc"
      in exI)
       apply(clarsimp)
       apply(case_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) m - length cc")
        apply(rename_tac G1 d2 n x m c e ea ca cb cc)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "\<exists>c. parserS_get_scheduler cb = c @ [parser_bottom G1] \<and> parser_bottom G1 \<notin> set c")
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
        apply(erule exE)+
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat "cd")(*strict*)
        apply(clarsimp)
        apply(case_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) m - length cd")
         apply(rename_tac G1 d2 n x m c e ea ca cb cc nat "cd")(*strict*)
         apply(clarsimp)
         apply(rename_tac G1 d2 n x m e ea ca cb cc nat "cd")(*strict*)
         apply (metis append_is_Nil_conv in_set_takeD last_in_set last_snoc not_Cons_self)
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat "cd" nata)(*strict*)
        apply(clarsimp)
       apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
       apply(subgoal_tac "cb \<in> parserS_configurations G1")
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
        apply(simp add: parserS_configurations_def parserS_get_scheduler_def)
        apply(clarsimp)
       apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
       apply(rule_tac
      d="parserHFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
        apply(rule parserS.derivation_initial_belongs)
         apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
         apply(force)
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
        apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
       apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
      apply(subgoal_tac "ca \<in> parserHFS_configurations G1")
       apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
       apply(simp add: parserHFS_configurations_def parserHFS_get_scheduler_def)
       apply(clarsimp)
      apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
      apply(rule_tac
      d="d2"
      in parserHFS.belongs_configurations)
       apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
       apply(rule parserHFS.derivation_initial_belongs)
        apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 n x m c)(*strict*)
     apply(simp add: parserHFS_to_parserS_derivation_def)
     apply(clarsimp)
    apply(rename_tac G1 d2 n x m c)(*strict*)
    apply(rule_tac
      M="G1"
      in parserHFS.some_position_has_details_before_max_dom)
      apply(rename_tac G1 d2 n x m c)(*strict*)
      apply (metis parserHFS.derivation_initial_is_derivation)
     apply(rename_tac G1 d2 n x m c)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 n x m c)(*strict*)
    apply(subgoal_tac "n=x")
     apply(rename_tac G1 d2 n x m c)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 n x m c)(*strict*)
    apply (metis parserS_vs_parserHFS_inst_AX_equal_length)
   apply(rename_tac G1 d2 n x m c)(*strict*)
   apply (metis parserHFS.derivation_initial_is_derivation parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply(rule sym)
  apply(rule parserHFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB)
    apply(rename_tac G1 d2 n x m)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 n x m)(*strict*)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply (metis parserHFS.allPreMaxDomSome parserHFS.derivation_initial_is_derivation parserS_vs_parserHFS_inst_AX_equal_length)
  done

lemma parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_unfixed_scheduler_extendable2: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>d2. parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>n. maximum_of_domain (parserHFS_to_parserS_derivation d2) n \<longrightarrow> (\<forall>m\<le>n. parserHFS_get_unfixed_scheduler_DB G1 d2 m \<sqsupseteq> [parser_bottom G1] \<longrightarrow> parserS_get_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation d2) m \<sqsupseteq> [parser_bottom G1]))))"
  apply(clarsimp)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply(subgoal_tac "parserS_get_fixed_scheduler_DB G1 (parserHFS_to_parserS_derivation d2) m = parserHFS_get_fixed_scheduler_DB G1 d2 m")
   apply(rename_tac G1 d2 n x m)(*strict*)
   apply(simp add: parserHFS_get_unfixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
   apply(simp add: parserHFS_get_fixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def)
   apply(simp add: suffix_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 n x m c)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d2 m = parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) m")
    apply(rename_tac G1 d2 n x m c)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e c. d2 m = Some (pair e c)")
     apply(rename_tac G1 d2 n x m c)(*strict*)
     apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation d2 m = Some (pair e c)")
      apply(rename_tac G1 d2 n x m c)(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
      apply(simp add: get_configuration_def get_configuration_def)
      apply(subgoal_tac "\<exists>c. parserS_get_scheduler cb = c @ [parser_bottom G1] \<and> parser_bottom G1 \<notin> set c")
       apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
       apply(erule exE)+
       apply(rename_tac G1 d2 n x m c e ea ca cb cc)(*strict*)
       apply(rule_tac
      x="drop (parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) m) cc"
      in exI)
       apply(clarsimp)
       apply(case_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) m - length cc")
        apply(rename_tac G1 d2 n x m c e ea ca cb cc)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
       apply(clarsimp)
       apply(subgoal_tac "\<exists>c. parserHFS_get_scheduler ca = c @ [parser_bottom G1] \<and> parser_bottom G1 \<notin> set c")
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
        apply(erule exE)+
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat "cd")(*strict*)
        apply(clarsimp)
        apply(case_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) m - length cd")
         apply(rename_tac G1 d2 n x m c e ea ca cb cc nat "cd")(*strict*)
         apply(clarsimp)
         apply(rename_tac G1 d2 n x m e ea ca cb cc nat "cd")(*strict*)
         apply (metis append_is_Nil_conv in_set_takeD last_in_set last_snoc not_Cons_self)
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat "cd" nata)(*strict*)
        apply(clarsimp)
       apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
       apply(subgoal_tac "ca \<in> parserHFS_configurations G1")
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
        apply(simp add: parserHFS_configurations_def parserHFS_get_scheduler_def)
        apply(clarsimp)
       apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
       apply(rule_tac
      d="d2"
      in parserHFS.belongs_configurations)
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
        apply(rule parserHFS.derivation_initial_belongs)
         apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
         apply(force)
        apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 n x m c e ea ca cb cc nat)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
      apply(subgoal_tac "cb \<in> parserS_configurations G1")
       apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
       apply(simp add: parserS_configurations_def parserS_get_scheduler_def)
       apply(clarsimp)
      apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
      apply(rule_tac
      d="parserHFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
       apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
       apply(rule parserS.derivation_initial_belongs)
        apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac G1 d2 n x m c e ea ca cb)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 n x m c)(*strict*)
     apply(simp add: parserHFS_to_parserS_derivation_def)
     apply(clarsimp)
    apply(rename_tac G1 d2 n x m c)(*strict*)
    apply(rule_tac
      M="G1"
      in parserHFS.some_position_has_details_before_max_dom)
      apply(rename_tac G1 d2 n x m c)(*strict*)
      apply (metis parserHFS.derivation_initial_is_derivation)
     apply(rename_tac G1 d2 n x m c)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 n x m c)(*strict*)
    apply(subgoal_tac "n=x")
     apply(rename_tac G1 d2 n x m c)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 n x m c)(*strict*)
    apply (metis parserS_vs_parserHFS_inst_AX_equal_length)
   apply(rename_tac G1 d2 n x m c)(*strict*)
   apply (metis parserHFS.derivation_initial_is_derivation parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply(rule sym)
  apply(rule parserHFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB)
    apply(rename_tac G1 d2 n x m)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 n x m)(*strict*)
   apply (metis parserHFS.derivation_initial_is_derivation)
  apply(rename_tac G1 d2 n x m)(*strict*)
  apply (metis parserHFS.allPreMaxDomSome parserHFS.derivation_initial_is_derivation parserS_vs_parserHFS_inst_AX_equal_length)
  done

lemma parserS_vs_parserHFS_inst_AX_accept_id1: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> parserS_marking_condition G1 (parserHFS_to_parserS_derivation d2) \<longrightarrow> parserHFS_marking_condition G1 d2)"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: parserHFS_to_parserS_derivation_def)
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
  apply(simp add: parserHFS_marking_condition_def)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="cb"
      in exI)
  apply(rule context_conjI)
   apply(rename_tac G1 d2 x c i e ca ea cb)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x c i e ca ea cb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i ca ea cb)(*strict*)
  apply(simp add: parserHFS_marking_configurations_def parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
   apply(rule_tac
      x="f"
      in bexI)
    apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
    apply(rule_tac
      x="w"
      in exI)
    apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(force)
   apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
  apply(rule parserHFS.belongs_configurations)
   apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
   apply(rule parserHFS.derivation_initial_belongs)
    apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c i ca ea cb f w)(*strict*)
  apply(force)
  done

lemma parserS_vs_parserHFS_inst_AX_accept_id2: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> parserHFS_marking_condition G1 d2 \<longrightarrow> parserS_marking_condition G1 (parserHFS_to_parserS_derivation d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 x)(*strict*)
  apply(simp add: parserHFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(rule conjI)
   apply(rename_tac G1 d2 x i e c)(*strict*)
   apply(subgoal_tac "\<exists>c. parserHFS_to_parserS_derivation d2 0 = Some (pair None c)")
    apply(rename_tac G1 d2 x i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 x i e c ca)(*strict*)
    apply(rule_tac
      d="parserHFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
     apply(rename_tac G1 d2 x i e c ca)(*strict*)
     apply(rule parserS.derivation_initial_belongs)
      apply(rename_tac G1 d2 x i e c ca)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x i e c ca)(*strict*)
     apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac G1 d2 x i e c ca)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c)(*strict*)
   apply(rule_tac
      M="G1"
      in parserS.some_position_has_details_at_0)
   apply(rule_tac parserS.derivation_initial_is_derivation)
   apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x i e c)(*strict*)
   prefer 2
   apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ea ca)(*strict*)
  apply(simp add: parserHFS_marking_configurations_def parserS_marking_configurations_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
   apply(rule_tac
      x="f"
      in bexI)
    apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
    apply(rule_tac
      x="w"
      in exI)
    apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(clarsimp)
   apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
  apply(rule conjI)
   apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
  apply(rule_tac
      d="parserHFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
   apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
   apply(rule parserS.derivation_initial_belongs)
    apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
   apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
  apply(rename_tac G1 d2 x i e c ea ca f w)(*strict*)
  apply(force)
  done

lemma parserHFS_to_parserS_derivation_reflects_string_state_delta: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> parserS_string_state ci' = w @ parserS_string_state cj'
  \<Longrightarrow> (parserHFS_to_parserS_derivation d) i = Some (pair ei ci')
  \<Longrightarrow> (parserHFS_to_parserS_derivation d) j = Some (pair ej cj')
  \<Longrightarrow> parserHFS_string_state ci = w @ parserHFS_string_state cj"
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac x ej cj cj' w nat)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
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
   apply(subgoal_tac "\<exists>e c. (parserHFS_to_parserS_derivation d) nat = Some (pair e c)")
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
    apply(subgoal_tac "\<exists>w. parserHFS_string_state c1 = w @ parserHFS_string_state cj")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     prefer 2
     apply(rule_tac
      j="Suc 0"
      in parserHFS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(rule parserHFS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
       apply(rule parserHFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(subgoal_tac "\<exists>w. parserHFS_string_state ci = w @ parserHFS_string_state c1")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     prefer 2
     apply(rule_tac
      j="nat-i"
      in parserHFS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(rule parserHFS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
       apply(rule parserHFS.derivation_initial_is_derivation)
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
      d="parserHFS_to_parserS_derivation d"
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
        apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
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
      d="parserHFS_to_parserS_derivation d"
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
        apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa wb wc)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
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
     apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb wc wd)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. parserHFS_to_parserS_derivation d nat = Some (pair e1 c1) \<and> parserHFS_to_parserS_derivation d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
       apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd)(*strict*)
    apply(clarsimp)
    apply(simp add: parserS_string_state_def parserHFS_string_state_def parserS_step_relation_def parserHFS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wc wd xa xb xc xd y)(*strict*)
    apply (metis append_injr)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(rule_tac
      m="Suc nat"
      in parserHFS.pre_some_position_is_some_position)
    apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
    apply(rule parserHFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(force)
  done

lemma parserHFS_to_parserS_derivation_preserves_string_state_delta: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> parserHFS_string_state ci = w @ parserHFS_string_state cj
  \<Longrightarrow> (parserHFS_to_parserS_derivation d) i = Some (pair ei ci')
  \<Longrightarrow> (parserHFS_to_parserS_derivation d) j = Some (pair ej cj')
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
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d nat = Some (pair e1 c1) \<and> d (Suc nat) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac x ej cj cj' w nat)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc nat"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac x ej cj cj' w nat)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
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
   apply(subgoal_tac "\<exists>e c. (parserHFS_to_parserS_derivation d) nat = Some (pair e c)")
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
    apply(subgoal_tac "\<exists>w. parserHFS_string_state c1 = w @ parserHFS_string_state cj")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     prefer 2
     apply(rule_tac
      j="Suc 0"
      in parserHFS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(rule parserHFS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
       apply(rule parserHFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
    apply(subgoal_tac "\<exists>w. parserHFS_string_state ci = w @ parserHFS_string_state c1")
     apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
     prefer 2
     apply(rule_tac
      j="nat-i"
      in parserHFS.derivation_monotonically_dec)
          apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
          apply(force)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(rule parserHFS.derivation_initial_belongs)
         apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
         apply(force)
        apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
        apply(force)
       apply(rename_tac x cj cj' w nat e1 e2 c1 e c wa)(*strict*)
       apply(rule parserHFS.derivation_initial_is_derivation)
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
     apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(erule meta_impE)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>e1 e2 c1 c2. parserHFS_to_parserS_derivation d nat = Some (pair e1 c1) \<and> parserHFS_to_parserS_derivation d (Suc nat) = Some (pair (Some e2) c2) \<and> parserS_step_relation G c1 e2 c2")
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc nat"
      in parserS.step_detail_before_some_position)
       apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
      apply(force)
     apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
     apply(force)
    apply(rename_tac x cj cj' nat e1 e2 c1 e c wa wb)(*strict*)
    apply(clarsimp)
    apply(simp add: parserS_string_state_def parserHFS_string_state_def parserS_step_relation_def parserHFS_step_relation_def)
    apply(clarsimp)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(rule_tac
      m="Suc nat"
      in parserHFS.pre_some_position_is_some_position)
    apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
    apply(rule parserHFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac x cj cj' w nat e1 e2 c1)(*strict*)
  apply(force)
  done

lemma parserHFS_history_equals_removed_append_overhead: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G d
  \<Longrightarrow> d 0 = Some (pair None c0)
  \<Longrightarrow> d n = Some (pair e cn)
  \<Longrightarrow> parserHFS_conf_scheduler c0 = w@parserHFS_conf_scheduler cn
  \<Longrightarrow> w @ butlast_if_match (take (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler cn)) (parser_bottom G) = parserHFS_conf_history cn"
  apply(induct n arbitrary: e cn w)
   apply(rename_tac e cn w)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS.derivation_initial_def)
   apply(simp add: parserHFS_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: butlast_if_match_def)
  apply(rename_tac n e cn w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac n e cn w)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac n e cn w)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac n e cn w)(*strict*)
    apply(force)
   apply(rename_tac n e cn w)(*strict*)
   apply(force)
  apply(rename_tac n e cn w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cn w e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state c1 = w @ parserHFS_string_state cn")
   apply(rename_tac n cn w e1 e2 c1)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and j="Suc 0"
      in parserHFS.derivation_monotonically_dec)
        apply(rename_tac n cn w e1 e2 c1)(*strict*)
        apply(force)
       apply(rename_tac n cn w e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac n cn w e1 e2 c1)(*strict*)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(rename_tac n cn w e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac n cn w e1 e2 c1)(*strict*)
      apply(force)
     apply(rename_tac n cn w e1 e2 c1)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac n cn w e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac n cn w e1 e2 c1)(*strict*)
   apply(force)
  apply(rename_tac n cn w e1 e2 c1)(*strict*)
  apply(simp add: parserHFS_string_state_def)
  apply(clarsimp)
  apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state c0 = w @ parserHFS_string_state c1")
   apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
   prefer 2
   apply(rule_tac
      d="d"
      and j="n"
      in parserHFS.derivation_monotonically_dec)
        apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
        apply(force)
       apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
       apply(force)
      apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
       apply(force)
      apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
      apply(force)
     apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
    apply(force)
   apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
   apply(force)
  apply(rename_tac n cn w e1 e2 c1 wa)(*strict*)
  apply(simp add: parserHFS_string_state_def)
  apply(clarsimp)
  apply(rename_tac n cn e1 e2 c1 wa wb)(*strict*)
  apply(erule_tac
      x="wb"
      in meta_allE)
  apply(clarsimp)
  apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac n cn e1 e2 c1 wa wb)(*strict*)
   prefer 2
   apply(simp add: valid_parser_def)
  apply(rename_tac n cn e1 e2 c1 wa wb)(*strict*)
  apply(clarsimp)
  apply(rename_tac n cn e1 e2 c1 wa wb x xa y)(*strict*)
  apply(simp add: valid_parser_step_label_def prefix_def suffix_def)
  apply(clarsimp)
  apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
  apply(rule_tac
      t="parserHFS_conf_history c1"
      and s="wb @ butlast_if_match (take (parser_fixed_input_length_recN d n) wa @ take (parser_fixed_input_length_recN d n - length wa) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length wa + length (rule_rpush e2))) xa) (parser_bottom G)"
      in ssubst)
   apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
   apply(force)
  apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
  apply(thin_tac "wb @ butlast_if_match (take (parser_fixed_input_length_recN d n) wa @ take (parser_fixed_input_length_recN d n - length wa) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length wa + length (rule_rpush e2))) xa) (parser_bottom G) = parserHFS_conf_history c1")
  apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "c1 \<in> parserHFS_configurations G")
   apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
   apply(subgoal_tac "cn \<in> parserHFS_configurations G")
    apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
    apply(subgoal_tac "wa=xc")
     apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
     prefer 2
     apply (metis append_injr)
    apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
    apply(clarsimp)
    apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
    apply(subgoal_tac "length (parserHFS_conf_fixed c1) = parser_fixed_input_length_recN d n")
     apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
     apply(case_tac "(parser_fixed_input_length_recN d n) - (length (kPrefix k (w @ [parser_bottom G])))=0")
      apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      t="max (parser_fixed_input_length_recN d n) (length (kPrefix k (w @ [parser_bottom G])))"
      and s="(length (kPrefix k (w @ [parser_bottom G])))"
      in ssubst)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(force)
      apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      t="(length (kPrefix k (w @ [parser_bottom G])) - (length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2)))"
      and s="length (rule_rpush e2)"
      in ssubst)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply (metis diff_diff_cancel drop_length_append drop_prefix_closureise length_drop)
      apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
      apply(clarsimp)
      apply(case_tac xa)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(clarsimp)
       apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
       apply(rule_tac
      t="butlast_if_match (kPrefix k (w @ [parser_bottom G])) (parser_bottom G)"
      and s="xc@y"
      in ssubst)
        apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
        prefer 2
        apply(clarsimp)
        apply(rule_tac
      t="butlast_if_match (take (parser_fixed_input_length_recN d n) xc @ take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2)) (parser_bottom G)"
      and s=" (take (parser_fixed_input_length_recN d n) xc @ take (parser_fixed_input_length_recN d n - length xc) y) "
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
         defer
         apply(clarsimp)
         apply(rule_tac
      t="butlast_if_match (rule_rpush e2) (parser_bottom G)"
      and s="y"
      in ssubst)
          apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
          defer
          apply (metis List.drop_append append_assoc append_take_drop_id_hlp take_append)
         apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
         apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc @ rule_rpush e2"
      in ssubst)
          apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
          apply(force)
         apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
         apply(rule_tac
      t="rule_rpush e2"
      and s="y@[parser_bottom G]"
      in ssubst)
          apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
          apply(force)
         apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
         apply(rule butlast_if_match_direct)
         apply(force)
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc a list)(*strict*)
        apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
         apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc a list)(*strict*)
         prefer 2
         apply(rule NonEmptyListHasTailElem)
         apply(force)
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc a list)(*strict*)
        apply(thin_tac "xa = a # list")
        apply(clarsimp)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(simp add: kPrefix_def)
        apply(case_tac "k-length w")
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         prefer 2
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w' nat)(*strict*)
         apply(subgoal_tac "False")
          apply(rename_tac n cn e1 e2 c1 wb x k w xc w' nat)(*strict*)
          apply(clarsimp)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w' nat)(*strict*)
         apply(simp add: parserHFS_configurations_def prefix_def suffix_def)
         apply(clarsimp)
         apply(rename_tac n e1 e2 wb x k w xc w' nat xa f c cb cc)(*strict*)
         apply(subgoal_tac "parser_bottom G \<in> set(rule_rpush e2)")
          apply(rename_tac n e1 e2 wb x k w xc w' nat xa f c cb cc)(*strict*)
          apply(force)
         apply(rename_tac n e1 e2 wb x k w xc w' nat xa f c cb cc)(*strict*)
         apply (metis Nil_is_append_conv last_in_set last_snoc not_Cons_self)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(clarsimp)
        apply(subgoal_tac "butlast_if_match (take k w) (parser_bottom G) = take k w")
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         prefer 2
         apply(rule butlast_if_match_direct2_prime)
         apply (metis in_set_takeD kPrefix_def not_in_diff)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(clarsimp)
        apply(rule_tac
      t="butlast_if_match (rule_rpush e2) (parser_bottom G)"
      and s="rule_rpush e2"
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply(rule butlast_if_match_direct2_prime)
         apply (metis in_set_takeD kPrefix_def not_in_diff set_append_contra2)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(rule_tac
      t="butlast_if_match (take (parser_fixed_input_length_recN d n) xc @ take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2))) w' @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2) + length w')) [parser_bottom G]) (parser_bottom G)"
      and s="take (parser_fixed_input_length_recN d n) (take k w)"
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         prefer 2
         apply (metis append_take_drop_id_hlp kPrefix_def)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(rule_tac
      t="butlast_if_match (take (parser_fixed_input_length_recN d n) xc @ take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2))) w' @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2) + length w')) [parser_bottom G]) (parser_bottom G)"
      and s=" (take (parser_fixed_input_length_recN d n) xc @ take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2))) w')"
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply(case_tac "parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2) + length w')")
          apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
          apply(clarsimp)
          apply(rule butlast_if_match_direct2_prime)
          apply(clarsimp)
          apply(rule conjI)
           apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
           apply (metis in_set_takeD takePrecise triv_compl)
          apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
          apply(rule conjI)
           apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
           apply (metis kPrefix_def set_append2 set_take_subset subsetE subset_trans triv_compl)
          apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
          apply (metis diff_is_0_eq' empty_iff empty_set length_append take_0 take_all_length)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w' nat)(*strict*)
         apply(clarsimp)
         apply(rule butlast_if_match_direct)
         apply(force)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(rule_tac
      t="take k w"
      and s="xc@(rule_rpush e2)"
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply(force)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(subgoal_tac "parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2)) = 0")
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply (metis append_Nil2 length_append take_0 take_append)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(clarsimp)
        apply (metis kPrefix_def length_append take_all_length)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(clarsimp)
       apply(rule_tac
      t="max (parser_fixed_input_length_recN d n) (length (kPrefix k (w @ [parser_bottom G])))"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
        apply(force)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(rule_tac
      t="length (kPrefix k (w @ [parser_bottom G])) - length (rule_rpush e2)"
      and s="length xc"
      in ssubst)
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
        apply (metis diff_diff_cancel drop_length_append drop_prefix_closureise length_drop)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(subgoal_tac "drop (parser_fixed_input_length_recN d n) (butlast_if_match (kPrefix k (w @ [parser_bottom G])) (parser_bottom G)) = []")
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
        prefer 2
        apply(clarsimp)
        apply (metis butlast_if_match_length_le le_trans nat_le_linear)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(clarsimp)
       apply(rule_tac
      t="take (parser_fixed_input_length_recN d n) xc"
      and s="xc"
      in ssubst)
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
        apply(rule take_all)
        apply (metis drop_length_append le_trans nat_le_linear)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(case_tac "xa")
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
        apply(clarsimp)
        apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
        apply(rule_tac
      t="butlast_if_match (take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2)) (parser_bottom G)"
      and s="(take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2))"
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
         apply(rule butlast_if_match_direct2_prime)
         apply (metis dropPrecise drop_eq_Nil kPrefix_def length_Suc parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler parserHFS_get_scheduler_def take_max_no_append)
        apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
        apply(rule_tac
      t="butlast_if_match (xc @ take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2)) (parser_bottom G)"
      and s="(xc @ take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2)) "
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
         apply(rule butlast_if_match_direct2_prime)
         apply (metis dropPrecise drop_eq_Nil kPrefix_def length_Suc parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler parserHFS_get_scheduler_def take_max_no_append)
        apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
        apply(force)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc a list)(*strict*)
       apply(subgoal_tac "\<exists>w' x'. xa = w' @ [x']")
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc a list)(*strict*)
        prefer 2
        apply(rule NonEmptyListHasTailElem)
        apply(force)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc a list)(*strict*)
       apply(thin_tac "xa = a # list")
       apply(clarsimp)
       apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
       apply(case_tac "parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2) + length w')")
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(clarsimp)
        apply(rule_tac
      t="butlast_if_match (take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2))) w') (parser_bottom G)"
      and s="take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2))) w'"
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply(rule butlast_if_match_direct2_prime)
         apply(clarsimp)
         apply(rule conjI)
          apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
          apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
          apply(clarsimp)
          apply(rename_tac n e1 e2 wb x k w xc w' f h)(*strict*)
          apply (metis in_set_takeD kPrefix_def length_drop)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
         apply(clarsimp)
         apply(rename_tac n e1 e2 wb x k w xc w' f h)(*strict*)
         apply (metis in_set_takeD kPrefix_def length_drop)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(rule_tac
      t="butlast_if_match (xc @ take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2))) w') (parser_bottom G)"
      and s="xc @ take (parser_fixed_input_length_recN d n - length xc) (rule_rpush e2) @ take (parser_fixed_input_length_recN d n - (length xc + length (rule_rpush e2))) w'"
      in ssubst)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply(rule butlast_if_match_direct2_prime)
         apply(clarsimp)
         apply(rule conjI)
          apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
          apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
          apply(clarsimp)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply(rule conjI)
          apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
          apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
          apply(clarsimp)
          apply(rename_tac n e1 e2 wb x k w xc w' f h)(*strict*)
          apply (metis in_set_takeD kPrefix_def length_drop)
         apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
         apply(simp add: parserHFS_step_relation_def parserHFS_configurations_def)
         apply(clarsimp)
         apply(rename_tac n e1 e2 wb x k w xc w' f h)(*strict*)
         apply (metis in_set_takeD kPrefix_def length_drop)
        apply(rename_tac n cn e1 e2 c1 wb x k w xc w')(*strict*)
        apply(force)
       apply(rename_tac n cn e1 e2 c1 wb x k w xc w' nat)(*strict*)
       apply(clarsimp)
       apply (metis Suc_length Suc_neq_Zero append_is_Nil_conv butlast_if_match_pull_out list.size(3))
      apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
      apply(subgoal_tac "take (parser_fixed_input_length_recN d n) (parserHFS_conf_scheduler c1) = parserHFS_conf_fixed c1")
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       prefer 2
       apply(rule parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler)
         apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
         apply(force)
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
        apply(force)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(force)
      apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
      apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserHFS_conf_scheduler c1)")
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply (metis kPrefix_def take_all_length)
      apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
      apply(rule parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
         apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
         apply(force)
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
        apply(rule parserHFS.derivation_initial_belongs)
         apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
         apply(force)
        apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
        apply(force)
       apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
       apply(simp add: parserHFS.derivation_initial_def)
      apply(rename_tac n cn e1 e2 c1 wb x xa y k w xc)(*strict*)
      apply(force)
     apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
     apply(rule parserHFS.belongs_configurations)
      apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
       apply(force)
      apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
      apply(force)
     apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
     apply(force)
    apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
    apply(rule parserHFS.belongs_configurations)
     apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
     apply(rule parserHFS.derivation_initial_belongs)
      apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
      apply(force)
     apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
     apply(force)
    apply(rename_tac n cn e1 e2 c1 wa wb x xa y k w xc)(*strict*)
    apply(force)
   apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
   apply(rule_tac
      t="rule_rpush e2"
      and s="y@[parser_bottom G]"
      in ssubst)
    apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
    apply(force)
   apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
   apply(simp (no_asm))
   apply(case_tac "parser_fixed_input_length_recN d n - (length xc + length y)")
    apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
    apply(clarsimp)
    apply(rule butlast_if_match_direct2_prime)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
     apply (metis append_is_Nil_conv butlast_if_match_direct butlast_if_match_pull_out kPrefix_def length_Suc list.simps(3) not_less_eq_eq set_append1 set_take_subset subsetE take_all take_append2 triv_compl)
    apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
    apply(simp add: kPrefix_def)
    apply(clarsimp)
    apply(case_tac "k - length w")
     apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "parser_bottom G \<in> set w")
      apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
      apply(subgoal_tac "parser_bottom G \<notin> set w")
       apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
       apply(force)
      apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
      apply(force)
     apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
     apply (metis elem_set_app in_set_takeD set_append2 set_subset_in)
    apply(rename_tac n cn e1 e2 c1 wb x y k w xc nat)(*strict*)
    apply(clarsimp)
    apply(rename_tac n cn e1 e2 c1 wb x y k w xc nat xa)(*strict*)
    apply(subgoal_tac "y=xa")
     apply(rename_tac n cn e1 e2 c1 wb x y k w xc nat xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac n cn e1 e2 c1 wb x k w xc nat xa)(*strict*)
     apply (metis Nil_is_append_conv butlast_if_match_direct butlast_if_match_pull_out kPrefix_def list.simps(2) not_in_diff set_append2 set_take_subset subsetE)
    apply(rename_tac n cn e1 e2 c1 wb x y k w xc nat xa)(*strict*)
    apply (metis append_injr)
   apply(rename_tac n cn e1 e2 c1 wb x y k w xc nat)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="kPrefix k (w @ [parser_bottom G])"
      and s="xc@y@[parser_bottom G]"
      in ssubst)
    apply(rename_tac n cn e1 e2 c1 wb x y k w xc nat)(*strict*)
    apply(force)
   apply(rename_tac n cn e1 e2 c1 wb x y k w xc nat)(*strict*)
   apply(rule butlast_if_match_direct)
   apply(force)
  apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
  apply(rule_tac
      t="rule_rpush e2"
      and s="y@[parser_bottom G]"
      in ssubst)
   apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
   apply(force)
  apply(rename_tac n cn e1 e2 c1 wb x y k w xc)(*strict*)
  apply(rule butlast_if_match_direct)
  apply(force)
  done

lemma parserHFS_parserS_schedUF_db_decreases: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> \<exists>w. parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation d) i = w @ (parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation d) j)"
  apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation d i = Some (pair e c)")
   apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation d j = Some (pair e c)")
    apply(clarsimp)
    apply(rename_tac e ea c ca)(*strict*)
    apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation d) i"
      and s="drop (parser_fixed_input_length_recN d i) (parserS_conf_scheduler c)"
      in ssubst)
     apply(rename_tac e ea c ca)(*strict*)
     apply(simp add: parserS_get_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
     apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d) i"
      and s="parser_fixed_input_length_recN d i"
      in subst)
      apply(rename_tac e ea c ca)(*strict*)
      apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca)(*strict*)
    apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation d) j"
      and s="drop (parser_fixed_input_length_recN d j) (parserS_conf_scheduler ca)"
      in ssubst)
     apply(rename_tac e ea c ca)(*strict*)
     apply(simp add: parserS_get_unfixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def)
     apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d) j"
      and s="parser_fixed_input_length_recN d j"
      in subst)
      apply(rename_tac e ea c ca)(*strict*)
      apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac e ea c ca)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca)(*strict*)
    apply(subgoal_tac "length (parserS_conf_scheduler c) - (parser_fixed_input_length_recN d i) \<ge> length (parserS_conf_scheduler ca) - (parser_fixed_input_length_recN d (i+(j-i)))")
     apply(rename_tac e ea c ca)(*strict*)
     prefer 2
     apply(rule_tac
      t="parser_fixed_input_length_recN d (i + (j - i))"
      and s="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d) (i + (j - i))"
      in ssubst)
      apply(rename_tac e ea c ca)(*strict*)
      apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac e ea c ca)(*strict*)
     apply(rule_tac
      t="parser_fixed_input_length_recN d i"
      and s="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d) i"
      in ssubst)
      apply(rename_tac e ea c ca)(*strict*)
      apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
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
        apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
       apply(rename_tac e ea c ca)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
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
      and d="parserHFS_to_parserS_derivation d"
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
        apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
       apply(rename_tac e ea c ca)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
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
      and s="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d) i"
      in ssubst)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
       apply(rename_tac e ea c ca w)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac e ea c ca w)(*strict*)
        apply(force)
       apply(rename_tac e ea c ca w)(*strict*)
       apply(rule parserS.derivation_initial_belongs)
        apply(rename_tac e ea c ca w)(*strict*)
        apply(force)
       apply(rename_tac e ea c ca w)(*strict*)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(rule parserS.derivation_initial_is_derivation)
      apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(force)
    apply(rename_tac e ea c ca w)(*strict*)
    apply(rule_tac
      t="parser_fixed_input_length_recN d j"
      and s="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d) j"
      in ssubst)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(force)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac e ea c ca w)(*strict*)
    apply(rule PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac e ea c ca w)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca w)(*strict*)
      apply(rule parserS.derivation_initial_belongs)
       apply(rename_tac e ea c ca w)(*strict*)
       apply(force)
      apply(rename_tac e ea c ca w)(*strict*)
      apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac e ea c ca w)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac e ea c ca w)(*strict*)
    apply(force)
   apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(simp add: parserHFS_to_parserS_derivation_def)
  done

lemma parser_S_HFS_replace_unfixed_scheduler_DB_preserves_parser_fixed_input_length_recN: "
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

lemma parserHFS_double_funct_mod_vs_mod: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> xa \<le> n
  \<Longrightarrow> parserHFS.derivation_initial G dh
  \<Longrightarrow> parserS_to_parserHFS_derivation G (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) xa = parserHFS.replace_unfixed_scheduler_DB G dh sUF n xa"
  apply(simp only: parserS_to_parserHFS_derivation_def)
  apply(simp add: parserS.replace_unfixed_scheduler_DB_def)
  apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def)
  apply(simp add: parserS.map_unfixed_scheduler_DB_def)
  apply(simp add: parserHFS.map_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(simp add: parserHFS.derivation_initial_def)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac e c)(*strict*)
  apply(subgoal_tac "\<exists>c. parserHFS_to_parserS_derivation dh xa = Some (pair e c)")
   apply(rename_tac e c)(*strict*)
   prefer 2
   apply(rule parserHFS_to_parserS_derivation_preserves_step_labels)
     apply(rename_tac e c)(*strict*)
     apply(force)
    apply(rename_tac e c)(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
   apply(rename_tac e c)(*strict*)
   apply(force)
  apply(rename_tac e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac e c ca)(*strict*)
  apply(simp add: parserHFS_set_unfixed_scheduler_DB_def get_configuration_def)
  apply(case_tac c)
  apply(rename_tac e c ca parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
  apply(clarsimp)
  apply(rename_tac e ca parserHFS_conf_fixed parserHFS_conf_history parserHFS_conf_stack parserHFS_conf_scheduler)(*strict*)
  apply(rename_tac f h l r)
  apply(rename_tac e ca f h l r)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) sUF n) xa"
      and s="parser_fixed_input_length_recN dh xa"
      in ssubst)
   apply(rename_tac e ca f h l r)(*strict*)
   defer
   apply(subgoal_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) xa = parser_fixed_input_length_recN dh xa")
    apply(rename_tac e ca f h l r)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
     apply(rename_tac e ca f h l r)(*strict*)
     apply(force)
    apply(rename_tac e ca f h l r)(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
   apply(rename_tac e ca f h l r)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) n = parser_fixed_input_length_recN dh n")
    apply(rename_tac e ca f h l r)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
     apply(rename_tac e ca f h l r)(*strict*)
     apply(force)
    apply(rename_tac e ca f h l r)(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
   apply(rename_tac e ca f h l r)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN dh xa \<le> length r")
    apply(rename_tac e ca f h l r)(*strict*)
    prefer 2
    apply(subgoal_tac "parser_fixed_input_length_recN dh xa \<le> length (parserHFS_conf_scheduler SSc)" for SSc)
     apply(rename_tac e ca f h l r)(*strict*)
     prefer 2
     apply(rule parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
        apply(rename_tac e ca f h l r)(*strict*)
        apply(force)
       apply(rename_tac e ca f h l r)(*strict*)
       apply(rule parserHFS.derivation_initial_belongs)
        apply(rename_tac e ca f h l r)(*strict*)
        apply(force)
       apply(rename_tac e ca f h l r)(*strict*)
       apply(force)
      apply(rename_tac e ca f h l r)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac e ca f h l r)(*strict*)
     apply(force)
    apply(rename_tac e ca f h l r)(*strict*)
    apply(force)
   apply(rename_tac e ca f h l r)(*strict*)
   apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
    apply(rename_tac e ca f h l r)(*strict*)
    prefer 2
    apply(rule parserHFS.some_position_has_details_before_max_dom)
      apply(rename_tac e ca f h l r)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(rename_tac e ca f h l r)(*strict*)
     apply(force)
    apply(rename_tac e ca f h l r)(*strict*)
    apply(force)
   apply(rename_tac e ca f h l r)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ca f h l r ea c)(*strict*)
   apply(rule_tac
      t="min (length r) (parser_fixed_input_length_recN dh xa)"
      and s="parser_fixed_input_length_recN dh xa"
      in ssubst)
    apply(rename_tac e ca f h l r ea c)(*strict*)
    apply(force)
   apply(rename_tac e ca f h l r ea c)(*strict*)
   apply(rule conjI)
    apply(rename_tac e ca f h l r ea c)(*strict*)
    apply(simp add: parserS_set_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def get_configuration_def parserS_get_scheduler_def parserS_get_unfixed_scheduler_DB_def)
    apply(subgoal_tac "take (parser_fixed_input_length_recN dh xa) (parserHFS_conf_scheduler SSc) = parserHFS_conf_fixed SSc" for SSc)
     apply(rename_tac e ca f h l r ea c)(*strict*)
     prefer 2
     apply(rule parserHFS_inst_hlp_AX_state_based_vs_derivation_based_get_fixed_scheduler)
       apply(rename_tac e ca f h l r ea c)(*strict*)
       apply(force)
      apply(rename_tac e ca f h l r ea c)(*strict*)
      apply(force)
     apply(rename_tac e ca f h l r ea c)(*strict*)
     apply(force)
    apply(rename_tac e ca f h l r ea c)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ca h l r ea c)(*strict*)
    apply(simp only: parserHFS_to_parserS_derivation_def)
    apply(clarsimp)
   apply(rename_tac e ca f h l r ea c)(*strict*)
   apply(rule conjI)
    apply(rename_tac e ca f h l r ea c)(*strict*)
    prefer 2
    apply(rule conjI)
     apply(rename_tac e ca f h l r ea c)(*strict*)
     apply(simp add: parserS_set_unfixed_scheduler_DB_def parserHFS_to_parserS_derivation_def get_configuration_def)
     apply(case_tac ca)
     apply(rename_tac e ca f h l r ea c parserS_conf_stacka parserS_conf_scheduler)(*strict*)
     apply(clarsimp)
    apply(rename_tac e ca f h l r ea c)(*strict*)
    apply(simp add: parserS_set_unfixed_scheduler_DB_def parserHFS_to_parserS_derivation_def get_configuration_def parserS_get_fixed_scheduler_DB_def parserS_get_scheduler_def parserHFS_get_fixed_scheduler_DB_def get_configuration_def parserS_get_unfixed_scheduler_DB_def parserHFS_get_scheduler_def parserHFS_get_unfixed_scheduler_DB_def)
    apply(case_tac ca)
    apply(rename_tac e ca f h l r ea c parserS_conf_stack parserS_conf_schedulera)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ca f h l r ea c)(*strict*)
   apply(subgoal_tac "\<exists>c. dh 0 = Some (pair None c)")
    apply(rename_tac e ca f h l r ea c)(*strict*)
    prefer 2
    apply(rule parserHFS.some_position_has_details_at_0)
    apply(simp add: parserHFS.derivation_initial_def)
    apply(force)
   apply(rename_tac e ca f h l r ea c)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ca f h l r ea c cb)(*strict*)
   apply(subgoal_tac "\<exists>w. parserHFS_string_state cb = w @ (parserHFS_string_state \<lparr>parserHFS_conf_fixed = f, parserHFS_conf_history = h, parserHFS_conf_stack = l, parserHFS_conf_scheduler = r\<rparr>)")
    apply(rename_tac e ca f h l r ea c cb)(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      in parserHFS.derivation_monotonically_dec)
         apply(rename_tac e ca f h l r ea c cb)(*strict*)
         apply(force)
        apply(rename_tac e ca f h l r ea c cb)(*strict*)
        apply(force)
       apply(rename_tac e ca f h l r ea c cb)(*strict*)
       apply(rule parserHFS.derivation_initial_belongs)
        apply(rename_tac e ca f h l r ea c cb)(*strict*)
        apply(force)
       apply(rename_tac e ca f h l r ea c cb)(*strict*)
       apply(force)
      apply(rename_tac e ca f h l r ea c cb)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac e ca f h l r ea c cb)(*strict*)
     apply(force)
    apply(rename_tac e ca f h l r ea c cb)(*strict*)
    apply(force)
   apply(rename_tac e ca f h l r ea c cb)(*strict*)
   apply(simp add: parserHFS_string_state_def)
   apply(clarsimp)
   apply(rename_tac e ca f h l r ea c cb w)(*strict*)
   apply(subgoal_tac "w @ butlast_if_match (take (parser_fixed_input_length_recN dh xa) (parserHFS_conf_scheduler \<lparr>parserHFS_conf_fixed = f, parserHFS_conf_history = h, parserHFS_conf_stack = l, parserHFS_conf_scheduler = r\<rparr>)) (parser_bottom G) = parserHFS_conf_history \<lparr>parserHFS_conf_fixed = f, parserHFS_conf_history = h, parserHFS_conf_stack = l, parserHFS_conf_scheduler = r\<rparr>")
    apply(rename_tac e ca f h l r ea c cb w)(*strict*)
    prefer 2
    apply(rule parserHFS_history_equals_removed_append_overhead)
        apply(rename_tac e ca f h l r ea c cb w)(*strict*)
        apply(force)
       apply(rename_tac e ca f h l r ea c cb w)(*strict*)
       apply(force)
      apply(rename_tac e ca f h l r ea c cb w)(*strict*)
      apply(force)
     apply(rename_tac e ca f h l r ea c cb w)(*strict*)
     apply(force)
    apply(rename_tac e ca f h l r ea c cb w)(*strict*)
    apply(force)
   apply(rename_tac e ca f h l r ea c cb w)(*strict*)
   apply(clarsimp)
   apply(rename_tac e ca f l r ea c cb w)(*strict*)
   apply(rule_tac
      t="butlast_if_match (take (parser_fixed_input_length_recN dh xa) (parserS_conf_scheduler (parserS_set_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) xa (the (right_quotient_word (parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) xa) (parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n)) @ sUF)))) (parser_bottom G)"
      and s="butlast_if_match (take (parser_fixed_input_length_recN dh xa) r) (parser_bottom G)"
      in ssubst)
    apply(rename_tac e ca f l r ea c cb w)(*strict*)
    prefer 2
    apply(rule_tac
      t="the (right_quotient_word             (parserS_conf_scheduler               (the (case ATS_SchedUF_DB.replace_unfixed_scheduler_DB                           right_quotient_word (@)                           parserS_set_unfixed_scheduler_DB                           parserS_get_unfixed_scheduler_DB G                           (parserHFS_to_parserS_derivation dh) sUF n 0 of                     None \<Rightarrow> None | Some (pair e b) \<Rightarrow> Some b)))             (parserS_conf_scheduler               (parserS_set_unfixed_scheduler_DB G                 (parserHFS_to_parserS_derivation dh) xa                 (the (right_quotient_word                        (parserS_get_unfixed_scheduler_DB G                          (parserHFS_to_parserS_derivation dh) xa)                        (parserS_get_unfixed_scheduler_DB G                          (parserHFS_to_parserS_derivation dh) n)) @                  sUF))))"
      and s="w"
      in ssubst)
     apply(rename_tac e ca f l r ea c cb w)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac e ca f l r ea c cb w)(*strict*)
    prefer 2
    apply(simp add: parserS_set_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def get_configuration_def parserHFS_to_parserS_derivation_def parserS_get_scheduler_def)
    apply(case_tac ca)
    apply(rename_tac e ca f l r ea c cb w parserS_conf_stack parserS_conf_schedulera)(*strict*)
    apply(clarsimp)
   apply(rename_tac e ca f l r ea c cb w)(*strict*)
   apply(subgoal_tac "\<exists>v. parserHFS_string_state \<lparr>parserHFS_conf_fixed = f, parserHFS_conf_history = w @ butlast_if_match (take (parser_fixed_input_length_recN dh xa) r) (parser_bottom G), parserHFS_conf_stack = l, parserHFS_conf_scheduler = r\<rparr> = v @ (parserHFS_string_state c)")
    apply(rename_tac e ca f l r ea c cb w)(*strict*)
    prefer 2
    apply(rule_tac
      d="dh"
      and j="n-xa"
      in parserHFS.derivation_monotonically_dec)
         apply(rename_tac e ca f l r ea c cb w)(*strict*)
         apply(force)
        apply(rename_tac e ca f l r ea c cb w)(*strict*)
        apply(force)
       apply(rename_tac e ca f l r ea c cb w)(*strict*)
       apply(rule parserHFS.derivation_initial_belongs)
        apply(rename_tac e ca f l r ea c cb w)(*strict*)
        apply(force)
       apply(rename_tac e ca f l r ea c cb w)(*strict*)
       apply(force)
      apply(rename_tac e ca f l r ea c cb w)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac e ca f l r ea c cb w)(*strict*)
     apply(force)
    apply(rename_tac e ca f l r ea c cb w)(*strict*)
    apply(force)
   apply(rename_tac e ca f l r ea c cb w)(*strict*)
   apply(simp add: parserHFS_string_state_def)
   apply(clarsimp)
   apply(rename_tac e ca f l ea c cb w v)(*strict*)
   apply(subgoal_tac "(right_quotient_word             (parserS_conf_scheduler               (the (case ATS_SchedUF_DB.replace_unfixed_scheduler_DB                           right_quotient_word (@)                           parserS_set_unfixed_scheduler_DB                           parserS_get_unfixed_scheduler_DB G                           (parserHFS_to_parserS_derivation dh) sUF n 0 of                     None \<Rightarrow> None | Some (pair e xa) \<Rightarrow> Some xa)))             (parserS_conf_scheduler               (parserS_set_unfixed_scheduler_DB G                 (parserHFS_to_parserS_derivation dh) xa                 (the (right_quotient_word                        (parserS_get_unfixed_scheduler_DB G                          (parserHFS_to_parserS_derivation dh) xa)                        (parserS_get_unfixed_scheduler_DB G                          (parserHFS_to_parserS_derivation dh) n)) @                  sUF))))= Some w")
    apply(rename_tac e ca f l ea c cb w v)(*strict*)
    apply(force)
   apply(rename_tac e ca f l ea c cb w v)(*strict*)
   apply(rule right_quotient_word_Some_by_append)
   apply(rename_tac wa)
   apply(rename_tac e ca f l ea c cb w wa)(*strict*)
   apply(subgoal_tac "parserHFS_conf_scheduler (the(get_configuration(dh xa))) = wa @ parserHFS_conf_scheduler c")
    apply(rename_tac e ca f l ea c cb w wa)(*strict*)
    prefer 2
    apply(simp add: get_configuration_def)
   apply(rename_tac e ca f l ea c cb w wa)(*strict*)
   apply(thin_tac "dh xa = Some (pair e \<lparr>parserHFS_conf_fixed = f, parserHFS_conf_history = w @ butlast_if_match (take (parser_fixed_input_length_recN dh xa) wa @ take (parser_fixed_input_length_recN dh xa - length wa) (parserHFS_conf_scheduler c)) (parser_bottom G), parserHFS_conf_stack = l, parserHFS_conf_scheduler = wa @ parserHFS_conf_scheduler c\<rparr>)")
   apply(rename_tac e ca f l ea c cb w wa)(*strict*)
   apply(thin_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) xa = parser_fixed_input_length_recN dh xa")
   apply(rename_tac e ca f l ea c cb w wa)(*strict*)
   apply(thin_tac "parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) n = parser_fixed_input_length_recN dh n")
   apply(rename_tac e ca f l ea c cb w wa)(*strict*)
   apply(thin_tac "parser_fixed_input_length_recN dh xa \<le> length wa + length (parserHFS_conf_scheduler c)")
   apply(rename_tac e ca f l ea c cb w wa)(*strict*)
   apply(induct xa)
    apply(rename_tac e ca f l ea c cb w wa)(*strict*)
    apply(clarsimp)
    apply(rename_tac e ca ea c cb w wa)(*strict*)
    apply(simp add: parserS_set_unfixed_scheduler_DB_def parserS_get_fixed_scheduler_DB_def get_configuration_def parserHFS_to_parserS_derivation_def parserS_get_scheduler_def parserS_get_unfixed_scheduler_DB_def parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def get_configuration_def)
   apply(rename_tac xa e ca f l ea c cb w wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e ca ea c cb w wa)(*strict*)
   apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
    apply(rename_tac xa e ca ea c cb w wa)(*strict*)
    prefer 2
    apply(rule_tac parserHFS.pre_some_position_is_some_position)
      apply(rename_tac xa e ca ea c cb w wa)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(rename_tac xa e ca ea c cb w wa)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb w wa)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb w wa)(*strict*)
   apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation dh xa = Some (pair e c)")
    apply(rename_tac xa e ca ea c cb w wa)(*strict*)
    prefer 2
    apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(clarsimp)
   apply(rename_tac xa e ca ea c cb w wa)(*strict*)
   apply(subgoal_tac "\<exists>e c. dh (Suc xa) = Some (pair (Some e) c)")
    apply(rename_tac xa e ca ea c cb w wa)(*strict*)
    prefer 2
    apply(rule_tac parserHFS.pre_some_position_is_some_position_prime)
       apply(rename_tac xa e ca ea c cb w wa)(*strict*)
       apply(simp add: parserHFS.derivation_initial_def)
       apply(force)
      apply(rename_tac xa e ca ea c cb w wa)(*strict*)
      apply(force)
     apply(rename_tac xa e ca ea c cb w wa)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb w wa)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb w wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
   apply(erule_tac
      x="ec"
      in meta_allE)
   apply(erule_tac
      x="cd"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="ea"
      in meta_allE)
   apply(erule_tac
      x="c"
      in meta_allE)
   apply(erule_tac
      x="cb"
      in meta_allE)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>w. parserHFS_string_state cb = w @ (parserHFS_string_state cc)")
    apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
    prefer 2
    apply(rule_tac
      i="0"
      and j="xa"
      in parserHFS.derivation_monotonically_dec)
         apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
         apply(force)
        apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
        apply(force)
       apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
       apply(rule parserHFS.derivation_initial_belongs)
        apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
        apply(force)
       apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
       apply(force)
      apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
   apply(subgoal_tac "\<exists>w. parserHFS_string_state cc = w @ (parserHFS_string_state ce)")
    apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
    prefer 2
    apply(rule_tac
      i="xa"
      and j="Suc 0"
      in parserHFS.derivation_monotonically_dec)
         apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
         apply(force)
        apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
        apply(force)
       apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
       apply(rule parserHFS.derivation_initial_belongs)
        apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
        apply(force)
       apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
       apply(force)
      apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
   apply(subgoal_tac "\<exists>w. parserHFS_string_state ce = w @ (parserHFS_string_state c)")
    apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
    prefer 2
    apply(rule_tac
      i="Suc xa"
      and j="n- Suc xa"
      in parserHFS.derivation_monotonically_dec)
         apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
         apply(force)
        apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
        apply(force)
       apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
       apply(rule parserHFS.derivation_initial_belongs)
        apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
        apply(force)
       apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
       apply(force)
      apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e ca ea c cb w wa eb ec ed cc "cd" ce wb wc wd)(*strict*)
   apply(simp add: parserHFS_string_state_def get_configuration_def)
   apply(clarsimp)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
   apply(erule_tac
      x="wb"
      in meta_allE)
   apply(clarsimp)
   apply(erule_tac
      x="wc@wd"
      in meta_allE)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>w. parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) xa = w @ (parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n)")
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
    prefer 2
    apply(rule parserHFS_parserS_schedUF_db_decreases)
        apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
        apply(force)
       apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
       apply(force)
      apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
      apply(force)
     apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w)(*strict*)
   apply(subgoal_tac "\<exists>w. parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) (Suc xa) = w @ (parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n)")
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w)(*strict*)
    prefer 2
    apply(rule parserHFS_parserS_schedUF_db_decreases)
        apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w)(*strict*)
        apply(force)
       apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w)(*strict*)
       apply(force)
      apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w)(*strict*)
      apply(force)
     apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
   apply(simp add: right_quotient_word_def)
   apply(simp add: parserS_set_unfixed_scheduler_DB_def)
   apply(rule_tac
      v="parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n"
      in append_injr)
   apply(rule_tac
      t="(parserS_get_fixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) xa @ w) @ parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n"
      and s="parserS_get_scheduler (the(get_configuration(parserHFS_to_parserS_derivation dh xa)))"
      in ssubst)
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
    apply(simp (no_asm))
    apply(rule_tac
      t="w @ parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n"
      and s="parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) xa"
      in ssubst)
     apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
    apply(simp (no_asm) add: parserS_get_fixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
   apply(simp (no_asm))
   apply(rule_tac
      t="wa @ parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n"
      and s="parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) (Suc xa)"
      in ssubst)
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
   apply(rule_tac
      t="parserS_get_fixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) (Suc xa) @ parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) (Suc xa)"
      and s="parserS_get_scheduler (the (get_configuration (parserHFS_to_parserS_derivation dh (Suc xa))))"
      in ssubst)
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
    apply(simp (no_asm) add: parserS_get_fixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
   apply(thin_tac "parserS_conf_scheduler        (the (case ATS_SchedUF_DB.replace_unfixed_scheduler_DB                    right_quotient_word (@)                    parserS_set_unfixed_scheduler_DB                    parserS_get_unfixed_scheduler_DB G                    (parserHFS_to_parserS_derivation dh) sUF n 0 of              None \<Rightarrow> None | Some (pair e xa) \<Rightarrow> Some xa)) =       wb @       parserS_get_fixed_scheduler_DB G (parserHFS_to_parserS_derivation dh)        xa @       w @ sUF")
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
   apply(thin_tac " parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) xa = w @ parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n")
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
   apply(thin_tac " parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) (Suc xa) = wa @ parserS_get_unfixed_scheduler_DB G (parserHFS_to_parserS_derivation dh) n")
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. dh xa = Some (pair e1 c1) \<and> dh (Suc xa) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
    prefer 2
    apply(rule_tac
      m="Suc xa"
      in parserHFS.step_detail_before_some_position)
      apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
     apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
     apply(force)
    apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
    apply(force)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd w wa)(*strict*)
   apply(clarsimp)
   apply(rename_tac xa e ca ea c cb eb ec ed cc "cd" ce wb wc wd)(*strict*)
   apply(simp add: get_configuration_def)
   apply(simp add: parserS_get_scheduler_def parserHFS_step_relation_def parserHFS_to_parserS_derivation_def)
   apply(clarsimp)
  apply(rename_tac e ca f h l r)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN dh xa"
      and s="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) xa"
      in ssubst)
   apply(rename_tac e ca f h l r)(*strict*)
   defer
   apply(rule parser_S_HFS_replace_unfixed_scheduler_DB_preserves_parser_fixed_input_length_recN)
      apply(rename_tac e ca f h l r)(*strict*)
      apply(force)+
     apply(rename_tac e ca f h l r)(*strict*)
     apply(rule parserHFS_to_parserS_derivation_preserves_maximum_of_domain)
      apply(rename_tac e ca f h l r)(*strict*)
      apply(force)+
   apply(rename_tac e ca f h l r)(*strict*)
   apply(rule parserHFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac e ca f h l r)(*strict*)
    apply(force)+
  apply(rename_tac e ca f h l r)(*strict*)
  apply (metis parserHFS.derivation_initial_is_derivation parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
  done

lemma parserHFS_get_unfixed_scheduler_DB_on_modification: "
  valid_parser G
  \<Longrightarrow> maximum_of_domain dh n
  \<Longrightarrow> sUF \<sqsupseteq> [parser_bottom G]
  \<Longrightarrow> parserHFS.derivation_initial G dh
  \<Longrightarrow> parserHFS_get_unfixed_scheduler_DB G (parserHFS.replace_unfixed_scheduler_DB G dh sUF n) n = sUF"
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS.replace_unfixed_scheduler_DB G dh sUF n) n"
      and s="parser_fixed_input_length_recN dh n"
      in ssubst)
   apply(rule parserHFS_parser_fixed_input_length_recN_equal_by_labels)
     apply(rule mod_preserves_derivation_prime)
        apply(force)+
    apply(simp add: parserHFS.derivation_initial_def)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(subgoal_tac "\<exists>e c. dh i = Some (pair e c)")
    apply(rename_tac i)(*strict*)
    apply(clarsimp)
    apply(rename_tac i e c)(*strict*)
    apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def)
    apply(simp add: parserHFS.map_unfixed_scheduler_DB_def)
   apply(rename_tac i)(*strict*)
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac i)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
   apply(clarsimp)
   apply(rename_tac e c)(*strict*)
   apply(rule_tac
      t="parserHFS_get_scheduler (the (get_configuration (parserHFS.replace_unfixed_scheduler_DB G dh sUF n n)))"
      and s="parserHFS_get_fixed_scheduler_DB G dh n @ sUF"
      in ssubst)
    apply(rename_tac e c)(*strict*)
    defer
    apply(simp add: parserHFS_get_fixed_scheduler_DB_def)
    apply(rule_tac
      t="(parser_fixed_input_length_recN dh n - min (length (parserHFS_get_scheduler (the (get_configuration (Some (pair e c)))))) (parser_fixed_input_length_recN dh n))"
      and s="0"
      in ssubst)
     apply(rename_tac e c)(*strict*)
     defer
     apply(force)
    apply(rule parserHFS.some_position_has_details_before_max_dom)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(rename_tac e c)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(simp add: get_configuration_def parserHFS_get_scheduler_def)
   apply(rule_tac
      d="dh"
      and m="n"
      and c="c"
      in parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
      apply(rename_tac e c)(*strict*)
      apply(force)
     apply(rename_tac e c)(*strict*)
     apply(rule parserHFS.derivation_initial_belongs)
      apply(rename_tac e c)(*strict*)
      apply(force)
     apply(rename_tac e c)(*strict*)
     apply(force)
    apply(rename_tac e c)(*strict*)
    apply(simp add: parserHFS.derivation_initial_def)
   apply(rename_tac e c)(*strict*)
   apply(force)
  apply(rename_tac e c)(*strict*)
  apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def get_configuration_def parserHFS_set_unfixed_scheduler_DB_def parserHFS_get_scheduler_def parserHFS_get_unfixed_scheduler_DB_def right_quotient_word_def)
  done

lemma parserHFS_get_unfixed_scheduler_DB_with_derivation_take: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> parserHFS_get_unfixed_scheduler_DB G d n = parserHFS_get_unfixed_scheduler_DB G (derivation_take d n) n"
  apply(simp add: parserHFS_get_unfixed_scheduler_DB_def)
  apply(rule_tac
      t="parser_fixed_input_length_recN (derivation_take d n) n"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
   apply(rule parserHFS_parser_fixed_input_length_recN_with_derivation_take)
    apply(force)
   apply(force)
  apply(simp add: derivation_take_def)
  done

lemma derivation_take_distributes_over_parserS_to_parserHFS_derivation: "
  derivation_take (parserS_to_parserHFS_derivation G d) n = parserS_to_parserHFS_derivation G (derivation_take d n)"
  apply(rule ext)
  apply(rename_tac x)(*strict*)
  apply(simp add: derivation_take_def parserS_to_parserHFS_derivation_def derivation_take_def)
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
   apply(fold derivation_take_def parserS_to_parserHFS_derivation_def derivation_take_def)
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

lemma parserS_vs_parserHFS_inst_hlp_bisimulation_compatible_with_replace_and_schedF: "
  valid_parser G1
  \<Longrightarrow> parserHFS.derivation_initial G1 dh
  \<Longrightarrow> maximum_of_domain dh x
  \<Longrightarrow> maximum_of_domain (parserHFS_to_parserS_derivation dh) n
  \<Longrightarrow> parserHFS.derivation_initial G1 dc'
  \<Longrightarrow> parserHFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n
  \<Longrightarrow> parserHFS_get_unfixed_scheduler_DB G1 dh n \<sqsupseteq> [parser_bottom G1]
  \<Longrightarrow> sUF \<sqsupseteq> [parser_bottom G1]
  \<Longrightarrow> sUF \<in> parser_unfixed_schedulers G1
  \<Longrightarrow> maximum_of_domain dc' xb
  \<Longrightarrow> xa \<le> n
  \<Longrightarrow> parserHFS_get_fixed_scheduler_DB G1 dh xa = parserHFS_get_fixed_scheduler_DB G1 dc' xa \<and> parserHFS.replace_unfixed_scheduler_DB G1 dh (parserHFS_get_unfixed_scheduler_DB G1 dc' n) n xa = dc' xa"
  apply(subgoal_tac "x=n")
   prefer 2
   apply(rule parserHFS.maximum_of_domainUnique)
     prefer 3
     apply(force)
    apply(simp add: parserHFS.derivation_initial_def)
    apply(force)
   apply(simp add: parserHFS_to_parserS_derivation_def)
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
    apply(rule parserHFS.none_position_after_max_dom)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "parserHFS_to_parserS_derivation dc' n = derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n n")
    prefer 2
    apply(force)
   apply(thin_tac "parserHFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n")
   apply(simp add: parserHFS_to_parserS_derivation_def derivation_append_def)
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def)
   apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
    apply(clarsimp)
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac n')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac n')(*strict*)
   apply(rule parserHFS_to_parserS_derivation_preserves_get_fixed_scheduler_DB_uniform)
             apply(rename_tac n')(*strict*)
             prefer 9
             apply(force)+
  apply(rename_tac n')(*strict*)
  apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   apply(rename_tac n')(*strict*)
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac n')(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n')(*strict*)
    apply(force)
   apply(rename_tac n')(*strict*)
   apply(force)
  apply(rename_tac n')(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n = Some (pair e c)")
   apply(rename_tac n')(*strict*)
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac n')(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n')(*strict*)
    apply(force)
   apply(rename_tac n')(*strict*)
   apply(force)
  apply(rename_tac n')(*strict*)
  apply(clarsimp)
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(subgoal_tac "dc' = parserS_to_parserHFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n)")
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(thin_tac "parserHFS_to_parserS_derivation dc' = derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n")
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "parserS_to_parserHFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n) xa = parserS_to_parserHFS_derivation G1 ((parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) ) xa")
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "parserHFS_get_unfixed_scheduler_DB G1 (parserS_to_parserHFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n)) n = sUF")
     apply(rename_tac n' e ea c ca)(*strict*)
     apply(clarsimp)
     apply(rule_tac
      t="parserS_to_parserHFS_derivation G1 (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) xa"
      and s=" (parserHFS.replace_unfixed_scheduler_DB G1 dh sUF n) xa"
      in ssubst)
      apply(rename_tac n' e ea c ca)(*strict*)
      prefer 2
      apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def)
      apply(simp add: parserHFS.map_unfixed_scheduler_DB_def)
     apply(rename_tac n' e ea c ca)(*strict*)
     apply(rule parserHFS_double_funct_mod_vs_mod)
        apply(rename_tac n' e ea c ca)(*strict*)
        apply(force)+
    apply(rename_tac n' e ea c ca)(*strict*)
    prefer 2
    apply(simp add: parserS_to_parserHFS_derivation_def derivation_append_def)
    apply(case_tac "parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n xa")
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
      t="parser_fixed_input_length_recN (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n) xa"
      and s="parser_fixed_input_length_recN (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) xa"
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
    apply (rule parserHFS_to_parserS_derivation_preserves_derivation_initial)
     apply(rename_tac n' e ea c ca option b)(*strict*)
     apply(force)+
   apply(rename_tac n' e ea c ca)(*strict*)
   prefer 2
   apply(rule_tac
      t="dc'"
      and s="parserS_to_parserHFS_derivation G1 (parserHFS_to_parserS_derivation dc')"
      in subst)
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(rule ext)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(rule parser_S_HFS_relation_coincide_hlp)
      apply(rename_tac n' e ea c ca x)(*strict*)
      apply(force)+
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(rule_tac
      t="parserHFS_get_unfixed_scheduler_DB G1 (parserS_to_parserHFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n)) n"
      and s="parserHFS_get_unfixed_scheduler_DB G1 (parserS_to_parserHFS_derivation G1 ((parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) )) n"
      in ssubst)
   apply(rename_tac n' e ea c ca)(*strict*)
   defer
   apply(rule_tac
      t="parserS_to_parserHFS_derivation G1 (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n)"
      and s="parserHFS.replace_unfixed_scheduler_DB G1 dh sUF n"
      in ssubst)
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(rule ext)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(case_tac "x\<le>n")
     apply(rename_tac n' e ea c ca x)(*strict*)
     apply(rule parserHFS_double_funct_mod_vs_mod)
        apply(rename_tac n' e ea c ca x)(*strict*)
        apply(force)+
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(subgoal_tac "dh x = None")
     apply(rename_tac n' e ea c ca x)(*strict*)
     apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def parserS_to_parserHFS_derivation_def parserHFS_to_parserS_derivation_def)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(rule parserHFS.none_position_after_max_dom)
      apply(rename_tac n' e ea c ca x)(*strict*)
      apply(simp add: parserHFS.derivation_initial_def)
      apply(force)
     apply(rename_tac n' e ea c ca x)(*strict*)
     apply(force)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(force)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(rule parserHFS_get_unfixed_scheduler_DB_on_modification)
      apply(rename_tac n' e ea c ca)(*strict*)
      apply(force)+
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(rule_tac
      t="parserHFS_get_unfixed_scheduler_DB G1 (parserS_to_parserHFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n)) n"
      and s="parserHFS_get_unfixed_scheduler_DB G1 (derivation_take (parserS_to_parserHFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n)) n) n"
      in ssubst)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(rule parserHFS_get_unfixed_scheduler_DB_with_derivation_take)
    apply(rename_tac n' e ea c ca)(*strict*)
    apply(force)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(simp add: parserHFS.derivation_initial_def)
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(rule_tac
      t="derivation_take (parserS_to_parserHFS_derivation G1 (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n)) n"
      and s=" (parserS_to_parserHFS_derivation G1 (derivation_take (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n) n))"
      in ssubst)
   apply(rename_tac n' e ea c ca)(*strict*)
   prefer 2
   apply(rule_tac
      t="derivation_take (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n) n"
      and s="parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n"
      in ssubst)
    apply(rename_tac n' e ea c ca)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n' e ea c ca)(*strict*)
   apply(rule_tac
      t="derivation_take (derivation_append (parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n) n"
      and s="derivation_take ((parserS.replace_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) ) n"
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
   apply(simp add: parserS.replace_unfixed_scheduler_DB_def parserS.map_unfixed_scheduler_DB_def parserHFS_to_parserS_derivation_def)
   apply(subgoal_tac "dh x=None")
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(clarsimp)
   apply(rename_tac n' e ea c ca x)(*strict*)
   apply(rule parserHFS.none_position_after_max_dom)
     apply(rename_tac n' e ea c ca x)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
     apply(force)
    apply(rename_tac n' e ea c ca x)(*strict*)
    apply(force)
   apply(rename_tac n' e ea c ca x)(*strict*)
   apply(force)
  apply(rename_tac n' e ea c ca)(*strict*)
  apply(rule derivation_take_distributes_over_parserS_to_parserHFS_derivation)
  done

lemma parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_replace_and_schedF1: "
  (\<forall>G1. valid_parser G1 \<longrightarrow> (\<forall>dh. parserHFS.derivation_initial G1 dh \<and> Ex (maximum_of_domain dh) \<longrightarrow> (\<forall>n. maximum_of_domain (parserHFS_to_parserS_derivation dh) n \<longrightarrow> parserHFS_get_unfixed_scheduler_DB G1 dh n \<sqsupseteq> [parser_bottom G1] \<longrightarrow> (\<forall>sUF. sUF \<sqsupseteq> [parser_bottom G1] \<longrightarrow> sUF \<in> parser_unfixed_schedulers G1 \<longrightarrow> (\<forall>dc dc'. parserHFS.derivation_initial G1 dc' \<and> Ex (maximum_of_domain dc') \<and> parserHFS_to_parserS_derivation dc' = derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) sUF n) dc n \<longrightarrow> (\<forall>x\<le>n. parserHFS_get_fixed_scheduler_DB G1 dh x = parserHFS_get_fixed_scheduler_DB G1 dc' x \<and> ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh (
parserHFS_get_unfixed_scheduler_DB G1 dc' n) n x = dc' x))))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x sUF dc dc' xa xb)(*strict*)
  apply(rule parserS_vs_parserHFS_inst_hlp_bisimulation_compatible_with_replace_and_schedF)
            apply(rename_tac G1 dh n x sUF dc dc' xa xb)(*strict*)
            apply(force)+
  done

lemma parser_parserHFS_parserHFS_parser_fixed_input_length_recN_equal_by_labels: "
  parserS.derivation G d1
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

lemma parserHFS_parser_fixed_input_length_recN_equals_parserHFS_get_fixed_scheduler_DB_length: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> parser_fixed_input_length_recN d n = length (parserHFS_get_fixed_scheduler_DB G1 d n)"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(simp add: parserHFS_get_fixed_scheduler_DB_def)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(simp add: parserHFS_get_fixed_scheduler_DB_def get_configuration_def)
  apply(subgoal_tac "length (rule_rpop e2) \<ge> length (rule_rpush e2)")
   apply(rename_tac n c e1 e2 c1)(*strict*)
   apply(subgoal_tac "parser_fixed_input_length_recN d n \<le> length (parserHFS_conf_scheduler c1)")
    apply(rename_tac n c e1 e2 c1)(*strict*)
    prefer 2
    apply(rule parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
       apply(rename_tac n c e1 e2 c1)(*strict*)
       apply(force)
      apply(rename_tac n c e1 e2 c1)(*strict*)
      apply (metis parserHFS.derivation_initial_belongs)
     apply(rename_tac n c e1 e2 c1)(*strict*)
     apply (metis parserHFS.derivation_initial_is_derivation)
    apply(rename_tac n c e1 e2 c1)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1)(*strict*)
   apply(case_tac "(parser_fixed_input_length_recN d n) - (length (rule_rpop e2))")
    apply(rename_tac n c e1 e2 c1)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="max (parser_fixed_input_length_recN d n) (length (rule_rpop e2))"
      and s="length (rule_rpop e2)"
      in ssubst)
     apply(rename_tac n c e1 e2 c1)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 c1)(*strict*)
    apply(clarsimp)
    apply(simp add: parserHFS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac n c e1 e2 c1 x xa y)(*strict*)
    apply(subgoal_tac "(length (parserHFS_get_scheduler c)) \<ge> (length (rule_rpush e2))")
     apply(rename_tac n c e1 e2 c1 x xa y)(*strict*)
     apply(force)
    apply(rename_tac n c e1 e2 c1 x xa y)(*strict*)
    apply (metis drop_length_append parserHFS_get_scheduler_def)
   apply(rename_tac n c e1 e2 c1 nat)(*strict*)
   apply(rule_tac
      t="max (parser_fixed_input_length_recN d n) (length (rule_rpop e2))"
      and s="parser_fixed_input_length_recN d n"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 nat)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 nat)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "(length (parserHFS_get_scheduler c)) \<ge> (parser_fixed_input_length_recN d n + length (rule_rpush e2) - length (rule_rpop e2))")
    apply(rename_tac n c e1 e2 c1 nat)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 nat)(*strict*)
   apply(erule_tac
      x="e1"
      in meta_allE)
   apply(erule_tac
      x="c1"
      in meta_allE)
   apply(clarsimp)
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(rename_tac n c e1 e2 c1 nat)(*strict*)
    prefer 2
    apply(simp add: parserHFS_step_relation_def valid_parser_def)
   apply(rename_tac n c e1 e2 c1 nat)(*strict*)
   apply(simp add: parserHFS_step_relation_def valid_parser_step_label_def)
   apply(clarsimp)
   apply(rename_tac n c e1 e2 c1 nat k w xa xb y xc)(*strict*)
   apply(subgoal_tac "(length (parserHFS_get_scheduler c1)) \<ge> (parser_fixed_input_length_recN d n)")
    apply(rename_tac n c e1 e2 c1 nat k w xa xb y xc)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac n c e1 e2 c1 nat k w xa xb y xc)(*strict*)
   apply(rule_tac
      j="length (kPrefix k (w @ [parser_bottom G]) @ xb) + length (rule_rpush e2) - length (kPrefix k (w @ [parser_bottom G]))"
      in le_trans)
    apply(rename_tac n c e1 e2 c1 nat k w xa xb y xc)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 nat k w xa xb y xc)(*strict*)
   apply(rule_tac
      t="length (kPrefix k (w @ [parser_bottom G]) @ xb) + length (rule_rpush e2) - length (kPrefix k (w @ [parser_bottom G]))"
      and s="length xb + length (rule_rpush e2)"
      in ssubst)
    apply(rename_tac n c e1 e2 c1 nat k w xa xb y xc)(*strict*)
    apply(force)
   apply(rename_tac n c e1 e2 c1 nat k w xa xb y xc)(*strict*)
   apply(simp add: parserHFS_get_scheduler_def)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac n c e1 e2 c1)(*strict*)
   prefer 2
   apply(simp add: parserHFS_step_relation_def valid_parser_def)
  apply(rename_tac n c e1 e2 c1)(*strict*)
  apply(simp add: parserHFS_step_relation_def valid_parser_step_label_def)
  apply(clarsimp)
  apply(rename_tac n c e1 e2 c1 k w xa xb y xc)(*strict*)
  apply(metis valid_parser_rules_rhs_gets_shorter)
  done

lemma parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_replace_and_schedF2: "
  \<forall>G1. valid_parser G1 \<longrightarrow>
         (\<forall>dh. ATS.derivation_initial parserHFS_initial_configurations
                parserHFS_step_relation G1 dh \<and>
               Ex (maximum_of_domain dh) \<longrightarrow>
               (\<forall>n. maximum_of_domain dh n \<longrightarrow>
                    parserS_get_unfixed_scheduler_DB G1
                     (parserHFS_to_parserS_derivation dh) n \<sqsupseteq>
                    [parser_bottom G1] \<longrightarrow>
                    (\<forall>sUF'.
                        sUF' \<sqsupseteq> [parser_bottom G1] \<longrightarrow>
                        sUF' \<in> parser_unfixed_schedulers G1 \<longrightarrow>
                        (\<forall>dc. (\<exists>dc'. ATS.derivation_initial
                                      parserHFS_initial_configurations
                                      parserHFS_step_relation G1
                                      (derivation_append
 (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
   parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1
   dh sUF' n)
 dc' n) \<and>
                                     Ex (maximum_of_domain
   (derivation_append
     (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
       parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB
       G1 dh sUF' n)
     dc' n)) \<and>
                                     parserHFS_to_parserS_derivation
                                      (derivation_append
 (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@)
   parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1
   dh sUF' n)
 dc' n) =
                                     dc) \<longrightarrow>
                              (\<forall>x\<le>n. parserS_get_fixed_scheduler_DB G1
(parserHFS_to_parserS_derivation dh) x =
                                      parserS_get_fixed_scheduler_DB G1 dc
x \<and>
                                      ATS_SchedUF_DB.replace_unfixed_scheduler_DB
right_quotient_word (@) parserS_set_unfixed_scheduler_DB parserS_get_unfixed_scheduler_DB G1
(parserHFS_to_parserS_derivation dh) (parserS_get_unfixed_scheduler_DB G1 dc n) n
x =
                                      dc x)))))"
  apply(clarsimp)
  apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
  apply(subgoal_tac "n=x")
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   prefer 2
   apply(rule parserHFS.maximum_of_domainUnique)
     apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh n x sUF' dc' xa xb)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(simp add: parserS_get_fixed_scheduler_DB_def)
   apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) xa"
      and s="parser_fixed_input_length_recN dh xa"
      in ssubst)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply (metis parserHFS.derivation_initial_is_derivation parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x)) xa"
      and s="parser_fixed_input_length_recN dh xa"
      in ssubst)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    prefer 2
    apply(simp add: parserS_get_scheduler_def)
    apply(rule_tac
      t="parserHFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x) xa"
      and s="parserHFS_to_parserS_derivation (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) xa"
      in ssubst)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(simp (no_asm) add: derivation_append_def parserHFS_to_parserS_derivation_def)
     apply(clarsimp)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation dh xa = Some (pair e c)")
      apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
      apply(simp (no_asm) add: parserHFS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def)
      apply(simp (no_asm) add: parserHFS_to_parserS_derivation_def)
      apply(clarsimp)
      apply(simp add: get_configuration_def)
      apply(simp add: parserHFS_set_unfixed_scheduler_DB_def)
      apply(subgoal_tac "parser_fixed_input_length_recN dh xa \<le> length (parserHFS_get_fixed_scheduler_DB G1 dh xa)")
       apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
       apply(clarsimp)
       apply(simp add: parserHFS_get_fixed_scheduler_DB_def)
       apply(simp add: get_configuration_def parserHFS_get_scheduler_def)
       apply(simp add: parserHFS_to_parserS_derivation_def)
       apply(clarsimp)
      apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
      apply(simp add: parserHFS_get_fixed_scheduler_DB_def)
      apply(simp add: get_configuration_def parserHFS_get_scheduler_def)
      apply(rule parserHFS_PARSER_possibility_of_restriction_EffectOverhead_prime)
         apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
        apply(rule parserHFS.derivation_initial_belongs)
         apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
         apply(force)
        apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
        apply(force)
       apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
       apply(rule parserHFS.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac G1 dh x sUF' dc' xa xb e ea c ca)(*strict*)
      apply(force)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(simp add: parserHFS_to_parserS_derivation_def)
     apply(clarsimp)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(rule parserHFS.some_position_has_details_before_max_dom)
      apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
      apply(rule parserHFS.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(rule parser_parserHFS_parserHFS_parser_fixed_input_length_recN_equal_by_labels)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(rule parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
      apply(force)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(rule parserHFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. dh i = Some (pair e c)")
    apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
    apply(simp add: parserHFS_to_parserS_derivation_def derivation_append_def get_label_def)
    apply(clarsimp)
    apply(rename_tac G1 dh x sUF' dc' xa xb i e c)(*strict*)
    apply(simp add: parserHFS.map_unfixed_scheduler_DB_def parserHFS.replace_unfixed_scheduler_DB_def get_label_def)
   apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule_tac
      t="parserHFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x) xa"
      and s="parserHFS_to_parserS_derivation ((ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) ) xa"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def derivation_append_def get_label_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule_tac
      t="(parserS_get_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x)) x)"
      and s="(drop (parser_fixed_input_length_recN (parserHFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x)) x) (parserS_get_scheduler (the (get_configuration (parserHFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x) x)))))"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(simp add: parserS_get_unfixed_scheduler_DB_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule_tac
      t="parserHFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x) x"
      and s="parserHFS_to_parserS_derivation ((ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) ) x"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def derivation_append_def get_label_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation (derivation_append (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) dc' x)) x"
      and s="parser_fixed_input_length_recN dh x"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(rule parser_parserHFS_parserHFS_parser_fixed_input_length_recN_equal_by_labels)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(rule parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
      apply(force)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(rule parserHFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. dh i = Some (pair e c)")
    apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
    apply(simp add: parserHFS_to_parserS_derivation_def derivation_append_def get_label_def)
    apply(clarsimp)
    apply(rename_tac G1 dh x sUF' dc' xa xb i e c)(*strict*)
    apply(simp add: parserHFS.map_unfixed_scheduler_DB_def parserHFS.replace_unfixed_scheduler_DB_def get_label_def)
   apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb i)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh x = Some (pair e c)")
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb)(*strict*)
  apply(erule exE)+
  apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
  apply(rule_tac
      t="parserS_get_scheduler (the (get_configuration (parserHFS_to_parserS_derivation (ATS_SchedUF_DB.replace_unfixed_scheduler_DB right_quotient_word (@) parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB G1 dh sUF' x) x)))"
      and s="parserS_get_scheduler (the (get_configuration (Some (pair e \<lparr>parserS_conf_stack = parserHFS_conf_stack (parserHFS_set_unfixed_scheduler_DB G1 dh x sUF'), parserS_conf_scheduler = parserHFS_conf_scheduler (parserHFS_set_unfixed_scheduler_DB G1 dh x sUF')\<rparr>))))"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
   apply(simp add: parserHFS.replace_unfixed_scheduler_DB_def parserS.replace_unfixed_scheduler_DB_def parserHFS.map_unfixed_scheduler_DB_def parserHFS_to_parserS_derivation_def)
   apply(rule_tac
      t="right_quotient_word (parserHFS_get_unfixed_scheduler_DB G1 dh x) (parserHFS_get_unfixed_scheduler_DB G1 dh x)"
      and s="Some []"
      in ssubst)
    apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
    apply(simp add: right_quotient_word_def)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
  apply(simp (no_asm) add: get_configuration_def)
  apply(simp (no_asm) add: parserS_get_scheduler_def)
  apply(simp (no_asm) add: parserHFS_to_parserS_derivation_def parserS.map_unfixed_scheduler_DB_def parserS.replace_unfixed_scheduler_DB_def parserHFS.replace_unfixed_scheduler_DB_def)
  apply(subgoal_tac "\<exists>e c. dh xa = Some (pair e c)")
   apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
   prefer 2
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
  apply(simp add: parserS_set_unfixed_scheduler_DB_def)
  apply(simp add: get_configuration_def parserHFS.map_unfixed_scheduler_DB_def)
  apply(rule conjI)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
   apply(simp add: parserHFS_set_unfixed_scheduler_DB_def)
   apply(simp add: get_configuration_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
  apply(simp add: parserHFS_set_unfixed_scheduler_DB_def)
  apply(subgoal_tac "parser_fixed_input_length_recN (\<lambda>a. case_option None (case_derivation_configuration (\<lambda>e c. Some (pair e \<lparr>parserS_conf_stack = parserHFS_conf_stack c, parserS_conf_scheduler = parserHFS_conf_scheduler c\<rparr>))) (dh a)) xa=parser_fixed_input_length_recN dh xa")
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
   prefer 2
   apply(rule parser_parserHFS_parserHFS_parser_fixed_input_length_recN_equal_by_labels)
     apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
     apply(rule parserS.derivation_initial_is_derivation)
     apply(fold parserHFS_to_parserS_derivation_def)
     apply(rule parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
      apply(force)
     apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
    apply(rule parserHFS.derivation_initial_is_derivation)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca i)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e c. dh i = Some (pair e c)")
    apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca i)(*strict*)
    apply(simp add: parserHFS_to_parserS_derivation_def derivation_append_def get_label_def)
    apply(clarsimp)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca i)(*strict*)
   apply(simp add: parserHFS.map_unfixed_scheduler_DB_def parserHFS.replace_unfixed_scheduler_DB_def get_label_def)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca i)(*strict*)
   apply(rule parserHFS.some_position_has_details_before_max_dom)
     apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca i)(*strict*)
     apply(rule parserHFS.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca i)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca i)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
  apply(rule_tac
      t="parserS_get_fixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) xa"
      and s="parserHFS_get_fixed_scheduler_DB G1 dh xa"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
   apply(simp add: parserS_get_fixed_scheduler_DB_def parserHFS_get_fixed_scheduler_DB_def)
   apply(simp add: get_configuration_def parserS_get_scheduler_def parserHFS_get_scheduler_def get_configuration_def parserHFS_to_parserS_derivation_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "parser_fixed_input_length_recN dh x = length (parserHFS_get_fixed_scheduler_DB G1 dh x)")
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
   prefer 2
   apply(rule parserHFS_parser_fixed_input_length_recN_equals_parserHFS_get_fixed_scheduler_DB_length)
     apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
     apply(force)
    apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
    apply(force)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
   apply(force)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) xa"
      and s="parserHFS_get_unfixed_scheduler_DB G1 dh xa"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def parserHFS_get_unfixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
   apply(simp add: parserHFS_get_scheduler_def get_configuration_def parserS_get_scheduler_def get_configuration_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
  apply(rule_tac
      t="parserS_get_unfixed_scheduler_DB G1 (parserHFS_to_parserS_derivation dh) x"
      and s="parserHFS_get_unfixed_scheduler_DB G1 dh x"
      in ssubst)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
   apply(simp add: parserHFS_get_unfixed_scheduler_DB_def parserS_get_unfixed_scheduler_DB_def)
   apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation dh) x"
      and s="parser_fixed_input_length_recN dh x"
      in ssubst)
    apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
    apply (metis parserHFS.derivation_initial_is_derivation parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
   apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def parserHFS_get_scheduler_def parserS_get_scheduler_def get_configuration_def get_configuration_def)
  apply(rename_tac G1 dh x sUF' dc' xa xb e c ea ca)(*strict*)
  apply(force)
  done

lemma parserS_vs_parserHFS_inst_AX_unAX_marked_effect_id1: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o1. o1 \<in> parserS_unmarked_effect G1 (parserHFS_to_parserS_derivation d2) \<longrightarrow> o1 \<in> parserHFS_unmarked_effect G1 d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o1 x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c c' i e v)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c c' i e v)(*strict*)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(rename_tac G1 d2 x c c' i e v)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(rule_tac
      x="ea"
      in exI)
    apply(rule_tac
      x="cb"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "v @ butlast_if_match (take (parser_fixed_input_length_recN d2 i) (parserHFS_conf_scheduler cb)) (parser_bottom G1) = parserHFS_conf_history cb")
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     prefer 2
     apply(rule parserHFS_history_equals_removed_append_overhead)
         apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
         apply(force)
        apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     apply(fold parserHFS_string_state_def)
     apply(subgoal_tac "\<exists>ei ci'. (parserHFS_to_parserS_derivation d2) 0 = Some (pair ei ci')")
      apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
      apply(subgoal_tac "\<exists>ej cj'. (parserHFS_to_parserS_derivation d2) i = Some (pair ej cj')")
       apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
       apply(clarsimp)
       apply(rule parserHFS_to_parserS_derivation_reflects_string_state_delta)
              apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
              apply(force)
             apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
             apply(force)
            apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
            apply(force)
           apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
           apply(force)
          apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
          apply(force)
         apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
         prefer 2
         apply(force)
        apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
        prefer 2
        apply(simp add: parserHFS_to_parserS_derivation_def)
       apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
       apply(simp add: parserS_string_state_def)
      apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
      apply(simp add: parserHFS_to_parserS_derivation_def)
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
    apply(rule_tac
      t="parserHFS_conf_history cb"
      and s="v @ butlast_if_match (take (parser_fixed_input_length_recN d2 i) (parserHFS_string_state cb)) (parser_bottom G1)"
      in ssubst)
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
    apply(thin_tac "v @ butlast_if_match (take (parser_fixed_input_length_recN d2 i) (parserHFS_string_state cb)) (parser_bottom G1) = parserHFS_conf_history cb")
    apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) i"
      and s="parser_fixed_input_length_recN d2 i"
      in ssubst)
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     apply (metis parserHFS.derivation_initial_is_derivation parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
    apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
    apply(simp add: parserHFS_string_state_def)
    apply(rule_tac
      t="parserHFS_conf_scheduler cb"
      and s="parserS_conf_scheduler c'"
      in ssubst)
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     apply(simp add: parserHFS_to_parserS_derivation_def)
     apply(clarsimp)
    apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
    apply(rule butlast_if_match_take)
    apply(subgoal_tac "c' \<in> parserS_configurations G1")
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     apply(simp add: parserS_configurations_def)
     apply(clarsimp)
    apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
    apply(rule_tac
      d="parserHFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     apply(rule parserS.derivation_initial_belongs)
      apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
     apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
    apply(rename_tac G1 d2 x c c' i e v ea ca cb)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c c' i e v)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
   apply(clarsimp)
   apply(rename_tac G1 d2 x c i e v ca)(*strict*)
   apply(case_tac "d2 0")
    apply(rename_tac G1 d2 x c i e v ca)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i e v ca a)(*strict*)
   apply(case_tac a)
   apply(rename_tac G1 d2 x c i e v ca a option b)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c c' i e v)(*strict*)
  apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(case_tac "d2 i")
   apply(rename_tac G1 d2 x c c' i e v)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c c' i e v a)(*strict*)
  apply(case_tac a)
  apply(rename_tac G1 d2 x c c' i e v a option b)(*strict*)
  apply(force)
  done

lemma parserS_vs_parserHFS_inst_AX_unAX_marked_effect_id2: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o2. o2 \<in> parserHFS_unmarked_effect G1 d2 \<longrightarrow> o2 \<in> parserS_unmarked_effect G1 (parserHFS_to_parserS_derivation d2)))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o2 x)(*strict*)
  apply(simp add: parserS_unmarked_effect_def parserHFS_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x i e c)(*strict*)
   apply(subgoal_tac "\<exists>c. parserHFS_to_parserS_derivation d2 0 = Some (pair None c)")
    apply(rename_tac G1 d2 x i e c)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
    apply(rule_tac
      x="cb"
      in exI)
    apply(rule_tac
      x="i"
      in exI)
    apply(clarsimp)
    apply(subgoal_tac "\<exists>w. parserS_string_state ca = w @ parserS_string_state cb")
     apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
     prefer 2
     apply(rule_tac
      d="parserHFS_to_parserS_derivation d2"
      and j="i"
      in parserS.derivation_monotonically_dec)
          apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
          apply(force)
         apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
         apply(force)
        apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
        apply(rule parserS.derivation_initial_belongs)
         apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
         apply(force)
        apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
        apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
       apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
       apply(rule parserS.derivation_initial_is_derivation)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x i e c ea ca cb)(*strict*)
    apply(clarsimp)
    apply(rename_tac G1 d2 x i e c ea ca cb w)(*strict*)
    apply(rule_tac
      x="w"
      in exI)
    apply(simp add: parserS_string_state_def)
    apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
     apply(rename_tac G1 d2 x i e c ea ca cb w)(*strict*)
     apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
      apply(rename_tac G1 d2 x i e c ea ca cb w)(*strict*)
      apply(clarsimp)
      apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
      apply(subgoal_tac "w @ butlast_if_match (take (parser_fixed_input_length_recN d2 i) (parserHFS_conf_scheduler c)) (parser_bottom G1) = parserHFS_conf_history c")
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       prefer 2
       apply(rule parserHFS_history_equals_removed_append_overhead)
           apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
           apply(force)
          apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
          apply(force)
         apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
         apply(force)
        apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       apply(fold parserHFS_string_state_def)
       apply(rule parserHFS_to_parserS_derivation_reflects_string_state_delta)
              apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
              apply(force)
             apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
             apply(force)
            apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
            apply(force)
           apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
           apply(force)
          apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
          apply(force)
         apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
         prefer 2
         apply(force)
        apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
        prefer 2
        apply(simp add: parserHFS_to_parserS_derivation_def)
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       apply(simp add: parserS_string_state_def)
      apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
      apply(rule_tac
      t="parserHFS_conf_history c"
      and s="w @ butlast_if_match (take (parser_fixed_input_length_recN d2 i) (parserHFS_string_state c)) (parser_bottom G1)"
      in ssubst)
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       apply(clarsimp)
      apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
      apply(thin_tac "w @ butlast_if_match (take (parser_fixed_input_length_recN d2 i) (parserHFS_string_state c)) (parser_bottom G1) = parserHFS_conf_history c")
      apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      t="parser_fixed_input_length_recN (parserHFS_to_parserS_derivation d2) i"
      and s="parser_fixed_input_length_recN d2 i"
      in ssubst)
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       apply (metis parserHFS.derivation_initial_is_derivation parserHFS_to_parserS_derivation_preserves_parser_fixed_input_length_recN)
      apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
      apply(simp add: parserHFS_string_state_def)
      apply(rule_tac
      t="parserHFS_conf_scheduler c"
      and s="parserS_conf_scheduler cb"
      in ssubst)
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       apply(simp add: parserHFS_to_parserS_derivation_def)
       apply(clarsimp)
      apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
      apply(rule butlast_if_match_take)
      apply(subgoal_tac "cb \<in> parserS_configurations G1")
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       apply(simp add: parserS_configurations_def)
       apply(clarsimp)
      apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
      apply(rule_tac
      d="parserHFS_to_parserS_derivation d2"
      in parserS.belongs_configurations)
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       apply(rule parserS.derivation_initial_belongs)
        apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
       apply (metis parserHFS_to_parserS_derivation_preserves_derivation_initial)
      apply(rename_tac G1 d2 x i e c ea ca cb w cc)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x i e c ea ca cb w)(*strict*)
     apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(rename_tac G1 d2 x i e c ea ca cb w)(*strict*)
    apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(case_tac "d2 0")
     apply(rename_tac G1 d2 x i e c ea ca cb w)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x i e c ea ca cb w a)(*strict*)
    apply(case_tac a)
    apply(rename_tac G1 d2 x i e c ea ca cb w a option b)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c)(*strict*)
   apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
    apply(rename_tac G1 d2 x i e c)(*strict*)
    apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(case_tac "d2 0")
     apply(rename_tac G1 d2 x i e c)(*strict*)
     apply(clarsimp)
    apply(rename_tac G1 d2 x i e c a)(*strict*)
    apply(case_tac a)
    apply(rename_tac G1 d2 x i e c a option b)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c)(*strict*)
   apply(rule parserHFS.some_position_has_details_at_0)
   apply(rule parserHFS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(simp add: parserHFS_to_parserS_derivation_def)
  done

lemma parserS_vs_parserHFS_inst_AX_marked_effect_id1: "
  (\<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o1. o1 \<in> parserS_marked_effect G1 (parserHFS_to_parserS_derivation d2) \<longrightarrow> parserS_marking_condition G1 (parserHFS_to_parserS_derivation d2) \<longrightarrow> o1 \<in> parserHFS_marked_effect G1 d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o1 x)(*strict*)
  apply(simp add: parserS_marked_effect_def parserHFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c)(*strict*)
  apply(simp add: parserS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x c i e ca)(*strict*)
   prefer 2
   apply(simp add: parserHFS_to_parserS_derivation_def)
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
   apply(rule parserHFS.some_position_has_details_at_0)
   apply(rule parserHFS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="ea"
      in exI)
  apply(rule_tac
      x="cc"
      in exI)
  apply(clarsimp)
  apply(rule propSym)
  apply(rule context_conjI)
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   apply(simp add: parserS_marking_configurations_def)
   apply(simp add: parserHFS_marking_configurations_def)
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
     apply(simp add: parserHFS_to_parserS_derivation_def)
     apply(clarsimp)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(simp add: parserHFS_to_parserS_derivation_def)
   apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
   apply(rule conjI)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(simp add: parserHFS_to_parserS_derivation_def)
    apply(clarsimp)
   apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
   apply(rule_tac
      d="d2"
      in parserHFS.belongs_configurations)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(rule parserHFS.derivation_initial_belongs)
     apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i e ca ea cb cc f w)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler c"
      and s="parserHFS_conf_scheduler cb"
      in ssubst)
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(subgoal_tac "parserHFS_conf_scheduler cc = [parser_bottom G1]")
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   prefer 2
   apply(simp add: parserHFS_marking_configurations_def)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state cb = w @ parserHFS_string_state cc")
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in parserHFS.derivation_monotonically_dec)
        apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x c i e ca ea cb cc)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x c i e ca ea cb cc w)(*strict*)
  apply(simp add: parserHFS_string_state_def)
  apply(rule_tac
      t="parserHFS_conf_history cc"
      and s="w @ butlast_if_match (take (parser_fixed_input_length_recN d2 i) (parserHFS_conf_scheduler cc)) (parser_bottom G1)"
      in subst)
   apply(rename_tac G1 d2 x c i e ca ea cb cc w)(*strict*)
   defer
   apply(clarsimp)
   apply(case_tac "parser_fixed_input_length_recN d2 i")
    apply(rename_tac G1 d2 x c i e ca ea cb cc w)(*strict*)
    apply(clarsimp)
    apply(simp add: butlast_if_match_def)
   apply(rename_tac G1 d2 x c i e ca ea cb cc w nat)(*strict*)
   apply(clarsimp)
   apply(simp add: butlast_if_match_def)
  apply(rename_tac G1 d2 x c i e ca ea cb cc w)(*strict*)
  apply(rule parserHFS_history_equals_removed_append_overhead)
      apply(rename_tac G1 d2 x c i e ca ea cb cc w)(*strict*)
      apply(force)+
  done

lemma parserHFS_history_does_not_change_if_rhs_can_not_change: "
  valid_parser G
  \<Longrightarrow> parserHFS.derivation G d
  \<Longrightarrow> parserHFS.belongs G d
  \<Longrightarrow> d i = Some (pair ei ci)
  \<Longrightarrow> d j = Some (pair ej cj)
  \<Longrightarrow> i\<le>j
  \<Longrightarrow> parserHFS_conf_scheduler ci = [parser_bottom G]
  \<Longrightarrow> parserHFS_conf_scheduler cj = [parser_bottom G]
  \<Longrightarrow> parserHFS_conf_history ci = parserHFS_conf_history cj"
  apply(induct "j-i" arbitrary: i ei ci)
   apply(rename_tac i ei ci)(*strict*)
   apply(clarsimp)
  apply(rename_tac x i ei ci)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="Suc i"
      in meta_allE)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> parserHFS_step_relation G c1 e2 c2")
   apply(rename_tac x i ei ci)(*strict*)
   prefer 2
   apply(rule_tac
      m="j"
      in parserHFS.step_detail_before_some_position)
     apply(rename_tac x i ei ci)(*strict*)
     apply(force)
    apply(rename_tac x i ei ci)(*strict*)
    apply(force)
   apply(rename_tac x i ei ci)(*strict*)
   apply(force)
  apply(rename_tac x i ei ci)(*strict*)
  apply(clarsimp)
  apply(rename_tac x i ei ci e2 c2)(*strict*)
  apply(erule_tac
      x="Some e2"
      in meta_allE)
  apply(erule_tac
      x="c2"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac x i ei ci e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i ei ci e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i ei ci e2 c2)(*strict*)
   apply(force)
  apply(rename_tac x i ei ci e2 c2)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x i ei ci e2 c2)(*strict*)
   apply(subgoal_tac "valid_parser_step_label G e2")
    apply(rename_tac x i ei ci e2 c2)(*strict*)
    prefer 2
    apply(simp add: parserHFS_step_relation_def valid_parser_def)
   apply(rename_tac x i ei ci e2 c2)(*strict*)
   apply(simp add: parserHFS_step_relation_def valid_parser_step_label_def)
   apply(clarify)
   apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd)(*strict*)
   apply(case_tac "rule_rpop e2")
    apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd)(*strict*)
    apply (metis Nil_is_append_conv parserHFS_string_state_def self_append_conv2)
   apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
   apply(subgoal_tac "list=[]")
    apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
    apply(subgoal_tac "xc=[]")
     apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
     apply(clarify)
     apply (metis ConsApp valid_parser_rules_rhs_gets_shorter parser_step_labels_def append_Nil append_Nil2 dropPrecise drop_Nil drop_Suc_Cons drop_distrib_append length_Suc)
    apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
    apply (metis ConsApp drop_append append_Nil drop_Nil drop_Suc_Cons)
   apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
   apply (metis drop_append append_Cons append_Nil2 drop_Nil drop_Suc_Cons eq_Nil_appendI parserHFS_string_state_def)
  apply(rename_tac x i ei ci e2 c2)(*strict*)
  apply(subgoal_tac "valid_parser_step_label G e2")
   apply(rename_tac x i ei ci e2 c2)(*strict*)
   prefer 2
   apply(simp add: parserHFS_step_relation_def valid_parser_def)
  apply(rename_tac x i ei ci e2 c2)(*strict*)
  apply(simp add: parserHFS_step_relation_def valid_parser_step_label_def)
  apply(clarify)
  apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd)(*strict*)
  apply(case_tac "rule_rpop e2")
   apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd)(*strict*)
   apply (metis set_simps(1) append_Nil2 butlast_if_match_direct2_prime drop_Nil emptyE)
  apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
  apply(subgoal_tac "list=[]")
   apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
   apply(subgoal_tac "xc=[]")
    apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
    apply(clarify)
    apply (metis append_Nil2 butlast_if_match_direct drop_Nil self_append_conv2)
   apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
   apply (metis append_Cons length_1_context_empty parserHFS_string_state_def self_append_conv2)
  apply(rename_tac x i ei ci e2 c2 k xa w xb xc y xd a list)(*strict*)
  apply (metis append_Cons append_Nil2 dropPrecise drop_Nil drop_Suc_Cons self_append_conv2)
  done

lemma parserS_vs_parserHFS_inst_AX_marked_effect_id2: "
  \<forall>G1 d2. valid_parser G1 \<and> parserHFS.derivation_initial G1 d2 \<and> Ex (maximum_of_domain d2) \<longrightarrow> (\<forall>o2. o2 \<in> parserHFS_marked_effect G1 d2 \<longrightarrow> parserHFS_marking_condition G1 d2 \<longrightarrow> o2 \<in> parserS_marked_effect G1 (parserHFS_to_parserS_derivation d2))"
  apply(clarsimp)
  apply(rename_tac G1 d2 o2 x)(*strict*)
  apply(simp add: parserS_marked_effect_def parserHFS_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c)(*strict*)
  apply(simp add: parserHFS_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ia ea ca)(*strict*)
  apply(subgoal_tac "\<exists>e c. parserHFS_to_parserS_derivation d2 i = Some (pair e c)")
   apply(rename_tac G1 d2 x i e c ia ea ca)(*strict*)
   prefer 2
   apply(simp add: parserHFS_to_parserS_derivation_def)
  apply(rename_tac G1 d2 x i e c ia ea ca)(*strict*)
  apply(subgoal_tac "\<exists>c. d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x i e c ia ea ca)(*strict*)
   prefer 2
   apply(rule parserHFS.some_position_has_details_at_0)
   apply(rule parserHFS.derivation_initial_is_derivation)
   apply(force)
  apply(rename_tac G1 d2 x i e c ia ea ca)(*strict*)
  apply(subgoal_tac "\<exists>c. parserHFS_to_parserS_derivation d2 0 = Some (pair None c)")
   apply(rename_tac G1 d2 x i e c ia ea ca)(*strict*)
   prefer 2
   apply(simp add: parserHFS_to_parserS_derivation_def)
   apply(case_tac "d2 0")
    apply(rename_tac G1 d2 x i e c ia ea ca)(*strict*)
    apply(clarsimp)
   apply(rename_tac G1 d2 x i e c ia ea ca a)(*strict*)
   apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ia ea ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
  apply(rule_tac
      t="parserS_conf_scheduler cc"
      and s="parserHFS_conf_scheduler cb"
      in ssubst)
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
   apply(simp add: parserHFS_to_parserS_derivation_def)
   apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
  apply(subgoal_tac "parserHFS_conf_scheduler ca = [parser_bottom G1]")
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
   prefer 2
   apply(simp add: parserHFS_marking_configurations_def)
  apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
  apply(subgoal_tac "\<exists>w. parserHFS_string_state cb = w @ parserHFS_string_state ca")
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
   prefer 2
   apply(rule_tac
      d="d2"
      in parserHFS.derivation_monotonically_dec)
        apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
        apply(force)
       apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
      apply(rule parserHFS.derivation_initial_belongs)
       apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
     apply(simp add: parserHFS.derivation_initial_def)
    apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
   apply(force)
  apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd")(*strict*)
  apply(clarsimp)
  apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
  apply(simp add: parserHFS_string_state_def)
  apply(rule_tac
      t="parserHFS_conf_history c"
      and s="parserHFS_conf_history ca"
      in ssubst)
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
   defer
   apply(rule_tac
      t="parserHFS_conf_history ca"
      and s="w @ butlast_if_match (take (parser_fixed_input_length_recN d2 ia) (parserHFS_conf_scheduler ca)) (parser_bottom G1)"
      in subst)
    apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
    apply(rule parserHFS_history_equals_removed_append_overhead)
        apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
   apply(clarsimp)
   apply(case_tac "parser_fixed_input_length_recN d2 ia")
    apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
    apply(clarsimp)
    apply(simp add: butlast_if_match_def)
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w nat)(*strict*)
   apply(clarsimp)
   apply(simp add: butlast_if_match_def)
  apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
  apply(case_tac "i\<le>ia")
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
   apply(rule_tac
      d="d2"
      in parserHFS_history_does_not_change_if_rhs_can_not_change)
          apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
          apply(force)
         apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
         apply(rule parserHFS.derivation_initial_is_derivation)
         apply(force)
        apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
        apply(rule parserHFS.derivation_initial_belongs)
         apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
         apply(force)
        apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
    apply(simp add: parserHFS_marking_configurations_def)
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
   apply(simp add: parserHFS_marking_configurations_def)
  apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
  apply(rule sym)
  apply(rule_tac
      d="d2"
      in parserHFS_history_does_not_change_if_rhs_can_not_change)
         apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
         apply(force)
        apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
        apply(rule parserHFS.derivation_initial_is_derivation)
        apply(force)
       apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
       apply(rule parserHFS.derivation_initial_belongs)
        apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
        apply(force)
       apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
       apply(force)
      apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
      apply(force)
     apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
     apply(force)
    apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
    apply(force)
   apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
   apply(simp add: parserHFS_marking_configurations_def)
  apply(rename_tac G1 d2 x i e c ia ea ca eb cb cc "cd" w)(*strict*)
  apply(simp add: parserHFS_marking_configurations_def)
  done

lemma parserS_vs_parserHFS_inst_AX_step_labels_unique1: "
  (\<forall>G1 G2 e1 e21 e22. valid_parser G1 \<and> G1 = G2 \<longrightarrow> e1 \<in> parser_step_labels G1 \<longrightarrow> e21 \<in> parser_step_labels G2 \<longrightarrow> e22 \<in> parser_step_labels G2 \<longrightarrow> e1 = e21 \<and> e1 \<in> parser_rules G1 \<longrightarrow> e1 = e22 \<and> e1 \<in> parser_rules G1 \<longrightarrow> e21 = e22)"
  apply(clarsimp)
  done

lemma parserS_vs_parserHFS_inst_AX_step_labels_unique2: "
  (\<forall>G1 G2 e11 e12 e2. valid_parser G1 \<and> G1 = G2 \<longrightarrow> e11 \<in> parser_step_labels G1 \<longrightarrow> e12 \<in> parser_step_labels G1 \<longrightarrow> e2 \<in> parser_step_labels G2 \<longrightarrow> e11 = e2 \<and> e11 \<in> parser_rules G1 \<longrightarrow> e12 = e2 \<and> e12 \<in> parser_rules G1 \<longrightarrow> e11 = e12)"
  apply(clarsimp)
  done

lemma parserS_vs_parserHFS_inst_AX_step_labels_exists1: "
  (\<forall>G1 G2 e1. valid_parser G1 \<and> G1 = G2 \<longrightarrow> e1 \<in> parser_step_labels G1 \<longrightarrow> (\<exists>e2\<in> parser_step_labels G2. e1 = e2 \<and> e1 \<in> parser_rules G1))"
  apply(clarsimp)
  apply(rename_tac G1 e1)(*strict*)
  apply(simp add: parser_step_labels_def)
  done

lemma parserS_vs_parserHFS_inst_AX_step_labels_exists2: "
  (\<forall>G1 G2 e2. valid_parser G1 \<and> G1 = G2 \<longrightarrow> e2 \<in> parser_step_labels G2 \<longrightarrow> (\<exists>e1\<in> parser_step_labels G1. e1 = e2 \<and> e1 \<in> parser_rules G1))"
  apply(clarsimp)
  apply(rename_tac G1 e2)(*strict*)
  apply(simp add: parser_step_labels_def)
  done

lemma parserS_vs_HFS_inst_ATS_Bisimulation_Derivation_Strong2_axioms: "
  ATS_Bisimulation_Derivation_Strong2_axioms valid_parser parserS_initial_configurations
     parser_step_labels parserS_step_relation parserS_marking_condition parserS_marked_effect
     parserS_unmarked_effect parser_unfixed_schedulers right_quotient_word (@)
     parser_unfixed_scheduler_extendable parserS_set_unfixed_scheduler_DB
     parserS_get_unfixed_scheduler_DB parserS_get_fixed_scheduler_DB valid_parser
     parserHFS_initial_configurations parser_step_labels parserHFS_step_relation
     parserHFS_marking_condition parserHFS_marked_effect parserHFS_unmarked_effect
     parser_unfixed_schedulers right_quotient_word (@) parser_unfixed_scheduler_extendable
     parserHFS_set_unfixed_scheduler_DB parserHFS_get_unfixed_scheduler_DB
     parserHFS_get_fixed_scheduler_DB (\<lambda>G1 G2. valid_parser G1 \<and> G1 = G2)
     (\<lambda>G1 G2 o1 o2. G1 = G2 \<and> o1 = o2) (\<lambda>G1 G2 e1 e2. e1 = e2 \<and> e1 \<in> parser_rules G1)
     (\<lambda>G1 G2 d1 d2.
         valid_parser G1 \<and>
         G1 = G2 \<and>
         parserHFS.derivation_initial G2
          d2 \<and>
         Ex (maximum_of_domain d2) \<and> parserHFS_to_parserS_derivation d2 = d1) "
  apply(simp add: ATS_Bisimulation_Derivation_Strong2_axioms_def)
  apply (simp add: parser_step_labels_def parserS_vs_parserHFS_inst_AX_accept_id1 parserS_vs_parserHFS_inst_AX_accept_id2 parserS_vs_parserHFS_inst_AX_unAX_marked_effect_id1 parserS_vs_parserHFS_inst_AX_unAX_marked_effect_id2 parserS_vs_parserHFS_inst_AX_marked_effect_id1 parserS_vs_parserHFS_inst_AX_marked_effect_id2 parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_replace_and_schedF1  parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_replace_and_schedF2 parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_crop1 parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_crop2 parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_unfixed_scheduler_extendable1 parserS_vs_parserHFS_inst_AX_bisimulation_compatible_with_unfixed_scheduler_extendable2 parserS_vs_parserHFS_inst_AX_initial_contained1 parserS_vs_parserHFS_inst_AX_initial_contained2 parserS_vs_parserHFS_inst_AX_on_derivation_initial1 parserS_vs_parserHFS_inst_AX_on_finite1 parserS_vs_parserHFS_inst_AX_equal_length parserS_vs_parserHFS_inst_AX_simulate12 parserS_vs_parserHFS_inst_AX_simulate21)
  done

interpretation "parserS_vs_parserHFS" : ATS_Bisimulation_Derivation_Strong2
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
  "parserHFS_configurations"
  (* initial_configurations2 *)
  "parserHFS_initial_configurations"
  (* step_labels2 *)
  "parser_step_labels"
  (* step_relation2 *)
  "parserHFS_step_relation"
  (* effects2 *)
  "parser_markers"
  (* marking_condition2 *)
  "parserHFS_marking_condition"
  (* marked_effect2 *)
  "parserHFS_marked_effect"
  (* unmarked_effect2 *)
  "parserHFS_unmarked_effect"
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
  "parserHFS_get_scheduler"
  (* join_fixed_scheduler_unfixed_scheduler2 *)
  "append"
  (* extend_scheduler2 *)
  "append"
  "parserHFS_set_unfixed_scheduler_DB"
  "parserHFS_get_unfixed_scheduler_DB"
  "parserHFS_get_fixed_scheduler_DB"
  "\<lambda>G1 G2. valid_parser G1 \<and> G1=G2"
  "\<lambda>G1 G2 o1 o2. G1=G2 \<and> o1=o2"
  "\<lambda>G1 G2 e1 e2. e1=e2 \<and> e1 \<in> parser_rules G1"
  "\<lambda>G1 G2 d1 d2. (valid_parser G1)
  \<and> (G1=G2)
  \<and> parserHFS.derivation_initial G2 d2
  \<and> (\<exists>n. maximum_of_domain d2 n)
  \<and> parserHFS_to_parserS_derivation d2 = d1"
  apply(simp add: LOCALE_DEFS parserHFS_interpretations0 parserS_interpretations LOCALE_DEFS)
  apply(simp add: parserS_vs_HFS_inst_ATS_Bisimulation_Derivation_Strong2_axioms)
  done

theorem parserS_vs_parserHFS_Nonblockingness_and_lang_transfer: "
  valid_parser G
  \<Longrightarrow> (parserHFS.Nonblockingness_linear_DB G \<longleftrightarrow> parserS.Nonblockingness_linear_DB G)
  \<and> parserHFS.unmarked_language G = parserS.unmarked_language G
  \<and> parserHFS.marked_language G = parserS.marked_language G"
  apply(rule conjI)
   apply (metis parserS_vs_parserHFS.Nonblockingness_translation1 parserS_vs_parserHFS.Nonblockingness_translation2)
  apply(rule conjI)
   apply(rule order_antisym)
    apply(rule_tac
      t="parserHFS.unmarked_language G"
      and s="parserHFS.finite_unmarked_language G"
      in ssubst)
     apply (metis parserHFS.AX_unmarked_language_finite)
    apply (metis parserS_vs_parserHFS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation2 subsetI)
   apply(rule_tac
      t="parserS.unmarked_language G"
      and s="parserS.finite_unmarked_language G"
      in ssubst)
    apply (metis parserS.AX_unmarked_language_finite)
   apply (metis parserS_vs_parserHFS.ATS_Bisimulation_Derivation_Strong1_unmarked_language_translation1 subsetI)
  apply(rule order_antisym)
   apply(rule_tac
      t="parserHFS.marked_language G"
      and s="parserHFS.finite_marked_language G"
      in ssubst)
    apply (metis parserHFS.AX_marked_language_finite)
   apply (metis parserS_vs_parserHFS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation2 subsetI)
  apply(rule_tac
      t="parserS.marked_language G"
      and s="parserS.finite_marked_language G"
      in ssubst)
   apply (metis parserS.AX_marked_language_finite)
  apply (metis parserS_vs_parserHFS.ATS_Bisimulation_Derivation_Strong1_marked_language_translation1 subsetI)
  done

theorem parserS_vs_parserHFS_is_forward_deterministic_accessible_preserved: "
  valid_parser G
  \<Longrightarrow> parserS.is_forward_deterministic_accessible G
  \<Longrightarrow> parserHFS.is_forward_deterministic_accessible G"
  apply(simp add: parserS.is_forward_deterministic_accessible_def parserHFS.is_forward_deterministic_accessible_def)
  apply(rule conjI)
   apply(rule parserHFS_is_forward_target_deterministic_accessible)
   apply(force)
  apply(clarsimp)
  apply (metis parserS_vs_parserHFS.preserve_FEdetermR1)
  done

end
