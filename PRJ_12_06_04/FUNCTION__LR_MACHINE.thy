section {*FUNCTION\_\_LR\_MACHINE*}
theory
  FUNCTION__LR_MACHINE

imports
  PRJ_12_06_04__ENTRY

begin

record ('nonterminal, 'event) F_LR_MACHINE__fp_one_ARG =
  funlrml_arg_grammar :: "('nonterminal, 'event) cfg"
  funlrml_arg_la_length :: "nat"
  funlrml_arg_found_edges :: "(('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set"
  funlrml_arg_found_states :: "('nonterminal, 'event) DT_cfg_item set set"
  funlrml_arg_todo_states :: "('nonterminal, 'event) DT_cfg_item set set"

definition F_LR_MACHINE__fp_one_TERM_ARGS_TEST :: "
  ('nonterminal, 'event) cfg
    \<times> (('nonterminal, 'event) DT_first_function)
    \<times> nat
    \<times> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
  \<Rightarrow> bool"
  where
    "F_LR_MACHINE__fp_one_TERM_ARGS_TEST A \<equiv>
  (\<lambda>(G, F, k, E, V, S).
      valid_cfg G
      \<and> cfgSTD_first_compatible F k
      \<and> finite E
      \<and> finite V
      \<and> finite S
      \<and> (\<forall>e \<in> E.
            edge_src e \<in> V
            \<and> edge_push e = [0]
            \<and> edge_pop e = [0]
            \<and> V \<inter> S = {}
            \<and> edge_trg e \<in> V \<union> S
            \<and> (\<exists>v \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G).
                  edge_event e = Some v))
      \<and> (\<forall>q \<in> V. \<forall>I \<in> q. valid_item G k I)
      \<and> (\<forall>q \<in> S. \<forall>I \<in> q. valid_item G k I)
      \<and> (\<forall>q \<in> V \<union> S.
            \<exists>w.
              set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
              \<and> q = valid_item_set G k w))
  A"

definition F_LR_MACHINE_TRANSFER_01 :: "
  ('nonterminal, 'event) cfg
    \<times> (('nonterminal, 'event) DT_first_function)
    \<times> nat
    \<times> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
  \<Rightarrow> bool"
  where
    "F_LR_MACHINE_TRANSFER_01 A \<equiv>
  (\<lambda>(G, F, k, E, V, S).
      finite S
      \<and> valid_cfg G
      \<longrightarrow> finite (F_LR_MACHINE__one G F k S))
  A"

definition F_LR_MACHINE_TRANSFER_02 :: "
  ('nonterminal, 'event) cfg
    \<times> (('nonterminal, 'event) DT_first_function)
    \<times> nat
    \<times> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
  \<Rightarrow> bool"
  where
    "F_LR_MACHINE_TRANSFER_02 A \<equiv>
  (\<lambda>(G, F, k, E, V, S).
    \<forall>q \<in> S.
      \<forall>X \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G).
        \<lparr>edge_src = q,
          edge_event = Some X,
          edge_pop = [0],
          edge_push = [0],
          edge_trg = F_VALID_ITEM_SET_GOTO G F k X q\<rparr> \<in> (F_LR_MACHINE__one G F k S))
  A"

definition F_LR_MACHINE_TRANSFER_03 :: "
  ('nonterminal, 'event) cfg
    \<times> (('nonterminal, 'event) DT_first_function)
    \<times> nat
    \<times> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
  \<Rightarrow> bool"
  where
    "F_LR_MACHINE_TRANSFER_03 A \<equiv>
  (\<lambda>(G, F, k, E, V, S).
    \<forall>q \<in> V \<union> S.
      \<exists>w.
        set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
        \<and> q = valid_item_set G k w)
  A"

definition F_LR_MACHINE_TRANSFER :: "
  ('nonterminal, 'event) cfg
    \<times> (('nonterminal, 'event) DT_first_function)
    \<times> nat
    \<times> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
  \<Rightarrow> bool"
  where
    "F_LR_MACHINE_TRANSFER A \<equiv>
  F_LR_MACHINE_TRANSFER_01 A
  \<and> F_LR_MACHINE_TRANSFER_02 A
  \<and> F_LR_MACHINE_TRANSFER_03 A"

definition F_LR_MACHINE_mod_args :: "
  (('nonterminal, 'event) cfg
    \<times> (('nonterminal, 'event) DT_first_function)
    \<times> nat
    \<times> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
    \<times> (('nonterminal, 'event) DT_cfg_item set set))
  \<Rightarrow>   (('nonterminal, 'event) cfg
    \<times> (('nonterminal, 'event) DT_first_function)
    \<times> nat
    \<times> (('nonterminal, 'event) DT_cfg_item set, ('nonterminal, 'event) DT_two_elements, nat) epda_step_label set
    \<times> (('nonterminal, 'event) DT_cfg_item set set)
    \<times> (('nonterminal, 'event) DT_cfg_item set set))"
  where
    "F_LR_MACHINE_mod_args A \<equiv>
  (\<lambda>(G, F, k, E, V, S).
    (G, F, k, E \<union> F_LR_MACHINE__one G F k S, V \<union> S, (edge_trg ` (F_LR_MACHINE__one G F k S))-(V \<union> S)))
  A"

lemma F_LR_MACHINE__one_finite: "
  valid_cfg G
  \<Longrightarrow> finite S
  \<Longrightarrow> finite (F_LR_MACHINE__one G F k S)"
  apply(simp add: F_LR_MACHINE__one_def)
  apply(rule finite_imageI)
  apply(rule finite_cartesian_product)
   apply(force)
  apply(rule finite_two_elements_construct_domain)
   apply(simp add: valid_cfg_def)
  apply(simp add: valid_cfg_def)
  done

lemma F_LR_MACHINE_TRANSFER_AT_kleene_starT: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, {}, {}, S)
  \<Longrightarrow> F_LR_MACHINE_TRANSFER (G, F, k, {}, {}, S)"
  apply(simp add: F_LR_MACHINE_TRANSFER_def)
  apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def F_LR_MACHINE_TRANSFER_01_def F_LR_MACHINE_TRANSFER_02_def F_LR_MACHINE_TRANSFER_03_def)
  apply(rule conjI)
   apply(rule F_LR_MACHINE__one_finite)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rename_tac q X)(*strict*)
  apply(simp add: F_LR_MACHINE__one_def)
  apply(rule inMap)
  apply(clarsimp)
  done

lemma F_LR_MACHINE__one_preserves_F_LR_MACHINE__fp_one_TERM_ARGS_TEST: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST A
  \<Longrightarrow> F_LR_MACHINE__fp_one_TERM_ARGS_TEST (F_LR_MACHINE_mod_args A)"
  apply(case_tac A)
  apply(rename_tac a b c d e f)(*strict*)
  apply(rename_tac G F k E V S)
  apply(rename_tac G F k E V S)(*strict*)
  apply(case_tac "F_LR_MACHINE__one G F k S = {}")
   apply(rename_tac G F k E V S)(*strict*)
   apply(clarsimp)
   apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
   apply(rename_tac G F k E V S q x)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def F_LR_MACHINE_mod_args_def)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac G F k E V S)(*strict*)
   apply(simp add: F_LR_MACHINE__one_def)
   apply(rule finite_imageI)
   apply(rule finite_cartesian_product)
    apply(rename_tac G k E V S)(*strict*)
    apply(force)
   apply(rename_tac G k E V S)(*strict*)
   apply(rule finite_two_elements_construct_domain)
    apply(rename_tac G k E V S)(*strict*)
    apply(simp add: valid_cfg_def)
   apply(rename_tac G k E V S)(*strict*)
   apply(simp add: valid_cfg_def)
  apply(rename_tac G F k E V S)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac G F k E V S)(*strict*)
   apply(rule finite_imageI)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G k E V S)(*strict*)
   apply(clarsimp)
   apply(rename_tac G k E V S e)(*strict*)
   apply(simp add: F_LR_MACHINE__one_def)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac G k E V S e)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="e"
      in ballE)
     apply(rename_tac G k E V S e)(*strict*)
     apply(clarsimp)
    apply(rename_tac G k E V S e)(*strict*)
    apply(clarsimp)
   apply(rename_tac G k E V S e)(*strict*)
   apply(clarsimp)
  apply(rename_tac G k E V S)(*strict*)
  apply(rule conjI)
   apply(rename_tac G k E V S)(*strict*)
   apply(clarsimp)
   apply(rename_tac G k E V S q x)(*strict*)
   apply(erule disjE)
    apply(rename_tac G k E V S q x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G k E V S q x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k E V S)(*strict*)
  apply(rule conjI)
   apply(clarsimp)
   apply(simp add: F_LR_MACHINE__one_def)
   apply(clarsimp)
   apply(erule_tac
      x="a"
      and A="S"
      and P="\<lambda>a. \<forall>x \<in> a. valid_item G k x"
      in ballE)
    prefer 2
    apply(clarsimp)
   apply(rule_tac
      S="a"
      in F_VALID_ITEM_SET_GOTO_preserves_item_set)
      apply(force)
     apply(rename_tac G k E V S xa a b)(*strict*)
     apply(force)
    apply(rename_tac G k E V S xa a b)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(simp add: F_LR_MACHINE__one_def)
  apply(clarsimp)
  apply(rename_tac G F k E V S q)(*strict*)
  apply(erule disjE)
   apply(rename_tac G F k E V S q)(*strict*)
   apply(erule_tac
      x="q"
      and A="V \<union> S"
      in ballE)
    apply(rename_tac G k E V S q)(*strict*)
    apply(force)
   apply(rename_tac G k E V S q)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S q)(*strict*)
  apply(erule disjE)
   apply(rename_tac G F k E V S q)(*strict*)
   apply(erule_tac
      x="q"
      and A="V \<union> S"
      in ballE)
    apply(rename_tac G F k E V S q)(*strict*)
    apply(force)
   apply(rename_tac G F k E V S q)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S q)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k E V S a b)(*strict*)
  apply(erule_tac
      x="a"
      and A="V \<union> S"
      in ballE)
   apply(rename_tac G F k E V S a b)(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k E V S b w)(*strict*)
   apply(rule_tac
      x="w@[b]"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac G F k E V S b w)(*strict*)
    prefer 2
    apply(rule sym)
    apply(rule Lemma6__26)
       apply(rename_tac G F k E V S b w)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac G F k E V S b w)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(force)
    apply(rename_tac G F k E V S b w)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rename_tac G F k E V S b w)(*strict*)
   apply(rule two_elements_construct_domain_append)
    apply(rename_tac G F k E V S b w)(*strict*)
    apply(force)
   apply(rename_tac G F k E V S b w)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S a b)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_termLem2: "
  F_LR_MACHINE__one G F k S \<noteq> {}
  \<Longrightarrow> F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> F_LR_MACHINE_mod_args (G, F, k, E, V, S) = (G, F', k, E', V', S')
  \<Longrightarrow> card ({x. edge_src x \<subseteq> Collect (valid_item G k) \<and> (\<exists>a \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G). edge_event x = Some a) \<and> edge_push x = [0] \<and> edge_pop x = [0] \<and> edge_trg x \<subseteq> Collect (valid_item G k)} - E') < card ({x. edge_src x \<subseteq> Collect (valid_item G k) \<and> (\<exists>a \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G). edge_event x = Some a) \<and> edge_push x = [0] \<and> edge_pop x = [0] \<and> edge_trg x \<subseteq> Collect (valid_item G k)} - E)"
  apply(rule psubset_card_mono)
   prefer 2
   apply(rule rev_subset)
    prefer 3
    apply(rule_tac
      B = "{x. edge_src x \<subseteq> Collect (valid_item G k) \<and> (\<exists>a \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G). edge_event x = Some a) \<and> edge_push x = [0] \<and> edge_pop x = [0] \<and> edge_trg x \<subseteq> Collect (valid_item G k)}"
      in finite_subset)
     apply(force)
    apply(rule_tac
      B = "(\<lambda>(s, r, po, pu, t). \<lparr>edge_src=s, edge_event=r, edge_pop=po, edge_push=pu, edge_trg=t\<rparr>) ` (Pow(Collect (valid_item G k)) \<times> (WrapInSome (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))) \<times> {[0]} \<times> {[0]} \<times> Pow(Collect (valid_item G k)))"
      in finite_subset)
     apply(clarsimp)
     apply(rename_tac x a)(*strict*)
     apply(rule inMap)
     apply(clarsimp)
     apply(case_tac x)
     apply(rename_tac x a edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
     apply(clarsimp)
     apply(rename_tac a edge_src edge_trg)(*strict*)
     apply(simp add: WrapInSome_def)
    apply(rule finite_imageI)
    apply(subgoal_tac "finite (Pow (Collect (valid_item G k)))")
     prefer 2
     apply(rule card_ge_0_finite)
     apply(rule_tac
      t="card (Pow (Collect (valid_item G k)))"
      and s="Suc (Suc 0) ^ card A" for A
      in ssubst)
      apply(rule card_Pow_SucSuc)
      apply(rule finite_ItemSet)
      apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
     apply(force)
    apply(rule finite_cartesian_product)
     apply(force)
    apply(rule finite_cartesian_product)
     apply(subgoal_tac "finite (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))")
      apply(simp add: WrapInSome_def)
     apply(rule finite_two_elements_construct_domain)
      apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def valid_cfg_def)
     apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def valid_cfg_def)
    apply(rule finite_cartesian_product)
     apply(force)
    apply(rule finite_cartesian_product)
     apply(force)
    apply(force)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>I \<in> (F_LR_MACHINE__one G F' k S). I\<notin> E")
    apply(force)
   apply(simp add: F_LR_MACHINE__one_def)
   apply(clarsimp)
   apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>x. x \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))")
    prefer 2
    apply(force)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>x \<in> S. True")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xa)(*strict*)
   apply(erule_tac
      x="xa"
      and A="V \<union> S"
      in ballE)
    apply(rename_tac x xa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(rule_tac
      x="xa"
      in bexI)
    apply(rename_tac x xa)(*strict*)
    apply(rule_tac
      x="x"
      in bexI)
     apply(rename_tac x xa)(*strict*)
     apply(case_tac "\<lparr>edge_src = xa, edge_event = Some x, edge_pop = [0], edge_push = [0], edge_trg = F_VALID_ITEM_SET_GOTO G F' k x xa\<rparr> \<in> E")
      apply(rename_tac x xa)(*strict*)
      apply(subgoal_tac "False")
       apply(rename_tac x xa)(*strict*)
       apply(force)
      apply(rename_tac x xa)(*strict*)
      apply(erule_tac
      x="\<lparr>edge_src = xa, edge_event = Some x, edge_pop = [0], edge_push = [0], edge_trg = F_VALID_ITEM_SET_GOTO G F' k x xa\<rparr>"
      in ballE)
       apply(rename_tac x xa)(*strict*)
       apply(clarsimp)
       apply(rename_tac x w)(*strict*)
       apply(force)
      apply(rename_tac x xa)(*strict*)
      apply(force)
     apply(rename_tac x xa)(*strict*)
     apply(force)
    apply(rename_tac x xa)(*strict*)
    apply(force)
   apply(rename_tac x xa)(*strict*)
   apply(force)
  apply(subgoal_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (F_LR_MACHINE_mod_args (G, F, k, E, V, S))")
   prefer 2
   apply(rule F_LR_MACHINE__one_preserves_F_LR_MACHINE__fp_one_TERM_ARGS_TEST)
   apply(force)
  apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def F_LR_MACHINE_mod_args_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="x"
      and P="\<lambda>x. (edge_src x \<in> V \<or> edge_src x \<in> S) \<and> edge_push x = [0] \<and> edge_pop x = [0] \<and> (edge_trg x \<in> V \<or> edge_trg x \<in> S \<or> edge_trg x \<in> edge_trg ` F_LR_MACHINE__one G F' k S \<and> edge_trg x \<notin> V \<and> edge_trg x \<notin> S) \<and> (\<exists>v \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G). edge_event x = Some v)"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(rule conjI)
   apply(rename_tac x v)(*strict*)
   apply(erule_tac
      P="edge_src x \<in> V"
      in disjE)
    apply(rename_tac x v)(*strict*)
    apply(clarsimp)
   apply(rename_tac x v)(*strict*)
   apply(clarsimp)
  apply(rename_tac x v)(*strict*)
  apply(clarsimp)
  apply(rename_tac x v xa)(*strict*)
  apply(erule_tac
      P="x \<in> E"
      in disjE)
   apply(rename_tac x v xa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac x v xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x v xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x v xa)(*strict*)
  apply(erule_tac
      P="edge_src x \<in> V"
      in disjE)
   apply(rename_tac x v xa)(*strict*)
   apply(clarsimp)
   apply(erule disjE)
    apply(rename_tac x v xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x v xa)(*strict*)
   apply(erule disjE)
    apply(rename_tac x v xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x v xa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="edge_trg x"
      and P="\<lambda>x. \<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> x = valid_item_set G k w"
      in ballE)
    apply(rename_tac x v xa)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac x v xa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x v xa w)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac x v xa w)(*strict*)
    apply(force)
   apply(rename_tac x v xa w)(*strict*)
   apply(force)
  apply(rename_tac x v xa)(*strict*)
  apply(clarsimp)
  apply(erule disjE)
   apply(rename_tac x v xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x v xa)(*strict*)
  apply(erule disjE)
   apply(rename_tac x v xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x v xa)(*strict*)
  apply(clarsimp)
  apply(simp add: F_LR_MACHINE__one_def)
  apply(clarsimp)
  apply(rename_tac v xa a)(*strict*)
  apply(erule_tac
      x="a"
      and A="V \<union> S"
      and P="\<lambda>a. \<forall>x \<in> a. valid_item G k x"
      in ballE)
   apply(rename_tac v xa a)(*strict*)
   apply(rule_tac
      S="a"
      in F_VALID_ITEM_SET_GOTO_preserves_item_set)
      apply(rename_tac v xa a)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac v xa a)(*strict*)
    apply(force)
   apply(rename_tac v xa a)(*strict*)
   apply(force)
  apply(rename_tac v xa a)(*strict*)
  apply(clarsimp)
  done

lemma F_LR_MACHINE__fp_one_Meta_Lift: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, {}, {}, S)
  \<Longrightarrow> (\<And>G F k E V S G' F' k' E' V' S'. F_LR_MACHINE_TRANSFER (G', F', k', {}, {}, S') \<longrightarrow> P G' F' k' S' (F_LR_MACHINE__fp_one G' F' k' {} {} S') \<Longrightarrow> F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S) \<Longrightarrow>  F_LR_MACHINE_mod_args (G, F, k, E, V, S) = (G', F', k', E', V', S') \<Longrightarrow> F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G', F', k', E', V', S') \<Longrightarrow> F_LR_MACHINE_TRANSFER (G, F, k, {}, {}, S) \<Longrightarrow> P G F k S (F_LR_MACHINE__fp_one G F k {} {} S))
  \<Longrightarrow> (\<And>G F k E V S. F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S) \<Longrightarrow> F_LR_MACHINE_TRANSFER (G, F, k, {}, {}, S) \<Longrightarrow> \<not> P G F k S (F_LR_MACHINE__fp_one G F k {} {} S) \<Longrightarrow> F_LR_MACHINE__one G F k S = {} \<Longrightarrow> False)
  \<Longrightarrow> P G F k S (F_LR_MACHINE__fp_one G F k {} {} S)"
  apply(subgoal_tac "(\<lambda>G F k E V S. F_LR_MACHINE_TRANSFER (G, F, k, E, V, S) \<longrightarrow> (P G F k S (F_LR_MACHINE__fp_one G F k {} {} S))) G F k {} {} S")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_LR_MACHINE_TRANSFER_AT_kleene_starT)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G, F, k, E, V, S). F_LR_MACHINE_TRANSFER (G, F, k, {}, {}, S) \<longrightarrow> (P G F k S (F_LR_MACHINE__fp_one G F k {} {} S))) (G, F, k, {}, {}, S)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G, F, k, E, V, S). F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)"
      and RECURSIVE_COND = "\<lambda>(G, F, k, E, V, S). F_LR_MACHINE__one G F k S \<noteq> {}"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G, F, k, E, V, S). (G, F, k, E \<union> (F_LR_MACHINE__one G F k S), V \<union> S, (edge_trg ` (F_LR_MACHINE__one G F k S))-(V \<union> S))"
      and MEASURE = "\<lambda>(G, F, k, E, V, S). card (((Collect (\<lambda>x. edge_src x \<subseteq> (Collect (\<lambda>x. valid_item G k x)) \<and> (\<exists>a \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)). edge_event x = Some a) \<and> edge_push x = [0] \<and> edge_pop x = [0] \<and> edge_trg x \<subseteq> (Collect (\<lambda>x. valid_item G k x))))) -E)"
      and TERM_FUN = "(\<lambda>(G, F, k, E, V, S). F_LR_MACHINE_TRANSFER (G, F, k, {}, {}, S) \<longrightarrow> (P G F k S (F_LR_MACHINE__fp_one G F k {} {} S)))"
      and y = "(G, F, k, {}, {}, S)"
      in partial_termination_wf)
      apply(fold F_LR_MACHINE_mod_args_def)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, {}, {}, S)")
      apply(rename_tac G F k E V S G' F' k' E' V' S')
      apply(rule_tac
      t="(G', F', k', E', V', S')"
      and s="F_LR_MACHINE_mod_args (G, F, k, E, V, S)"
      in ssubst)
       apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
       apply(force)
      apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
      apply(rule F_LR_MACHINE__one_preserves_F_LR_MACHINE__fp_one_TERM_ARGS_TEST)
      apply(force)
     apply(clarify)
     apply(rename_tac a aa ab ac b)(*strict*)
     apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, {}, {}, S)")
     apply(rename_tac G F k E V S)
     apply(rename_tac G F k E V S)(*strict*)
     apply(case_tac "F_LR_MACHINE_mod_args (G, F, k, E, V, S)")
     apply(rename_tac G F k E V S a b c d e)(*strict*)
     apply(rename_tac G F k E V S G' F' k' E' V' S')
     apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "G'=G \<and> k'=k")
      apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
      prefer 2
      apply(simp add: F_LR_MACHINE_mod_args_def)
     apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
     apply(clarsimp)
     apply(rename_tac G F k E V S E' V' S' F')(*strict*)
     apply(rule_tac
      S="S"
      and F="F"
      in F_LR_MACHINE_termLem2)
       apply(rename_tac G F k E V S E' V' S')(*strict*)
       apply(force)
      apply(rename_tac G F k E V S E' V' S')(*strict*)
      apply(force)
     apply(rename_tac G F k E V S E' V' S')(*strict*)
     apply(force)
    prefer 3
    apply(force)
   apply(clarify)
   apply(rename_tac a aa ab ac b)(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, {}, {}, S)")
   apply(rename_tac G F k E V S)
   apply(rename_tac G F k E V S)(*strict*)
   prefer 2
   apply(clarify)
   apply(rename_tac a aa ab ac b x ad ae af ba xa ag ah ai bb)(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, {}, {}, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "(\<And>G F k E V S.
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G, F, k, E, V, S) \<Longrightarrow>
           F_LR_MACHINE_TRANSFER (G, F, k, {}, {}, S) \<Longrightarrow>
           \<not> P G F k S (F_LR_MACHINE__fp_one G F k {} {} S) \<Longrightarrow>
           F_LR_MACHINE__one G F k S = {} \<Longrightarrow> False)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(erule_tac
      x="G"
      in meta_allE)
   apply(erule_tac
      x="F"
      in meta_allE)
   apply(erule_tac
      x="k"
      in meta_allE)
   apply(erule_tac
      x="E"
      in meta_allE)
   apply(erule_tac
      x="V"
      in meta_allE)
   apply(erule_tac
      x="S"
      in meta_allE)
   apply(erule_tac
      x="G'"
      in meta_allE)
   apply(erule_tac
      x="F'"
      in meta_allE)
   apply(erule_tac
      x="k'"
      in meta_allE)
   apply(erule_tac
      x="E'"
      in meta_allE)
   apply(erule_tac
      x="V'"
      in meta_allE)
   apply(erule_tac
      x="S'"
      in meta_allE)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(erule_tac
      x="G"
      and P="\<lambda>G. (\<And>F k E V S.
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G, F, k, E, V, S) \<Longrightarrow>
           F_LR_MACHINE_TRANSFER (G, F, k, {}, {}, S) \<Longrightarrow>
           \<not> P G F k S (F_LR_MACHINE__fp_one G F k {} {} S) \<Longrightarrow>
           F_LR_MACHINE__one G F k S = {} \<Longrightarrow> False)"
      in meta_allE)
  apply(rename_tac G F k E V S)(*strict*)
  apply(erule_tac
      x="F"
      in meta_allE)
  apply(erule_tac
      x="k"
      in meta_allE)
  apply(erule_tac
      x="E"
      in meta_allE)
  apply(erule_tac
      x="V"
      in meta_allE)
  apply(erule_tac
      x="S"
      in meta_allE)
  apply(force)
  done

lemma F_LR_MACHINE_TRANSFER_transfers: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> F_LR_MACHINE_TRANSFER (G, F, k, E, V, S)"
  apply(simp add: F_LR_MACHINE_TRANSFER_def)
  apply(simp add: F_LR_MACHINE_TRANSFER_01_def F_LR_MACHINE_TRANSFER_02_def)
  apply(simp add: F_LR_MACHINE__one_def)
  apply(rule conjI)
   apply(clarsimp)
   apply(rule finite_imageI)
   apply(rule finite_cartesian_product)
    apply(force)
   apply(rule finite_two_elements_construct_domain)
    apply(simp add: valid_cfg_def)
   apply(simp add: valid_cfg_def)
  apply(rule conjI)
   apply(rule ballI)
   apply(rename_tac q)(*strict*)
   apply(rule ballI)
   apply(rename_tac q X)(*strict*)
   apply(case_tac "\<lparr>edge_src = q, edge_event = Some X, edge_pop = [0], edge_push = [0], edge_trg = F_VALID_ITEM_SET_GOTO G F k X q\<rparr> \<in> E")
    apply(rename_tac q X)(*strict*)
    apply(force)
   apply(rename_tac q X)(*strict*)
   apply(rule inMap)
   apply(clarsimp)
  apply(simp add: F_LR_MACHINE_TRANSFER_03_def)
  apply(clarsimp)
  apply(rename_tac q)(*strict*)
  apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
  done

lemma F_LR_MACHINE__fp_one_Meta_Lift2: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> (\<And>G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S''. F_LR_MACHINE_mod_args (G, F, k, E, V, S) = (G', F', k', E', V', S') \<Longrightarrow> F_LR_MACHINE_TRANSFER (G', F', k', E', V', S') \<longrightarrow> P G' F' k' E' V' S' (F_LR_MACHINE__fp_one G' F' k' E' V' S') \<Longrightarrow> F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S) \<Longrightarrow> F_LR_MACHINE_mod_args (G, F, k, E, V, S) = (G'', F'', k'', E'', V'', S'') \<Longrightarrow> F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G'', F'', k'', E'', V'', S'') \<Longrightarrow> F_LR_MACHINE_TRANSFER (G, F, k, E, V, S) \<Longrightarrow> P G F k E V S (F_LR_MACHINE__fp_one G F k E V S))
  \<Longrightarrow> (\<And>G F k E V S. F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S) \<Longrightarrow> F_LR_MACHINE_TRANSFER (G, F, k, E, V, S) \<Longrightarrow> F_LR_MACHINE__one G F k S = {} \<Longrightarrow> P G F k E V S (F_LR_MACHINE__fp_one G F k E V S))
  \<Longrightarrow> P G F k E V S (F_LR_MACHINE__fp_one G F k E V S)"
  apply(subgoal_tac "(\<lambda>G F k E V S. F_LR_MACHINE_TRANSFER (G, F, k, E, V, S) \<longrightarrow> (P G F k E V S (F_LR_MACHINE__fp_one G F k E V S))) G F k E V S")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_LR_MACHINE_TRANSFER_transfers)
   apply(force)
  apply(subgoal_tac "(\<lambda>(G, F, k, E, V, S). F_LR_MACHINE_TRANSFER (G, F, k, E, V, S) \<longrightarrow> (P G F k E V S (F_LR_MACHINE__fp_one G F k E V S))) (G, F, k, E, V, S)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G, F, k, E, V, S). F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)"
      and RECURSIVE_COND = "\<lambda>(G, F, k, E, V, S). F_LR_MACHINE__one G F k S \<noteq> {}"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G, F, k, E, V, S). (G, F, k, E \<union> (F_LR_MACHINE__one G F k S), V \<union> S, (edge_trg ` (F_LR_MACHINE__one G F k S))-(V \<union> S))"
      and MEASURE = "\<lambda>(G, F, k, E, V, S). card (((Collect (\<lambda>x. edge_src x \<subseteq> (Collect (\<lambda>x. valid_item G k x)) \<and> (\<exists>a \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)). edge_event x = Some a) \<and> edge_push x = [0] \<and> edge_pop x = [0] \<and> edge_trg x \<subseteq> (Collect (\<lambda>x. valid_item G k x))))) -E)"
      and TERM_FUN = "(\<lambda>(G, F, k, E, V, S). F_LR_MACHINE_TRANSFER (G, F, k, E, V, S) \<longrightarrow> (P G F k E V S (F_LR_MACHINE__fp_one G F k E V S)))"
      and y = "(G, F, k, E, V, S)"
      in partial_termination_wf)
      apply(fold F_LR_MACHINE_mod_args_def)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a aa ab ac b ad ae af ag ba)(*strict*)
      apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
      apply(rename_tac G F k E V S G' F' k' E' V' S')
      apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
      apply(rule_tac
      t="(G', F', k', E', V', S')"
      and s="F_LR_MACHINE_mod_args (G, F, k, E, V, S)"
      in ssubst)
       apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
       apply(rule sym)
       apply(force)
      apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
      apply(rule F_LR_MACHINE__one_preserves_F_LR_MACHINE__fp_one_TERM_ARGS_TEST)
      apply(force)
     apply(clarify)
     apply(rename_tac a aa ab ac b)(*strict*)
     apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
     apply(rename_tac G F k E V S)
     apply(rename_tac G F k E V S)(*strict*)
     apply(case_tac "F_LR_MACHINE_mod_args (G, F, k, E, V, S)")
     apply(rename_tac G F k E V S a b c d e)(*strict*)
     apply(rename_tac G F k E V S G' F' k' E' V' S')
     apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
     apply(subgoal_tac "G'=G \<and> k'=k")
      apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
      prefer 2
      apply(simp only: F_LR_MACHINE_mod_args_def)
      apply(clarify)
      apply(blast)
     apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
     apply(thin_tac " (\<And>G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S''.
           F_LR_MACHINE_mod_args (G, F, k, E, V, S) = (G', F', k', E', V', S') \<Longrightarrow>
           F_LR_MACHINE_TRANSFER (G', F', k', E', V', S') \<longrightarrow>
           P G' F' k' E' V' S' (F_LR_MACHINE__fp_one G' F' k' E' V' S') \<Longrightarrow>
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S) \<Longrightarrow>
           F_LR_MACHINE_mod_args (G, F, k, E, V, S) = (G'', F'', k'', E'', V'', S'') \<Longrightarrow>
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G'', F'', k'', E'', V'', S'') \<Longrightarrow>
           F_LR_MACHINE_TRANSFER (G, F, k, E, V, S) \<Longrightarrow> P G F k E V S (F_LR_MACHINE__fp_one G F k E V S)) ")
     apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
     apply(clarsimp)
     apply(rename_tac G F k E V S F' E' V' S')(*strict*)
     apply(rule_tac
      S="S"
      and F="F"
      in F_LR_MACHINE_termLem2)
       apply(rename_tac G F k E V S E' V' S')(*strict*)
       apply(force)
      apply(rename_tac G F k E V S E' V' S')(*strict*)
      apply(force)
     apply(rename_tac G F k E V S E' V' S')(*strict*)
     apply(force)
    prefer 3
    apply(force)
   apply(clarify)
   apply(rename_tac a aa ab ac b)(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S)
   apply(rename_tac G F k E V S)(*strict*)
   prefer 2
   apply(clarify)
   apply(rename_tac a aa ab ac b x ad ae af ba xa ag ah ai bb)(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')
   apply(erule_tac
      x="G"
      and P="\<lambda>G. (\<And>F k E V S G' F' k' E' V' S' G''
           F'' k'' E'' V'' S''.
           F_LR_MACHINE_mod_args
            (G, F, k, E, V, S) =
           (G', F', k', E', V', S') \<Longrightarrow>
           F_LR_MACHINE_TRANSFER
            (G', F', k', E', V', S') \<longrightarrow>
           P G' F' k' E' V' S'
            (F_LR_MACHINE__fp_one G' F' k' E' V'
              S') \<Longrightarrow>
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G, F, k, E, V, S) \<Longrightarrow>
           F_LR_MACHINE_mod_args
            (G, F, k, E, V, S) =
           (G'', F'', k'', E'', V'', S'') \<Longrightarrow>
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G'', F'', k'', E'', V'', S'') \<Longrightarrow>
           F_LR_MACHINE_TRANSFER
            (G, F, k, E, V, S) \<Longrightarrow>
           P G F k E V S
            (F_LR_MACHINE__fp_one G F k E V S))"
      in meta_allE)
   apply(erule_tac
      x="F"
      in meta_allE)
   apply(erule_tac
      x="k"
      in meta_allE)
   apply(erule_tac
      x="E"
      in meta_allE)
   apply(erule_tac
      x="V"
      in meta_allE)
   apply(erule_tac
      x="S"
      in meta_allE)
   apply(erule_tac
      x="G'"
      and P="\<lambda>G'. (\<And>F' k' E' V' S' G'' F'' k'' E''
           V'' S''.
           F_LR_MACHINE_mod_args
            (G, F, k, E, V, S) =
           (G', F', k', E', V', S') \<Longrightarrow>
           F_LR_MACHINE_TRANSFER
            (G', F', k', E', V', S') \<longrightarrow>
           P G' F' k' E' V' S'
            (F_LR_MACHINE__fp_one G' F' k' E' V'
              S') \<Longrightarrow>
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G, F, k, E, V, S) \<Longrightarrow>
           F_LR_MACHINE_mod_args
            (G, F, k, E, V, S) =
           (G'', F'', k'', E'', V'', S'') \<Longrightarrow>
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G'', F'', k'', E'', V'', S''
       ) \<Longrightarrow>
           F_LR_MACHINE_TRANSFER
            (G, F, k, E, V, S) \<Longrightarrow>
           P G F k E V S
            (F_LR_MACHINE__fp_one G F k E V S))"
      in meta_allE)
   apply(erule_tac
      x="F'"
      in meta_allE)
   apply(erule_tac
      x="k'"
      in meta_allE)
   apply(erule_tac
      x="E'"
      in meta_allE)
   apply(erule_tac
      x="V'"
      in meta_allE)
   apply(erule_tac
      x="S'"
      in meta_allE)
   apply(erule_tac
      x="G''"
      and P="\<lambda>G''. (\<And>F'' k'' E'' V'' S''.
           F_LR_MACHINE_mod_args
            (G, F, k, E, V, S) =
           (G', F', k', E', V', S') \<Longrightarrow>
           F_LR_MACHINE_TRANSFER
            (G', F', k', E', V', S') \<longrightarrow>
           P G' F' k' E' V' S'
            (F_LR_MACHINE__fp_one G' F' k' E' V'
              S') \<Longrightarrow>
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G, F, k, E, V, S) \<Longrightarrow>
           F_LR_MACHINE_mod_args
            (G, F, k, E, V, S) =
           (G'', F'', k'', E'', V'', S'') \<Longrightarrow>
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G'', F'', k'', E'', V'', S'') \<Longrightarrow>
           F_LR_MACHINE_TRANSFER
            (G, F, k, E, V, S) \<Longrightarrow>
           P G F k E V S
            (F_LR_MACHINE__fp_one G F k E V S))"
      in meta_allE)
   apply(erule_tac
      x="F''" in meta_allE)
   apply(erule_tac
      x="k''"
      in meta_allE)
   apply(erule_tac
      x="E''"
      in meta_allE)
   apply(erule_tac
      x="V''"
      in meta_allE)
   apply(erule_tac
      x="S''"
      in meta_allE)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(erule_tac
      x="G"
      and P="\<lambda>G. (\<And>F k E V S.
           F_LR_MACHINE__fp_one_TERM_ARGS_TEST
            (G, F, k, E, V, S) \<Longrightarrow>
           F_LR_MACHINE_TRANSFER (G, F, k, E, V, S) \<Longrightarrow>
           F_LR_MACHINE__one G F k S = {} \<Longrightarrow>
           P G F k E V S (F_LR_MACHINE__fp_one G F k E V S))"
      in meta_allE)
  apply(rename_tac G F k E V S)(*strict*)
  apply(erule_tac
      x="F"
      in meta_allE)
  apply(erule_tac
      x="k"
      in meta_allE)
  apply(erule_tac
      x="E"
      in meta_allE)
  apply(erule_tac
      x="V"
      in meta_allE)
  apply(erule_tac
      x="S"
      in meta_allE)
  apply(blast)
  done

lemma F_LR_MACHINE__fp_one_dom_empty: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> F_LR_MACHINE__one G F k S = {}
  \<Longrightarrow> F_LR_MACHINE__fp_one_dom (G, F, k, E, V, S)"
  apply(rule F_LR_MACHINE__fp_one.domintros)
  apply(clarsimp)
  apply(simp add: F_LR_MACHINE__one_def)
  apply(erule disjE)
   apply(force)
  apply(simp add: two_elements_construct_domain_def F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def valid_cfg_def)
  done

lemma F_LR_MACHINE__fp_one_termination: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> F_LR_MACHINE__fp_one_dom (G, F, k, E, V, S)"
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G, F, k, E, V, S). F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)"
      and RECURSIVE_COND = "\<lambda>(G, F, k, E, V, S). F_LR_MACHINE__one G F k S \<noteq> {}"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G, F, k, E, V, S). (G, F, k, E \<union> (F_LR_MACHINE__one G F k S), V \<union> S, (edge_trg ` (F_LR_MACHINE__one G F k S))-(V \<union> S))"
      and MEASURE = "\<lambda>(G, F, k, E, V, S). card (((Collect (\<lambda>x. edge_src x \<subseteq> (Collect (\<lambda>x. valid_item G k x)) \<and> (\<exists>a \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)). edge_event x = Some a) \<and> edge_push x = [0] \<and> edge_pop x = [0] \<and> edge_trg x \<subseteq> (Collect (\<lambda>x. valid_item G k x))))) -E)"
      and y = "(G, F, k, E, V, S)"
      in partial_termination_wf)
      apply(fold F_LR_MACHINE_mod_args_def)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a aa ab ac b ad ae af ag ba)(*strict*)
      apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
      apply(rename_tac G F k E V S G' F' k' E' V' S')
      apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
      apply(rule_tac
      t="(G', F', k', E', V', S')"
      and s="F_LR_MACHINE_mod_args (G, F, k, E, V, S)"
      in ssubst)
       apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
       apply(force)
      apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
      apply(rule F_LR_MACHINE__one_preserves_F_LR_MACHINE__fp_one_TERM_ARGS_TEST)
      apply(force)
     apply(clarify)
     apply(rename_tac a aa ab ac b)(*strict*)
     apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
     apply(rename_tac G F k E V S)
     apply(rename_tac G F k E V S)(*strict*)
     apply(case_tac "F_LR_MACHINE_mod_args (G, F, k, E, V, S)")
     apply(rename_tac G F k E V S a b c d e)(*strict*)
     apply(rename_tac G F k E V S G' F' k' E' V' S')
     apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "G'=G \<and> k'=k")
      apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
      prefer 2
      apply(simp add: F_LR_MACHINE_mod_args_def)
     apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
     apply(clarsimp)
     apply(rename_tac G F k E V S E' V' S' F')(*strict*)
     apply(rule_tac
      S="S"
      and V="V"
      and F="F"
      in F_LR_MACHINE_termLem2)
       apply(rename_tac G k E V S E' V' S')(*strict*)
       apply(force)
      apply(rename_tac G k E V S E' V' S')(*strict*)
      apply(force)
     apply(rename_tac G k E V S E' V' S')(*strict*)
     apply(force)
    prefer 3
    apply(force)
   apply(clarify)
   apply(rename_tac a aa ab ac b)(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S)
   apply(rename_tac G F  k E V S)(*strict*)
   prefer 2
   apply(clarify)
   apply(rename_tac a aa ab ac b x ad ae af ba)(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(clarsimp)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
   apply(rename_tac ab ac b x ad)(*strict*)
   apply(rule F_LR_MACHINE__fp_one.domintros, blast)
  apply(rename_tac G F k E V S)(*strict*)
  apply(subgoal_tac "F_LR_MACHINE__fp_one_dom (G, F, k, E, V, S)")
   apply(rename_tac G F  k E V S)(*strict*)
   apply(force)
  apply(rule F_LR_MACHINE__fp_one_dom_empty)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE__fp_one_psimps_ALT: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> F_LR_MACHINE__fp_one G F k E V S = (if F_LR_MACHINE__one G F k S = {} then (V, E) else F_LR_MACHINE__fp_one G F k (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S)))"
  apply(rule_tac
      P="%X. X =
    (if F_LR_MACHINE__one G F k S = {} then (V, E)
     else F_LR_MACHINE__fp_one G F k
           (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S)
           (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S)))"
      and s=" (if S = {} then (V, E) else F_LR_MACHINE__fp_one G F k (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S)))"
      in ssubst)
   prefer 2
   apply(rule_tac t="F_LR_MACHINE__one G F k S = {}" and s="S={}" in ssubst)
    prefer 2
    apply(force)
   apply(simp add: F_LR_MACHINE__one_def)
   apply(rule antisym)
    apply(clarsimp)
    apply(simp add: two_elements_construct_domain_def F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def valid_cfg_def)
   apply(clarsimp)
  apply(rule F_LR_MACHINE__fp_one.psimps)
  apply(rule F_LR_MACHINE__fp_one_termination)
  apply(force)
  done

lemma F_LR_MACHINE_all_finite_snd2: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> finite S
  \<Longrightarrow> finite E
  \<Longrightarrow> finite V
  \<Longrightarrow> finite (snd (F_LR_MACHINE__fp_one G F k E V S))"
  apply(subgoal_tac "finite S \<and> finite E \<and> finite V \<longrightarrow> finite (snd (F_LR_MACHINE__fp_one G F k E V S))")
   apply(blast)
  apply(thin_tac "finite S")
  apply(thin_tac "finite E")
  apply(thin_tac "finite V")
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k')(*strict*)
    apply(rule propSym)
    apply(rule context_conjI)
     apply(rename_tac E V S G' F' k')(*strict*)
     apply(rule F_LR_MACHINE__one_finite)
      apply(rename_tac E V S G' F' k')(*strict*)
      apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
     apply(rename_tac E V S G' F' k')(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k')(*strict*)
    apply(rule finite_imageI)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
    apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(clarsimp)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S)(*strict*)
  apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
   apply(rename_tac G F k E V S)(*strict*)
   apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(case_tac "F_LR_MACHINE__one G F k S = {}")
   apply(rename_tac G F k E V S)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(clarsimp)
  done

lemma F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, {}, {}, {F_VALID_ITEM_SET_INITIAL G F k})"
  apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
  apply(rule conjI)
   apply(subgoal_tac "F_VALID_ITEM_SET_INITIAL G F k \<subseteq> (Collect (valid_item G k))")
    apply(force)
   apply(rule F_VALID_ITEM_SET_INITIAL_consists_of_items)
    apply(force)
   apply(force)
  apply(rule_tac
      x="[]"
      in exI)
  apply(clarsimp)
  apply(rule sym)
  apply(rule Lemma6__23_1)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_all_finite_snd: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> finite (snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}))"
  apply(rule F_LR_MACHINE_all_finite_snd2)
     apply(auto)
  apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_all_finite_fst2: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> finite S
  \<Longrightarrow> finite E
  \<Longrightarrow> finite V
  \<Longrightarrow> finite (fst (F_LR_MACHINE__fp_one G F k E V S))"
  apply(subgoal_tac "finite S \<and> finite E \<and> finite V \<longrightarrow> finite (fst (F_LR_MACHINE__fp_one G F k E V S))")
   apply(blast)
  apply(thin_tac "finite S")
  apply(thin_tac "finite E")
  apply(thin_tac "finite V")
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k')(*strict*)
    apply(rule propSym)
    apply(rule context_conjI)
     apply(rename_tac E V S G' F' k')(*strict*)
     apply(rule F_LR_MACHINE__one_finite)
      apply(rename_tac E V S G' F' k')(*strict*)
      apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
     apply(rename_tac E V S G' F' k')(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k')(*strict*)
    apply(rule finite_imageI)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
    apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S')(*strict*)
   apply(clarsimp)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S)(*strict*)
  apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
   apply(rename_tac G F k E V S)(*strict*)
   apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(case_tac "F_LR_MACHINE__one G F k S = {}")
   apply(rename_tac G F k E V S)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(clarsimp)
  done

lemma F_LR_MACHINE_all_finite_fst: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> finite (fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}))"
  apply(rule F_LR_MACHINE_all_finite_fst2)
     apply(auto)
  apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE__fp_one_snd_monotone: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> E \<subseteq> snd (F_LR_MACHINE__fp_one G F k E V S)"
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
   apply(rename_tac E V S G'' F'' k'' x)(*strict*)
   apply(rename_tac E V S G F k x)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac E V S G F k x)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = (V, E)")
     apply(rename_tac E V S G F k x)(*strict*)
     apply(clarsimp)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
     apply(rename_tac E V S G F k x)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
     apply(force)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = F_LR_MACHINE__fp_one G F k (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S))")
    apply(rename_tac E V S G F k x)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(rule_tac
      t="F_LR_MACHINE__fp_one G F k E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(force)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S)(*strict*)
  apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
   apply(rename_tac G F k E V S)(*strict*)
   apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE__fp_one_fst_monotone: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> V \<subseteq> fst (F_LR_MACHINE__fp_one G F k E V S)"
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
   apply(rename_tac E V S G'' F'' k'' x)(*strict*)
   apply(rename_tac E V S G F k x)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac E V S G F k x)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = (V, E)")
     apply(rename_tac E V S G F k x)(*strict*)
     apply(clarsimp)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
     apply(rename_tac E V S G F k x)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
     apply(force)
    apply(rename_tac E V S G  F k x)(*strict*)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = F_LR_MACHINE__fp_one G F k (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S))")
    apply(rename_tac E V S G F k x)(*strict*)
    apply(clarsimp)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(rule_tac
      t="F_LR_MACHINE__fp_one G F k E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(force)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S)(*strict*)
  apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
   apply(rename_tac G F k E V S)(*strict*)
   apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE__fp_one_fst_monotone2: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> S \<subseteq> fst (F_LR_MACHINE__fp_one G F k E V S)"
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
   apply(rename_tac E V S G'' k'' x)(*strict*)
   apply(rename_tac E V S G F k x)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac E V S G F k x)(*strict*)
    apply(subgoal_tac "S={}")
     apply(rename_tac E V S G F k x)(*strict*)
     prefer 2
     apply(simp add: F_LR_MACHINE__one_def)
     apply(clarsimp)
     apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
     apply(simp add: valid_cfg_def two_elements_construct_domain_def)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(clarsimp)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      A="V \<union> S"
      in set_mp)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule F_LR_MACHINE__fp_one_fst_monotone)
    apply(clarsimp)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S)(*strict*)
  apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
   apply(rename_tac G F k E V S)(*strict*)
   apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
   apply(force)
  apply(rename_tac G F k E V S)(*strict*)
  apply(subgoal_tac "S={}")
   apply(rename_tac G F k E V S)(*strict*)
   prefer 2
   apply(simp add: F_LR_MACHINE__one_def)
   apply(clarsimp)
   apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
   apply(simp add: valid_cfg_def two_elements_construct_domain_def)
  apply(rename_tac G F k E V S)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_all_edgesOK2: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> \<forall>x \<in> E. edge_src x \<in> V \<and> (\<exists>y. (edge_event x) = Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> (V \<union> S)
  \<Longrightarrow> \<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k E V S). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k E V S) \<and> (\<exists>y. (edge_event x) = Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k E V S)"
  apply(subgoal_tac "(\<forall>x \<in> E. edge_src x \<in> V \<and> (\<exists>y. edge_event x = Some y \<and> y \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> edge_pop x = [0] \<and> edge_push x = [0] \<and> edge_trg x \<in> (V \<union> S)) \<longrightarrow> (\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k E V S). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k E V S) \<and> (\<exists>y. edge_event x = Some y \<and> y \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> edge_pop x = [0] \<and> edge_push x = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k E V S)) ")
   apply(force)
  apply(thin_tac "\<forall>x \<in> E. edge_src x \<in> V \<and> (\<exists>y. edge_event x = Some y \<and> y \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> edge_pop x = [0] \<and> edge_push x = [0] \<and> edge_trg x \<in> (V \<union> S)")
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(rule impI)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x)(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k' x)(*strict*)
    apply(erule disjE)
     apply(rename_tac E V S G' F' k' x)(*strict*)
     apply(clarsimp)
     apply(simp add: F_LR_MACHINE__one_def)
     apply(erule_tac
      x="x"
      in ballE)
      apply(rename_tac E V S G' F' k' x)(*strict*)
      apply(clarsimp)
     apply(rename_tac E V S G' F' k' x)(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k' x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_LR_MACHINE__one_def)
    apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x)(*strict*)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. edge_src x \<in> V \<and> (\<exists>y. edge_event x = Some y \<and> y \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x)) \<and> edge_pop x = [0] \<and> edge_push x = [0] \<and> (edge_trg x \<in> V \<or> edge_trg x \<in> S)"
      in ballE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x)(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k' x y)(*strict*)
    apply(rename_tac E V S G F k x y)
    apply(rename_tac E V S G F k x y)(*strict*)
    apply(case_tac "F_LR_MACHINE__one G F k S = {}")
     apply(rename_tac E V S G F k x y)(*strict*)
     apply(clarsimp)
     apply(subgoal_tac "S={}")
      apply(rename_tac E V S G F k x y)(*strict*)
      apply(clarsimp)
      apply(rename_tac E V G k x y)(*strict*)
      apply(erule_tac
      x="x"
      in ballE)
       apply(rename_tac E V G k x y)(*strict*)
       apply(clarsimp)
      apply(rename_tac E V G k x y)(*strict*)
      apply(force)
     apply(rename_tac E V S G F k x y)(*strict*)
     apply(simp add: F_LR_MACHINE__one_def)
     apply(clarsimp)
    apply(rename_tac E V S G F k x y)(*strict*)
    apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = F_LR_MACHINE__fp_one G F k (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S))")
     apply(rename_tac E V S G F k x y)(*strict*)
     apply(clarsimp)
     apply(erule_tac
      x="x"
      in ballE)
      apply(rename_tac E V S G F k x y)(*strict*)
      apply(clarsimp)
     apply(rename_tac E V S G F k x y)(*strict*)
     apply(force)
    apply(rename_tac E V S G F k x y)(*strict*)
    apply(rule_tac
      t="F_LR_MACHINE__fp_one G F k E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
     apply(rename_tac E V S G F k x y)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
     apply(force)
    apply(rename_tac E V S G F k x y)(*strict*)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x)(*strict*)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
   apply(rename_tac E V S G' F' k' x)(*strict*)
   apply(rename_tac E V S G F k x)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac E V S G F k x)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "S={}")
     apply(rename_tac E V S G F k x)(*strict*)
     apply(clarsimp)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(simp add: F_LR_MACHINE__one_def)
    apply(clarsimp)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = F_LR_MACHINE__fp_one G F k (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S))")
     apply(rename_tac E V S G F k x)(*strict*)
     apply(clarsimp)
     apply(simp add: F_LR_MACHINE__one_def)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule_tac
      t="F_LR_MACHINE__fp_one G F k E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
     apply(rename_tac E V S G F k x)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
     apply(force)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule cfg_has_nonempty_two_elements_construct_domain)
     apply(rename_tac E V S G F k x)(*strict*)
     apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
     apply(force)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = F_LR_MACHINE__fp_one G F k (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S))")
    apply(rename_tac E V S G F k x)(*strict*)
    apply(clarsimp)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(rule_tac
      t="F_LR_MACHINE__fp_one G F k E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
    apply(rename_tac E V S G F k x)(*strict*)
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac E V S G F k x)(*strict*)
   apply(force)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga Fa ka Ea Va Sa x)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S x)(*strict*)
  apply(subgoal_tac "S={}")
   apply(rename_tac G F k E V S x)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V {}= (if F_LR_MACHINE__one G F k {} = {} then (V, E) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSE SSG SSF SSk SSV SSS)
    apply(rename_tac G F k E V S x)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac G F k E V S x)(*strict*)
   prefer 2
   apply(simp add: F_LR_MACHINE__one_def)
   apply(erule disjE)
    apply(rename_tac G F k E V S x)(*strict*)
    apply(force)
   apply(rename_tac G F k E V S x)(*strict*)
   apply(rule cfg_has_nonempty_two_elements_construct_domain)
    apply(rename_tac G F k E V S x)(*strict*)
    apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
    apply(force)
   apply(rename_tac G F k E V S x)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S x)(*strict*)
  apply(clarsimp)
  done

lemma F_LR_MACHINE_all_edgesOK: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> \<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x) = Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})"
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(force)
  apply(rule F_LR_MACHINE_all_edgesOK2)
   apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_all_edgesOK_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> \<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x) = Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})"
  apply(rule F_LR_MACHINE_all_edgesOK2)
   apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_all_edges_src_OK: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> \<forall>x \<in> E. edge_src x \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> \<forall>x \<in> S. x \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> \<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k E V S). edge_src x \<subseteq> (Collect (valid_item G k))"
  apply(subgoal_tac "(\<forall>x \<in> E. edge_src x \<subseteq> Collect (valid_item G k)) \<and> (\<forall>x \<in> S. x \<subseteq> Collect (valid_item G k)) \<longrightarrow> (\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k E V S). edge_src x \<subseteq> (Collect (valid_item G k)))")
   apply(force)
  apply(thin_tac "\<forall>x \<in> E. edge_src x \<subseteq> Collect (valid_item G k)")
  apply(thin_tac "\<forall>x \<in> S. x \<subseteq> Collect (valid_item G k)")
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k' x xa)(*strict*)
    apply(rule conjI)
     apply(rename_tac E V S G' F' k' x xa)(*strict*)
     apply(clarsimp)
     apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
     apply(erule disjE)
      apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
      apply(erule_tac
      x="xb"
      in ballE)
       apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
       apply(force)
      apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
      apply(force)
     apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
     apply(simp add: F_LR_MACHINE__one_def)
     apply(clarsimp)
     apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
     apply(erule_tac
      x="a"
      in ballE)
      apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
      apply(force)
     apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k' x xa)(*strict*)
    apply(simp add: F_LR_MACHINE__one_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k' x xa a b xd)(*strict*)
    apply(erule_tac
      x="a"
      in ballE)
     apply(rename_tac E V S G' F' k' x xa a b xd)(*strict*)
     apply(rule_tac
      S="a"
      and F="F'"
      in F_VALID_ITEM_SET_GOTO_preserves_item_set)
        apply(rename_tac E V S G' F' k' x xa a b xd)(*strict*)
        apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G', F', k', E \<union> (\<lambda>(q, X). \<lparr>edge_src = q, edge_event = Some X, edge_pop = [0], edge_push = [0], edge_trg = F_VALID_ITEM_SET_GOTO G' F' k' X q\<rparr>) ` (S \<times> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')), V \<union> S, edge_trg ` (\<lambda>(q, X). \<lparr>edge_src = q, edge_event = Some X, edge_pop = [0], edge_push = [0], edge_trg = F_VALID_ITEM_SET_GOTO G' F' k' X q\<rparr>) ` (S \<times> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')) - (V \<union> S))")
        apply(rename_tac E V S G' F' k' x xa a b xd)(*strict*)
        apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
       apply(rename_tac E V S G' F' k' x xa a b xd)(*strict*)
       apply(simp only: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
       apply(force)
      apply(force)
     apply(rename_tac E V S G' F' k' x xa a b xd)(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k' x xa a b xd)(*strict*)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = (V, E)")
     apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
     apply(clarsimp)
     apply(simp add: F_LR_MACHINE_mod_args_def)
     apply(subgoal_tac "F_LR_MACHINE__fp_one G' F' k' E' V' {} = (V', E')")
      apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac V S G' k' E' x xa)(*strict*)
      apply(erule_tac
      x="x"
      in ballE)
       apply(rename_tac V S G' k' E' x xa)(*strict*)
       apply(force)
      apply(rename_tac V S G' k' E' x xa)(*strict*)
      apply(force)
     apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
     apply(rule_tac
      t="F_LR_MACHINE__fp_one G' F' k' E' V' {}"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
      apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
      apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
      apply(force)
     apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
     apply(simp add: F_LR_MACHINE__one_def)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(rule_tac
      t="F_LR_MACHINE__fp_one G F k E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
     apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
     apply(force)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(simp add: F_LR_MACHINE__one_def)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S= (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. edge_src x \<subseteq> Collect (valid_item G k)"
      in ballE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(force)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga Fa ka Ea Va Sa x xa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S x xa)(*strict*)
  apply(subgoal_tac "S={}")
   apply(rename_tac G F k E V S x xa)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V {}= (if F_LR_MACHINE__one G F k {} = {} then (V, E) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE)
    apply(rename_tac G F k E V S x xa)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac G F k E V S x xa)(*strict*)
   prefer 2
   apply(simp add: F_LR_MACHINE__one_def)
   apply(erule disjE)
    apply(rename_tac G F k E V S x xa)(*strict*)
    apply(force)
   apply(rename_tac G F k E V S x xa)(*strict*)
   apply(rule cfg_has_nonempty_two_elements_construct_domain)
    apply(rename_tac G F k E V S x xa)(*strict*)
    apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
    apply(force)
   apply(rename_tac G F k E V S x xa)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G k E V x xa)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac G k E V x xa)(*strict*)
   apply(force)
  apply(rename_tac G k E V x xa)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_all_edges_src_OK2: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> \<forall>x \<in> V \<union> S. x \<subseteq> Collect (valid_item G k)
  \<Longrightarrow> \<forall>x \<in> fst (F_LR_MACHINE__fp_one G F k E V S). x \<subseteq> (Collect (valid_item G k))"
  apply(subgoal_tac "(\<forall>x \<in> V \<union> S. x \<subseteq> Collect (valid_item G k)) \<longrightarrow> (\<forall>x \<in> fst (F_LR_MACHINE__fp_one G F k E V S). x \<subseteq> (Collect (valid_item G k)))")
   apply(force)
  apply(thin_tac "\<forall>x \<in> V \<union> S. x \<subseteq> Collect (valid_item G k)")
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
    apply(erule disjE)
     apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
    apply(erule disjE)
     apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k' x xa xb xc)(*strict*)
    apply(simp add: F_LR_MACHINE__one_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
    apply(erule_tac
      x="a"
      in ballE)
     apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
     apply(rule_tac
      S="a"
      and F="F'"
      in F_VALID_ITEM_SET_GOTO_preserves_item_set)
        apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
        apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST
        (G', F', k',
         E \<union>
         (\<lambda>(q, X).
             \<lparr>edge_src = q, edge_event = Some X, edge_pop = [0],
                edge_push = [0], edge_trg = F_VALID_ITEM_SET_GOTO G' F' k' X q\<rparr>) `
         (S \<times> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')),
         V \<union> S,
         edge_trg `
         (\<lambda>(q, X).
             \<lparr>edge_src = q, edge_event = Some X, edge_pop = [0],
                edge_push = [0], edge_trg = F_VALID_ITEM_SET_GOTO G' F' k' X q\<rparr>) `
         (S \<times> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')) -
         (V \<union> S))")
        apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
        apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
       apply(simp only: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
       apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
       apply(force)
      apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
      apply(force)
     apply(rename_tac E V S G' F' k' x xa xc a b)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = (V, E)")
     apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
     apply(clarsimp)
     apply(simp add: F_LR_MACHINE_mod_args_def)
     apply(subgoal_tac "F_LR_MACHINE__fp_one G' F' k' E' V' {} = (V', E')")
      apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
      apply(clarsimp)
      apply(rename_tac V S G' k' E' x xa)(*strict*)
      apply(erule_tac
      x="x"
      in ballE)
       apply(rename_tac V S G' k' E' x xa)(*strict*)
       apply(force)
      apply(rename_tac V S G' k' E' x xa)(*strict*)
      apply(force)
     apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
     apply(rule_tac
      t="F_LR_MACHINE__fp_one G' F' k' E' V' {}"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
      apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
      apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
      apply(force)
     apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
     apply(simp add: F_LR_MACHINE__one_def)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(rule_tac
      t="F_LR_MACHINE__fp_one G F k E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
     apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
     apply(force)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(simp add: F_LR_MACHINE__one_def)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S= (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="x"
      and P="\<lambda>x. x \<subseteq> Collect (valid_item G k)"
      in ballE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x xa)(*strict*)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(force)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga Fa ka Ea Va Sa x xa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S x xa)(*strict*)
  apply(subgoal_tac "S={}")
   apply(rename_tac G F k E V S x xa)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V {}= (if F_LR_MACHINE__one G F k {} = {} then (V, E) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE)
    apply(rename_tac G F k E V S x xa)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac G F k E V S x xa)(*strict*)
   prefer 2
   apply(simp add: F_LR_MACHINE__one_def)
   apply(erule disjE)
    apply(rename_tac G F k E V S x xa)(*strict*)
    apply(force)
   apply(rename_tac G F k E V S x xa)(*strict*)
   apply(rule cfg_has_nonempty_two_elements_construct_domain)
    apply(rename_tac G F k E V S x xa)(*strict*)
    apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
    apply(force)
   apply(rename_tac G F k E V S x xa)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S x xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac G k E V x xa)(*strict*)
  apply(erule_tac
      x="x"
      in ballE)
   apply(rename_tac G k E V x xa)(*strict*)
   apply(force)
  apply(rename_tac G k E V x xa)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_all_edgesDiffer: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> \<forall>x1 x2. x1 \<in> (snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})) \<and> x2 \<in> (snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})) \<and> (x1\<lparr>edge_trg := edge_trg x2\<rparr>) = x2\<longrightarrow> x1 = x2"
  apply(clarsimp)
  apply(rename_tac x1 x2)(*strict*)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(rename_tac x1 x2)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK_prime)
    apply(force)
   apply(force)
  apply(rename_tac x1 x2)(*strict*)
  apply(erule_tac
      x="x1"
      in ballE)
   apply(rename_tac x1 x2)(*strict*)
   apply(clarsimp)
   apply(rename_tac x1 x2 y)(*strict*)
   apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
    apply(rename_tac x1 x2 y)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE_all_edgesOK_prime)
     apply(force)
    apply(force)
   apply(rename_tac x1 x2 y)(*strict*)
   apply(erule_tac
      x="x2"
      in ballE)
    apply(rename_tac x1 x2 y)(*strict*)
    apply(clarsimp)
    apply(rename_tac x1 x2 y ya)(*strict*)
    apply(case_tac x1)
    apply(rename_tac x1 x2 y ya edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(case_tac x2)
    apply(rename_tac x1 x2 y ya edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x1 x2 y)(*strict*)
   apply(force)
  apply(rename_tac x1 x2)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE__fp_one_step_eq: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> F_LR_MACHINE_mod_args (G, F, k, E, V, S) = (G', F', k', E', V', S')
  \<Longrightarrow> F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G', F', k', E', V', S')
  \<Longrightarrow> F_LR_MACHINE_TRANSFER (G, F, k, E, V, S)
  \<Longrightarrow> F_LR_MACHINE__fp_one G F k E V S = F_LR_MACHINE__fp_one G' F' k' E' V' S'"
  apply(simp add: F_LR_MACHINE_mod_args_def)
  apply(clarsimp)
  apply(rule_tac
      t="F_LR_MACHINE__fp_one G' F' k' E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
   apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "S={}")
   apply(clarsimp)
   apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(clarsimp)
  apply(simp add: F_LR_MACHINE__one_def)
  apply(clarsimp)
  apply(simp add: F_LR_MACHINE__fp_one_TERM_ARGS_TEST_def)
  apply(simp add: valid_cfg_def two_elements_construct_domain_def)
  done

lemma F_LR_MACHINE__fp_one_colapses: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> F_LR_MACHINE__one G F k S = {}
  \<Longrightarrow> F_LR_MACHINE__fp_one G F k E V S = (V, E)"
  apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
   apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
   apply(force)
  apply(clarsimp)
  done

lemma F_LR_MACHINE__fp_one_unfold_03: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> \<forall>q \<in> V \<union> S. \<exists>w. set w \<subseteq> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> q = valid_item_set G k w
  \<Longrightarrow> q \<in> fst (F_LR_MACHINE__fp_one G F k E V S)
  \<Longrightarrow> \<exists>w. set w \<subseteq> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> q = valid_item_set G k w"
  apply(subgoal_tac "(\<forall>q \<in> V \<union> S. \<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> q = valid_item_set G k w) \<longrightarrow> (\<forall>q \<in> fst (F_LR_MACHINE__fp_one G F k E V S). \<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> q = valid_item_set G k w)")
   apply(force)
  apply(thin_tac "q \<in> fst (F_LR_MACHINE__fp_one G F k E V S)")
  apply(thin_tac "\<forall>q \<in> V \<union> S. \<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> q = valid_item_set G k w")
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(force)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE_TRANSFER (G', F', k', E', V', S')")
    apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
   apply(simp add: F_LR_MACHINE_TRANSFER_def F_LR_MACHINE_TRANSFER_03_def)
   apply(clarsimp)
   apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = F_LR_MACHINE__fp_one G' F' k' E' V' S'")
    apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE__fp_one_step_eq)
       apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
       apply(force)
      apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
      apply(force)
     apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
     apply(force)
    apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="q"
      and A="fst (F_LR_MACHINE__fp_one G' F' k' E' V' S')"
      and P="\<lambda>q. \<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G') \<and> q = valid_item_set G' k' w"
      in ballE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(rename_tac G F k E V S G' F' k' E' V' S' q)(*strict*)
   apply(force)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k E V S q)(*strict*)
  apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = (V, E)")
   apply(rename_tac G F k E V S q)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k E V S q)(*strict*)
  apply(rule F_LR_MACHINE__fp_one_colapses)
   apply(rename_tac G F k E V S q)(*strict*)
   apply(force)
  apply(rename_tac G F k E V S q)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_all_uniqueEntry: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> \<forall>e1 e2. e1 \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> e2 \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> edge_trg e2 = edge_trg e1 \<and> edge_trg e1 \<noteq> {} \<longrightarrow> edge_event e1 = edge_event e2"
  apply(clarsimp)
  apply(rename_tac e1 e2)(*strict*)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(rename_tac e1 e2)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK_prime)
    apply(force)
   apply(force)
  apply(rename_tac e1 e2)(*strict*)
  apply(erule_tac
      x="e1"
      in ballE)
   apply(rename_tac e1 e2)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 e2 y)(*strict*)
   apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
    apply(rename_tac e1 e2 y)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE_all_edgesOK_prime)
     apply(force)
    apply(force)
   apply(rename_tac e1 e2 y)(*strict*)
   apply(erule_tac
      x="e2"
      in ballE)
    apply(rename_tac e1 e2 y)(*strict*)
    apply(clarsimp)
    apply(rename_tac e1 e2 y ya)(*strict*)
    defer
    apply(rename_tac e1 e2 y)(*strict*)
    apply(force)
   apply(rename_tac e1 e2)(*strict*)
   apply(force)
  apply(rename_tac e1 e2 y ya)(*strict*)
  apply(case_tac e1)
  apply(rename_tac e1 e2 y ya edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(case_tac e2)
  apply(rename_tac e1 e2 y ya edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
  apply(clarsimp)
  apply(rename_tac y ya edge_src edge_srca)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO_unique_entry_for_nonempty_sets)
       apply(rename_tac y ya edge_src edge_srca)(*strict*)
       apply(force)
      apply(rename_tac y ya edge_src edge_srca)(*strict*)
      apply(force)
     apply(rename_tac y ya edge_src edge_srca)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac y ya edge_src edge_srca)(*strict*)
   apply(subgoal_tac "\<forall>x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). x \<subseteq> Collect (valid_item G k)")
    apply(rename_tac y ya edge_src edge_srca)(*strict*)
    prefer 2
    apply(rule F_LR_MACHINE_all_edges_src_OK2)
     apply(rename_tac y ya edge_src edge_srca)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
      apply(force)
     apply(force)
    apply(rename_tac y ya edge_src edge_srca)(*strict*)
    apply(subgoal_tac "F_VALID_ITEM_SET_INITIAL G F k \<subseteq> (Collect (valid_item G k))")
     apply(rename_tac y ya edge_src edge_srca)(*strict*)
     apply(force)
    apply(rename_tac y ya edge_src edge_srca)(*strict*)
    apply(rule F_VALID_ITEM_SET_INITIAL_consists_of_items)
     apply(force)
    apply(rename_tac y ya edge_src edge_srca)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac y ya edge_src edge_srca)(*strict*)
  apply(subgoal_tac "\<forall>x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). x \<subseteq> Collect (valid_item G k)")
   apply(rename_tac y ya edge_src edge_srca)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_edges_src_OK2)
    apply(rename_tac y ya edge_src edge_srca)(*strict*)
    apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
     apply(force)
    apply(force)
   apply(rename_tac y ya edge_src edge_srca)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_INITIAL G F k \<subseteq> (Collect (valid_item G k))")
    apply(rename_tac y ya edge_src edge_srca)(*strict*)
    apply(force)
   apply(rename_tac y ya edge_src edge_srca)(*strict*)
   apply(rule F_VALID_ITEM_SET_INITIAL_consists_of_items)
    apply(force)
   apply(force)
  apply(rename_tac y ya edge_src edge_srca)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_complete_prime: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> (\<forall>x' p. x' \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<longrightarrow> p \<in> V \<longrightarrow> \<lparr>edge_src = p, edge_event = Some x', edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k x' p\<rparr> \<in> E) \<longrightarrow> (\<forall>x' p. x' \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<longrightarrow> p \<in> fst (F_LR_MACHINE__fp_one G F k E V S) \<longrightarrow> \<lparr>edge_src = p, edge_event = Some x', edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k x' p\<rparr> \<in> snd (F_LR_MACHINE__fp_one G F k E V S))"
  apply(rule_tac
      G="G"
      and k="k"
      and S="S"
      and E="E"
      and V="V"
      in F_LR_MACHINE__fp_one_Meta_Lift2)
    apply(blast)
   apply(rename_tac Ga Fa ka Ea Va Sa G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
   apply(rename_tac G F k E V S G' F' k' E' V' S' G'' F'' k'' E'' V'' S'')(*strict*)
   apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x' p)(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x' p)(*strict*)
    apply(rule F_LR_MACHINE_TRANSFER_transfers)
    apply(force)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x' p)(*strict*)
   apply(erule impE)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x' p)(*strict*)
    apply(clarsimp)
    apply(rename_tac G F k E V S G' F' k' E' V' S' x' p x'nonterminal pa)(*strict*)
    apply(simp add: F_LR_MACHINE_mod_args_def)
    apply(clarsimp)
    apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
    apply(erule_tac
      x="x'nonterminal"
      in allE)
    apply(clarsimp)
    apply(erule_tac
      x="pa"
      in allE)
    apply(erule disjE)
     apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
     apply(clarsimp)
    apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
    apply(subgoal_tac "pa \<notin> S")
     apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
    apply(simp add: F_LR_MACHINE__one_def)
    apply(subgoal_tac "\<lparr>edge_src = pa, edge_event = Some x'nonterminal, edge_pop = [epda_box (F_LR_MACHINE G' F' k')], edge_push = [epda_box (F_LR_MACHINE G' F' k')], edge_trg = F_VALID_ITEM_SET_GOTO G' F' k' x'nonterminal pa\<rparr> \<in> (\<lambda>(q, X). \<lparr>edge_src = q, edge_event = Some X, edge_pop = [0], edge_push = [0], edge_trg = F_VALID_ITEM_SET_GOTO G' F' k' X q\<rparr>) ` (S \<times> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G'))")
     apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
     apply(force)
    apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
    apply(rule inMap)
    apply(rule_tac
      x="(pa, x'nonterminal)"
      in bexI)
     apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
     apply(clarsimp)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac E V S G' F' k' x' p x'nonterminal pa)(*strict*)
    apply(clarsimp)
   apply(rename_tac G F k E V S G' F' k' E' V' S' x' p)(*strict*)
   apply(simp add: F_LR_MACHINE_mod_args_def)
   apply(clarsimp)
   apply(rename_tac E V S G' F' k' x' p)(*strict*)
   apply(erule_tac
      x="x'"
      and P="\<lambda>x'. x' \<in> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G') \<longrightarrow> (\<forall>p. p \<in> fst (F_LR_MACHINE__fp_one G' F' k' (E \<union> F_LR_MACHINE__one G' F' k' S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G' F' k' S - (V \<union> S))) \<longrightarrow> \<lparr>edge_src = p, edge_event = Some x', edge_pop = [epda_box (F_LR_MACHINE G' F' k')], edge_push = [epda_box (F_LR_MACHINE G' F' k')], edge_trg = F_VALID_ITEM_SET_GOTO G' F' k' x' p\<rparr> \<in> snd (F_LR_MACHINE__fp_one G' F' k' (E \<union> F_LR_MACHINE__one G' F' k' S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G' F' k' S - (V \<union> S))))"
      in allE)
   apply(rename_tac E V S G' F' k' x' p)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="p"
      in allE)
   apply(rename_tac E V S G F k x' p)
   apply(rename_tac E V S G F k x' p)(*strict*)
   apply(case_tac "F_LR_MACHINE__one G F k S = {}")
    apply(rename_tac E V S G F k x' p)(*strict*)
    apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = (V, E)")
     apply(rename_tac E V S G F k x' p)(*strict*)
     apply(clarsimp)
    apply(rename_tac E V S G F k x' p)(*strict*)
    prefer 2
    apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
     apply(rename_tac E V S G F k x' p)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
     apply(force)
    apply(rename_tac E V S G F k x' p)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "p \<in> fst (F_LR_MACHINE__fp_one G F k (E \<union> F_LR_MACHINE__one G F k S) (V \<union> S) (edge_trg ` F_LR_MACHINE__one G F k S - (V \<union> S)))")
     apply(rename_tac E V S G F k x' p)(*strict*)
     apply(force)
    apply(rename_tac E V S G F k x' p)(*strict*)
    apply(rule_tac
      A="fst (F_LR_MACHINE__fp_one G F k E V S)"
      in set_mp)
     apply(rename_tac E V S G F k x' p)(*strict*)
     apply(rule_tac
      t="F_LR_MACHINE__fp_one G F k E V S"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
      apply(rename_tac E V S G F k x' p)(*strict*)
      apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
      apply(force)
     apply(rename_tac E V S G F k x' p)(*strict*)
     apply(clarsimp)
    apply(rename_tac E V S G F k x' p)(*strict*)
    apply(force)
   apply(rename_tac E V S G F k x' p)(*strict*)
   apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
    apply(rename_tac E V S G F k x' p)(*strict*)
    apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
    apply(force)
   apply(rename_tac E V S G F k x' p)(*strict*)
   apply(subgoal_tac "F_LR_MACHINE__one G F k {} = {}")
    apply(rename_tac E V S G F k x' p)(*strict*)
    apply(clarsimp)
   apply(rename_tac E V S G F k x' p)(*strict*)
   apply(simp add: F_LR_MACHINE__one_def)
  apply(rename_tac Ga Fa ka Ea Va Sa)(*strict*)
  apply(thin_tac "F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)")
  apply(rename_tac G F k E V S)(*strict*)
  apply(clarsimp)
  apply(rename_tac G F k E V S x' p)(*strict*)
  apply(subgoal_tac "F_LR_MACHINE__fp_one G F k E V S = (V, E)")
   apply(rename_tac G F k E V S x' p)(*strict*)
   apply(clarsimp)
  apply(rename_tac G F k E V S x' p)(*strict*)
  apply(rule_tac
      t="F_LR_MACHINE__fp_one SSG SSF SSk SSE SSV SSS"
      and s=" (if F_LR_MACHINE__one SSG SSF SSk SSS = {} then (SSV, SSE) else F_LR_MACHINE__fp_one SSG SSF SSk (SSE \<union> F_LR_MACHINE__one SSG SSF SSk SSS) (SSV \<union> SSS) (edge_trg ` F_LR_MACHINE__one SSG SSF SSk SSS - (SSV \<union> SSS)))" for SSG SSF SSk SSS SSV SSE
      in ssubst)
   apply(rename_tac G F k E V S x' p)(*strict*)
   apply(rule F_LR_MACHINE__fp_one_psimps_ALT)
   apply(force)
  apply(rename_tac G F k E V S x' p)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_complete: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> x' \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> p \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})
  \<Longrightarrow> \<lparr>edge_src = p, edge_event = Some x', edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k x' p\<rparr> \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})"
  apply(subgoal_tac "(\<forall>x' p. x' \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<longrightarrow> p \<in> {} \<longrightarrow> \<lparr>edge_src = p, edge_event = Some x', edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k x' p\<rparr> \<in> {}) \<longrightarrow> (\<forall>x' p. x' \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<longrightarrow> p \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<longrightarrow> \<lparr>edge_src = p, edge_event = Some x', edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k x' p\<rparr> \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}))")
   apply(force)
  apply(rule F_LR_MACHINE_complete_prime)
  apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
   apply(force)
  apply(force)
  done

theorem LRM_contains_theEqClasses: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> epda_states M = {valid_item_set G k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)}"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> x = valid_item_set G k w")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule F_LR_MACHINE__fp_one_unfold_03)
     apply(rename_tac x)(*strict*)
     apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
      apply(force)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
    apply(rule sym)
    apply(rule Lemma6__23_1)
     apply(force)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(clarsimp)
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<longrightarrow> valid_item_set G k w \<in> epda_states (F_LR_MACHINE G F k)")
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(thin_tac "set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(induct_tac w rule: rev_induct)
   apply(rename_tac w)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="valid_item_set G k []"
      and s="F_VALID_ITEM_SET_INITIAL G F k"
      in ssubst)
    apply(rule Lemma6__23_1)
     apply(force)
    apply(force)
   apply(simp add: F_LR_MACHINE_def)
   apply(rule_tac
      A="{F_VALID_ITEM_SET_INITIAL G F k}"
      in set_mp)
    apply(rule F_LR_MACHINE__fp_one_fst_monotone2)
    apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac w x xs)(*strict*)
  apply(clarsimp)
  apply(rename_tac x xs)(*strict*)
  apply(subgoal_tac "\<lparr>edge_src = valid_item_set G k xs, edge_event = Some x, edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k x (valid_item_set G k xs)\<rparr> \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(rename_tac x xs)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_complete)
      apply(rename_tac x xs)(*strict*)
      apply(force)
     apply(rename_tac x xs)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac x xs)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac x xs)(*strict*)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(rename_tac x xs)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK)
    apply(force)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = valid_item_set G k xs, edge_event = Some x, edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k x (valid_item_set G k xs)\<rparr>"
      in ballE)
   apply(rename_tac x xs)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="valid_item_set G k (xs @ [x])"
      and s="F_VALID_ITEM_SET_GOTO G F k x (valid_item_set G k xs)"
      in ssubst)
   apply(rename_tac x xs)(*strict*)
   prefer 2
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac x xs)(*strict*)
  apply(rule Lemma6__26)
     apply(rename_tac x xs)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac x xs)(*strict*)
   apply(subgoal_tac "set (xs@[x]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
    apply(rename_tac x xs)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(force)
   apply(rename_tac x xs)(*strict*)
   apply(rule two_elements_construct_domain_append)
    apply(rename_tac x xs)(*strict*)
    apply(force)
   apply(rename_tac x xs)(*strict*)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(subgoal_tac "set (xs@[x]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   apply(rename_tac x xs)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(rule two_elements_construct_domain_append)
   apply(rename_tac x xs)(*strict*)
   apply(force)
  apply(rename_tac x xs)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_all_insert_edge_valid_item_set: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> setA (w @ [a]) \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB (w @ [a]) \<subseteq> cfg_events G
  \<Longrightarrow> \<lparr>edge_src = valid_item_set G k w, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = valid_item_set G k (w @ [a]) \<rparr> \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})"
  apply(subgoal_tac "valid_item_set G k w \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(rule_tac
      t="valid_item_set G k (w @ [a])"
      and s="F_VALID_ITEM_SET_GOTO G F k a (valid_item_set G k w)"
      in ssubst)
    apply(rule Lemma6__26)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rule F_LR_MACHINE_complete)
      apply(force)
     apply(force)
    apply(simp only: setAConcat concat_asso setBConcat two_elements_construct_domain_def)
    apply(clarsimp)
    apply(case_tac a)
     apply(rename_tac aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac b)(*strict*)
    apply(clarsimp)
   apply(force)
  apply(rule_tac
      t="fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})"
      and s="epda_states M"
      in ssubst)
   apply(simp add: F_LR_MACHINE_def)
  apply(rule_tac
      t="epda_states M "
      and s="{valid_item_set G k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)}"
      in ssubst)
   apply(rule LRM_contains_theEqClasses)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule_tac
      x="w"
      in exI)
  apply(rule conjI)
   apply(clarsimp)
  apply(rule_tac
      B="set (w@[a])"
      in subset_trans)
   apply(force)
  apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
   apply(force)
  apply(force)
  done

theorem F_LR_MACHINE_Complete: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> some_step_from_every_configuration M"
  apply(simp only: some_step_from_every_configuration_def F_LR_MACHINE_def)
  apply(clarsimp)
  apply(rename_tac q A)(*strict*)
  apply(rule_tac
      x="\<lparr>edge_src = q, edge_event = Some A, edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k A q\<rparr>"
      in bexI)
   apply(rename_tac q A)(*strict*)
   apply(force)
  apply(rename_tac q A)(*strict*)
  apply(rule F_LR_MACHINE_complete)
     apply(force)
    apply(rename_tac q A)(*strict*)
    apply(force)
   apply(rename_tac q A)(*strict*)
   apply(force)
  apply(rename_tac q A)(*strict*)
  apply(force)
  done

theorem Theorem6__27_b: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> p \<noteq> {}
  \<Longrightarrow> e1 \<in> epda_delta M
  \<Longrightarrow> e2 \<in> epda_delta M
  \<Longrightarrow> edge_trg e1 = p
  \<Longrightarrow> edge_trg e2 = p
  \<Longrightarrow> edge_event e1 = edge_event e2"
  apply(simp add: F_LR_MACHINE_def)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>e1 e2. e1 \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> e2 \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> edge_trg e2 = edge_trg e1 \<and> edge_trg e1\<noteq>{} \<longrightarrow> edge_event e1 = edge_event e2")
   apply(blast)
  apply(rule F_LR_MACHINE_all_uniqueEntry)
   apply(blast)
  apply(force)
  done

lemma F_LR_MACHINE__fp_one_mono_fst: "
  F_LR_MACHINE__fp_one_TERM_ARGS_TEST (G, F, k, E, V, S)
  \<Longrightarrow> S \<union> V \<subseteq> fst (F_LR_MACHINE__fp_one G F k E V S)"
  apply(rule Un_least)
   apply(rule F_LR_MACHINE__fp_one_fst_monotone2)
   apply(force)
  apply(rule F_LR_MACHINE__fp_one_fst_monotone)
  apply(force)
  done

lemma Theorem6__27_a1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_epda M"
  apply(simp add: valid_epda_def)
  apply(simp add: F_LR_MACHINE_def)
  apply(auto)
      apply(rule F_LR_MACHINE_all_finite_fst)
       apply(force)
      apply(force)
     apply(simp add: two_elements_construct_domain_def)
     apply(auto)
      apply(rule finite_imageI)
      apply(simp add: valid_cfg_def)
     apply(rule finite_imageI)
     apply(simp add: valid_cfg_def)
    apply(rule F_LR_MACHINE_all_finite_snd)
     apply(blast)
    apply(force)
   apply(rule_tac
      A="{F_VALID_ITEM_SET_INITIAL G F k} \<union> {}"
      in set_mp)
    apply(rule F_LR_MACHINE__fp_one_mono_fst)
    apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_epda_step_label_def)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
   apply(simp add: may_terminated_by_def append_language_def kleene_star_def)
   apply(simp add: option_to_set_def)
   apply(erule_tac
      x="x"
      in ballE)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule F_LR_MACHINE_all_edgesOK)
   apply(blast)+
  done

lemma Theorem6__27_a2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_pda M"
  apply(simp add: valid_pda_def)
  apply(rule conjI)
   apply(rule Theorem6__27_a1)
     apply(blast)
    apply(blast)
   apply(force)
  apply(simp add: F_LR_MACHINE_def)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(force)
  apply(rule F_LR_MACHINE_all_edgesOK)
   apply(blast)
  apply(blast)
  done

lemma Theorem6__27_a3: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dpda M"
  apply(simp add: valid_dpda_def)
  apply(rule conjI)
   apply(rule Theorem6__27_a2)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(simp add: epdaS.is_forward_edge_deterministic_accessible_def)
  apply(rule ballI)
  apply(rename_tac c)(*strict*)
  apply(rule allI)+
  apply(rename_tac c c1 c2 e1 e2)(*strict*)
  apply(rule impI)
  apply(clarsimp)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c c1 c2 e1 e2 w wa)(*strict*)
  apply(case_tac c)
  apply(rename_tac c c1 c2 e1 e2 w wa epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
  apply(case_tac c1)
  apply(rename_tac c c1 c2 e1 e2 w wa epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka epdaS_conf_stateaa epdaS_conf_scheduleraa epdaS_conf_stackaa)(*strict*)
  apply(case_tac c2)
  apply(rename_tac c c1 c2 e1 e2 w wa epdaS_conf_statea epdaS_conf_schedulera epdaS_conf_stacka epdaS_conf_stateaa epdaS_conf_scheduleraa epdaS_conf_stackaa epdaS_conf_stateb epdaS_conf_schedulerb epdaS_conf_stackb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK)
    apply(blast)
   apply(blast)
  apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
  apply(erule_tac
      x="e1"
      in ballE)
   apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
   prefer 2
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK)
    apply(blast)
   apply(blast)
  apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
  apply(erule_tac
      x="e2"
      in ballE)
   apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
   prefer 2
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac e1 e2 w wa epdaS_conf_schedulera epdaS_conf_schedulerb)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 e2 w epdaS_conf_schedulerb ya)(*strict*)
  apply(subgoal_tac "\<forall>x1 x2. x1 \<in> (snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})) \<and> x2 \<in> (snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})) \<and> (x1\<lparr>edge_trg:=edge_trg x2\<rparr>)=x2 \<longrightarrow> x1=x2")
   apply(rename_tac e1 e2 w epdaS_conf_schedulerb ya)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesDiffer)
    apply(blast)
   apply(blast)
  apply(rename_tac e1 e2 w epdaS_conf_schedulerb ya)(*strict*)
  apply(erule_tac
      x="e1"
      in allE)
  apply(erule_tac
      x="e2"
      in allE)
  apply(erule impE)
   apply(rename_tac e1 e2 w epdaS_conf_schedulerb ya)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac e1 e2 w epdaS_conf_schedulerb ya)(*strict*)
  apply(clarsimp)
  done

theorem Theorem6__27_a: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M"
  apply(simp add: valid_dfa_def)
  apply(rule conjI)
   apply(rule Theorem6__27_a3)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G) (cfg_events G))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK)
    apply(blast)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   apply(clarsimp)
   apply(rename_tac e y)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac e)(*strict*)
  apply(simp add: F_LR_MACHINE_def)
  done

lemma Theorem6__27_c: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> set \<gamma> \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> (\<exists>d e qf. epdaS.derivation M d \<and> maximum_of_domain d (length \<gamma>) \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = epda_initial M, epdaS_conf_scheduler = \<gamma>, epdaS_conf_stack = [epda_box M]\<rparr>) \<and> d (length \<gamma>) = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box M]\<rparr>)) \<longleftrightarrow> (q = valid_item_set G k \<gamma>)"
  apply(clarsimp)
  apply(rule aequI)
   apply(clarsimp)
   apply(rename_tac d e)(*strict*)
   defer
   apply(clarsimp)
   apply(induct \<gamma> rule: rev_induct)
    apply(rule_tac
      t="valid_item_set G k []"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL G F k)"
      in ssubst)
     apply(simp add: Lemma6__23)
    apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
    apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G))"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G)"
      in ssubst)
     apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_idemp)
     apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
     apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
    apply(rule_tac
      x = "der1 \<lparr>epdaS_conf_state = F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G), epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>"
      in exI)
    apply(rule conjI)
     apply(rule epdaS.der1_is_derivation)
    apply(rule conjI)
     apply(rule der1_maximum_of_domain)
    apply(simp add: der1_def)
    apply(simp add: F_LR_MACHINE_def)
    apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
   apply(rename_tac x xs)(*strict*)
   apply(clarsimp)
   apply(rename_tac x xs d e)(*strict*)
   apply(rename_tac a w d e)
   apply(rename_tac a w d e)(*strict*)
   apply(rule_tac
      x = "derivation_append (derivation_map d (\<lambda>v. v\<lparr>epdaS_conf_scheduler:= (epdaS_conf_scheduler v) @ [a]\<rparr>)) (der2 \<lparr>epdaS_conf_state = valid_item_set G k w, epdaS_conf_scheduler = [a], epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr> \<lparr>edge_src=valid_item_set G k w, edge_event=Some a, edge_pop=[epda_box (F_LR_MACHINE G F k)], edge_push=[epda_box (F_LR_MACHINE G F k)], edge_trg=valid_item_set G k (w@[a])\<rparr> \<lparr>epdaS_conf_state = valid_item_set G k (w@[a]), epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>) (length w)"
      in exI)
   apply(rename_tac a w d e)(*strict*)
   apply(rule conjI)
    apply(rename_tac a w d e)(*strict*)
    apply(rule epdaS.derivation_concat2)
       apply(rename_tac a w d e)(*strict*)
       apply(rule epdaS.derivation_map_preserves_derivation2)
        apply(rename_tac a w d e)(*strict*)
        apply(blast)
       apply(rename_tac a w d e)(*strict*)
       apply(clarsimp)
       apply(rename_tac a w d e aa ea b)(*strict*)
       apply(simp add: epdaS_step_relation_def)
      apply(rename_tac a w d e)(*strict*)
      apply(rule derivation_map_preserves_maximum_of_domain)
      apply(blast)
     apply(rename_tac a w d e)(*strict*)
     apply(rule epdaS.der2_is_derivation)
     apply(simp add: epdaS_step_relation_def)
     apply(simp add: option_to_list_def)
     apply(simp (no_asm) add: F_LR_MACHINE_def)
     apply(rule_tac
      t="0"
      and s="epda_box (F_LR_MACHINE G F k)"
      in ssubst)
      apply(rename_tac a w d e)(*strict*)
      apply(simp add: F_LR_MACHINE_def)
     apply(rename_tac a w d e)(*strict*)
     apply(rule F_LR_MACHINE_all_insert_edge_valid_item_set)
         apply(rename_tac a w d e)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac a w d e)(*strict*)
       apply(force)
      apply(rename_tac a w d e)(*strict*)
      apply(subgoal_tac "set (w@[a]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
       apply(rename_tac a w d e)(*strict*)
       apply(rule two_elements_construct_domain_setA)
       apply(force)
      apply(rename_tac a w d e)(*strict*)
      apply(rule two_elements_construct_domain_append)
       apply(rename_tac a w d e)(*strict*)
       apply(force)
      apply(rename_tac a w d e)(*strict*)
      apply(force)
     apply(rename_tac a w d e)(*strict*)
     apply(subgoal_tac "set (w@[a]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
      apply(rename_tac a w d e)(*strict*)
      apply(rule two_elements_construct_domain_setB)
      apply(force)
     apply(rename_tac a w d e)(*strict*)
     apply(rule two_elements_construct_domain_append)
      apply(rename_tac a w d e)(*strict*)
      apply(force)
     apply(rename_tac a w d e)(*strict*)
     apply(force)
    apply(rename_tac a w d e)(*strict*)
    apply(simp add: derivation_map_def der2_def)
   apply(rename_tac a w d e)(*strict*)
   apply(rule conjI)
    apply(rename_tac a w d e)(*strict*)
    apply(rule_tac
      t="Suc (length w)"
      and s="length w+Suc 0"
      in ssubst)
     apply(rename_tac a w d e)(*strict*)
     apply(force)
    apply(rename_tac a w d e)(*strict*)
    apply(rule concat_has_max_dom)
     apply(rename_tac a w d e)(*strict*)
     apply(rule derivation_map_preserves_maximum_of_domain)
     apply(blast)
    apply(rename_tac a w d e)(*strict*)
    apply(rule der2_maximum_of_domain)
   apply(rename_tac a w d e)(*strict*)
   apply(simp add: derivation_append_def)
   apply(simp add: derivation_map_def der2_def)
  apply(rename_tac d e)(*strict*)
  apply(subgoal_tac "\<forall>n d e q \<gamma>1 \<gamma>2. epdaS.derivation (F_LR_MACHINE G F k) d \<and> set \<gamma>1 \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<and> n=length \<gamma>1 \<and> maximum_of_domain d n \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state = epda_initial (F_LR_MACHINE G F k), epdaS_conf_scheduler = \<gamma>1@\<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>) \<and> d n = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = \<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>) \<longrightarrow> q = valid_item_set G k \<gamma>1")
   apply(rename_tac d e)(*strict*)
   apply(erule_tac
      x="length \<gamma>"
      in allE)
   apply(erule_tac
      x="d"
      in allE)
   apply(erule_tac
      x="e"
      in allE)
   apply(erule_tac
      x="q"
      in allE)
   apply(erule_tac
      x="\<gamma>"
      in allE)
   apply(erule_tac
      x="[]"
      in allE)
   apply(force)
  apply(rename_tac d e)(*strict*)
  apply(thin_tac "epdaS.derivation (F_LR_MACHINE G F k) d")
  apply(thin_tac "maximum_of_domain d (length \<gamma>)")
  apply(thin_tac "d 0 = Some (pair None \<lparr>epdaS_conf_state = epda_initial (F_LR_MACHINE G F k), epdaS_conf_scheduler = \<gamma>, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>)")
  apply(thin_tac "d (length \<gamma>) = Some (pair e \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = [], epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>)")
  apply(thin_tac "set \<gamma> \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
  apply(rule allI)
  apply(rename_tac d e n)(*strict*)
  apply(induct_tac n)
   apply(rename_tac d e n)(*strict*)
   apply(clarsimp)
   apply(rename_tac d \<gamma>2)(*strict*)
   apply(simp (no_asm) add: F_LR_MACHINE_def)
   apply(rule_tac
      t="valid_item_set G k []"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL G F k)"
      in ssubst)
    apply(rename_tac d \<gamma>2)(*strict*)
    apply(simp add: Lemma6__23)
   apply(rename_tac d \<gamma>2)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G))"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_INITIAL__fp_start G)"
      in ssubst)
    apply(rename_tac d \<gamma>2)(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_idemp)
    apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
    apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
   apply(rename_tac d \<gamma>2)(*strict*)
   apply(blast)
  apply(rename_tac d e n na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d e q \<gamma>1 \<gamma>2)(*strict*)
  apply(subgoal_tac "\<exists>e c. d na = Some (pair e c)")
   apply(rename_tac na d e q \<gamma>1 \<gamma>2)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom)
     apply(rename_tac na d e q \<gamma>1 \<gamma>2)(*strict*)
     apply(blast)
    apply(rename_tac na d e q \<gamma>1 \<gamma>2)(*strict*)
    apply(blast)
   apply(rename_tac na d e q \<gamma>1 \<gamma>2)(*strict*)
   apply(arith)
  apply(rename_tac na d e q \<gamma>1 \<gamma>2)(*strict*)
  apply(erule exE)+
  apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
  apply(subgoal_tac "(epdaS_conf_scheduler c=drop na (epdaS_conf_scheduler \<lparr>epdaS_conf_state = epda_initial (F_LR_MACHINE G F k), epdaS_conf_scheduler = \<gamma>1@\<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>)) \<and> (length (epdaS_conf_scheduler \<lparr>epdaS_conf_state = epda_initial (F_LR_MACHINE G F k), epdaS_conf_scheduler = \<gamma>1@\<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>) = na + (length (epdaS_conf_scheduler c)))")
   apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
   prefer 2
   apply(rule_tac
      M="F_LR_MACHINE G F k"
      in DFA_derivation_drops_stepwise)
        apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
        apply(rule Theorem6__27_a)
          apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
          apply(blast)
         apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
         apply(blast)
        apply(force)
       apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
       apply(blast)
      apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
      apply(blast)
     apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
     apply(arith)
    apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
    apply(blast)
   apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
   apply(blast)
  apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "length \<gamma>1 = Suc na")
   apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
   prefer 2
   apply(arith)
  apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
  apply(subgoal_tac " (epdaS_conf_scheduler \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = \<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>=drop (Suc na) (epdaS_conf_scheduler \<lparr>epdaS_conf_state = epda_initial (F_LR_MACHINE G F k), epdaS_conf_scheduler = \<gamma>1@\<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>)) \<and> (length (epdaS_conf_scheduler \<lparr>epdaS_conf_state = epda_initial (F_LR_MACHINE G F k), epdaS_conf_scheduler = \<gamma>1@\<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>) = (Suc na) + (length (epdaS_conf_scheduler \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = \<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>)))")
   apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
   prefer 2
   apply(rule_tac
      M="F_LR_MACHINE G F k"
      in DFA_derivation_drops_stepwise)
        apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
        apply(rule Theorem6__27_a)
          apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
          apply(blast)
         apply(force)
        apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
        apply(blast)
       apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
       apply(blast)
      apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
      apply(blast)
     apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
     apply(arith)
    apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
    apply(force)
   apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
   apply(force)
  apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc na) = Some (pair (Some e) c)")
   apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
   prefer 2
   apply(rule epdaS.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
     apply(blast)
    apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
    apply(blast)
   apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
   apply(arith)
  apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c)(*strict*)
  apply(erule exE)+
  apply(rename_tac na d e q \<gamma>1 \<gamma>2 ea c eb ca)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
  apply(subgoal_tac "epdaS_step_relation (F_LR_MACHINE G F k) c eb \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = \<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>")
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   prefer 2
   apply(rule_tac
      n="na"
      in epdaS.position_change_due_to_step_relation)
     apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
     apply(blast)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(blast)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(blast)
  apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
  apply(subgoal_tac "valid_dfa (F_LR_MACHINE G F k)")
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   prefer 2
   apply(rule Theorem6__27_a)
     apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
     apply(blast)
    apply(force)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(blast)
  apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
  apply(subgoal_tac "epdaS_conf_stack c=[epda_box (F_LR_MACHINE G F k)]")
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   prefer 2
   apply(simp add: valid_dfa_def)
   apply(clarsimp)
   apply(erule_tac
      x="eb"
      in ballE)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(clarsimp)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb y)(*strict*)
    apply(simp add: epdaS_step_relation_def)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
  apply(erule_tac
      x="derivation_take d na"
      in allE)
  apply(erule_tac
      x="ea"
      in allE)
  apply(erule_tac
      x="epdaS_conf_state c"
      in allE)
  apply(erule_tac
      x="take na \<gamma>1"
      in allE)
  apply(erule impE)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(rule_tac epdaS.derivation_take_preserves_derivation)
    apply(blast)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(subgoal_tac "length \<gamma>1 \<ge> na")
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    prefer 2
    apply(clarsimp)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(rule_tac
      B="set \<gamma>1"
      in subset_trans)
     apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(force)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(force)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(rule_tac
      m="Suc 0"
      in epdaS.derivation_take_preserves_generates_maximum_of_domain)
     apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
     apply(blast)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(clarsimp)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(rule_tac
      x="drop na \<gamma>1@\<gamma>2"
      in exI)
   apply(rule conjI)
    apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   apply(simp add: derivation_take_def)
  apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
  apply(thin_tac "epdaS.derivation (F_LR_MACHINE G F k) d")
  apply(thin_tac "d 0 = Some (pair None \<lparr>epdaS_conf_state = epda_initial (F_LR_MACHINE G F k), epdaS_conf_scheduler = \<gamma>1 @ \<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>)")
  apply(thin_tac "d (Suc na) = Some (pair (Some eb) \<lparr>epdaS_conf_state = q, epdaS_conf_scheduler = \<gamma>2, epdaS_conf_stack = [epda_box (F_LR_MACHINE G F k)]\<rparr>)")
  apply(thin_tac "d na = Some (pair ea c)")
  apply(thin_tac "maximum_of_domain d (Suc na)")
  apply(subgoal_tac "eb=\<lparr>edge_src=valid_item_set G k (take na \<gamma>1), edge_event=Some (last (drop na \<gamma>1)), edge_pop=[epda_box (F_LR_MACHINE G F k)], edge_push=[epda_box (F_LR_MACHINE G F k)], edge_trg=q\<rparr>")
   apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
   prefer 2
   apply(simp add: valid_dfa_def)
   apply(rename_tac na q \<gamma>1 \<gamma>2 c eb)(*strict*)
   apply(clarsimp)
   apply(erule_tac
      x="eb"
      in ballE)
    apply(rename_tac na q \<gamma>1 \<gamma>2 c eb)(*strict*)
    apply(clarsimp)
    apply(rename_tac na q \<gamma>1 \<gamma>2 c eb y)(*strict*)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac na \<gamma>1 \<gamma>2 c eb y)(*strict*)
    apply(case_tac eb)
    apply(rename_tac na \<gamma>1 \<gamma>2 c eb y edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
    apply(clarsimp)
    apply(rename_tac na \<gamma>1 \<gamma>2 c y edge_trg)(*strict*)
    apply(simp add: option_to_list_def)
    apply (metis take_last2)
   apply(rename_tac na q \<gamma>1 \<gamma>2 c eb)(*strict*)
   apply(simp add: epdaS_step_relation_def)
  apply(rename_tac na d q \<gamma>1 \<gamma>2 ea c eb)(*strict*)
  apply(clarsimp)
  apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
  apply(simp add: epdaS_step_relation_def)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(subgoal_tac "\<forall>x1 x2. x1 \<in> (snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})) \<and> x2 \<in> (snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})) \<and> (x1\<lparr>edge_trg:=edge_trg x2\<rparr>)=x2 \<longrightarrow> x1=x2")
   apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesDiffer)
    apply(blast)
   apply(force)
  apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = valid_item_set G k (take na \<gamma>1), edge_event = Some (last \<gamma>1), edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = q\<rparr>"
      in allE)
  apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
  apply(erule_tac
      x="\<lparr>edge_src = valid_item_set G k (take na \<gamma>1), edge_event = Some (last \<gamma>1), edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = valid_item_set G k ((take na \<gamma>1) @ [last \<gamma>1])\<rparr>"
      in allE)
  apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
  apply(erule impE)
   apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
   apply(rule conjI)
    apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
   apply(rule conjI)
    apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
    apply(rule F_LR_MACHINE_all_insert_edge_valid_item_set)
        apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
      apply(force)
     apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
     apply(rule_tac
      t="take na \<gamma>1 @ [last \<gamma>1]"
      and s="\<gamma>1"
      in ssubst)
      apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
      apply(rule_tac
      t="[last \<gamma>1]"
      and s="drop na \<gamma>1"
      in ssubst)
       apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
       apply(force)
      apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
      apply(rule append_take_drop_id)
     apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(force)
    apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
    apply(rule_tac
      t="take na \<gamma>1 @ [last \<gamma>1]"
      and s="\<gamma>1"
      in ssubst)
     apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
     apply(rule_tac
      t="[last \<gamma>1]"
      and s="drop na \<gamma>1"
      in ssubst)
      apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
      apply(force)
     apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
     apply(rule append_take_drop_id)
    apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
   apply(force)
  apply(rename_tac na q \<gamma>1 \<gamma>2 c)(*strict*)
  apply(clarsimp)
  apply(rename_tac na \<gamma>1 \<gamma>2 c)(*strict*)
  apply(subgoal_tac "take na \<gamma>1 @ [last \<gamma>1]=\<gamma>1")
   apply(rename_tac na \<gamma>1 \<gamma>2 c)(*strict*)
   apply(clarsimp)
  apply(rename_tac na \<gamma>1 \<gamma>2 c)(*strict*)
  apply(rule take_last)
  apply(blast)
  done

theorem F_LR_MACHINE_all_epdaS_accessible_states: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> q \<in> epdaS_accessible_states M"
  apply(simp add: epdaS_accessible_states_def)
  apply(subgoal_tac "\<exists>w. q=valid_item_set G k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)}")
    prefer 2
    apply(rule LRM_contains_theEqClasses)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)+
  apply(rename_tac w)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "(\<exists>d e qf. epdaS.derivation M d \<and> maximum_of_domain d (length w) \<and> d 0 = Some (pair None \<lparr>epdaS_conf_state=epda_initial M, epdaS_conf_scheduler=w, epdaS_conf_stack=[epda_box M]\<rparr>) \<and> d (length w) = Some (pair e \<lparr>epdaS_conf_state=q, epdaS_conf_scheduler=[], epdaS_conf_stack=[epda_box M]\<rparr>)) \<longleftrightarrow> (q=valid_item_set G k w)")
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rule Theorem6__27_c)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(clarsimp)
  apply(rename_tac w d e)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac w d e)(*strict*)
   apply(rule_tac
      x="length w"
      in exI)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
  apply(rename_tac w d e)(*strict*)
  apply(simp add: get_configuration_def)
  apply(simp add: epdaS_initial_configurations_def)
  apply(simp add: epdaS_configurations_def)
  apply(rule conjI)
   apply(rename_tac w d e)(*strict*)
   apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac w d e)(*strict*)
  apply(rule conjI)
   apply(rename_tac w d e)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac w d e)(*strict*)
  apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  done

theorem F_LR_MACHINE_all_epdaS_accessible_states2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> all_states_accessible M"
  apply(simp add: all_states_accessible_def)
  apply(clarsimp)
  apply(rule F_LR_MACHINE_all_epdaS_accessible_states)
      apply(force)
     apply(force)
    apply(force)
   apply(rule Theorem6__27_a)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma Theorem6__27_e: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> S = {q. \<exists>\<gamma>. q = valid_item_set G k \<gamma> \<and> q \<noteq> {}}\<inter> (epda_states M)
  \<Longrightarrow> (epdaS.marked_language (M\<lparr>epda_marking := S\<rparr>)) = Collect (\<lambda>x. viable_prefix G x)"
  oops

lemma Theorem6__27_f: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> (epdaS.marked_language (M\<lparr>epda_marking := epda_states M\<rparr>)) = {w. setA w \<subseteq> cfg_nonterminals G \<and> setB w \<subseteq> cfg_events G}"
  oops

lemma F_LR_MACHINE_all_Connected: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> every_state_in_some_accessible_configuration M"
  apply(rule DFA_Connected_from_ConnectedEx)
   apply(force)
  apply(simp add: every_state_in_some_accessible_configurationEx_def)
  apply(rule ballI)
  apply(rename_tac q)(*strict*)
  apply(subgoal_tac "q \<in> epdaS_accessible_states M")
   apply(rename_tac q)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_all_epdaS_accessible_states)
       apply(rename_tac q)(*strict*)
       apply(force)
      apply(rename_tac q)(*strict*)
      apply(force)
     apply(rename_tac q)(*strict*)
     apply(force)
    apply(rename_tac q)(*strict*)
    apply(force)
   apply(rename_tac q)(*strict*)
   apply(clarsimp)
  apply(simp add: epdaS.get_accessible_configurations_def epdaS_accessible_states_def)
  apply(clarsimp)
  apply(rename_tac q d n)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac q d n)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac q d n a)(*strict*)
  apply(clarsimp)
  apply(case_tac "d 0")
   apply(rename_tac q d n a)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac q d n a aa)(*strict*)
  apply(clarsimp)
  apply(simp add: get_configuration_def)
  apply(case_tac a)
  apply(rename_tac q d n a aa option b)(*strict*)
  apply(case_tac aa)
  apply(rename_tac q d n a aa option b optiona ba)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n option b optiona ba)(*strict*)
  apply(rule_tac
      x="epdaS_conf_scheduler b"
      in exI)
  apply(subgoal_tac "b \<in> epdaS_configurations (F_LR_MACHINE G F k)")
   apply(rename_tac d n option b optiona ba)(*strict*)
   apply(rule conjI)
    apply(rename_tac d n option b optiona ba)(*strict*)
    apply(simp add: epdaS_configurations_def)
    apply(force)
   apply(rename_tac d n option b optiona ba)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule conjI)
    apply(rename_tac d n option b optiona ba)(*strict*)
    apply(simp add: epdaS.derivation_initial_def)
    apply(simp add: epdaS.derivation_def)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
    apply(case_tac "optiona")
     apply(rename_tac d n option b optiona ba)(*strict*)
     apply(force)
    apply(rename_tac d n option b optiona ba a)(*strict*)
    apply(force)
   apply(rename_tac d n option b optiona ba)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(clarsimp)
   apply(subgoal_tac "epdaS_conf_stack b = [epda_box (F_LR_MACHINE G F k)]")
    apply(rename_tac d n option b optiona ba)(*strict*)
    apply(force)
   apply(rename_tac d n option b optiona ba)(*strict*)
   apply(rule_tac
      d="d"
      in DFA_always_box_stack)
     apply(rename_tac d n option b optiona ba)(*strict*)
     apply(force)
    apply(rename_tac d n option b optiona ba)(*strict*)
    apply(simp add: epdaS.derivation_initial_def)
    apply(simp add: epdaS.derivation_def)
    apply(erule_tac
      x="0"
      in allE)
    apply(clarsimp)
    apply(case_tac "optiona")
     apply(rename_tac d n option b optiona ba)(*strict*)
     apply(force)
    apply(rename_tac d n option b optiona ba a)(*strict*)
    apply(force)
   apply(rename_tac d n option b optiona ba)(*strict*)
   apply(force)
  apply(rename_tac d n option b optiona ba)(*strict*)
  apply(rule_tac
      d="d"
      in epdaS.belongs_configurations)
   apply(rename_tac d n option b optiona ba)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d n option b optiona ba)(*strict*)
  apply(rule epdaS.derivation_initial_belongs)
   apply(rename_tac d n option b optiona ba)(*strict*)
   apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
  apply(rename_tac d n option b optiona ba)(*strict*)
  apply(rule epdaS.derivation_initialI)
   apply(rename_tac d n option b optiona ba)(*strict*)
   apply(force)
  apply(rename_tac d n option b optiona ba)(*strict*)
  apply(simp add: get_configuration_def)
  done

theorem F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_dfa (F_LR_MACHINE G F k)
  \<Longrightarrow> some_step_from_every_configuration (F_LR_MACHINE G F k)
  \<Longrightarrow> x' \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> p \<in> epda_states (F_LR_MACHINE G F k)
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G F k x' p = F_DFA_GOTO (F_LR_MACHINE G F k) p x'"
  apply(rule equalsFUNF_DFA_GOTO)
       apply(force)
      apply(force)
     apply(rule F_LR_MACHINE_all_Connected)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: F_LR_MACHINE_def)
  apply(subgoal_tac "\<lparr>edge_src = p, edge_event = Some x', edge_pop = [epda_box (F_LR_MACHINE G F k)], edge_push = [epda_box (F_LR_MACHINE G F k)], edge_trg = F_VALID_ITEM_SET_GOTO G F k x' p\<rparr> \<in> snd (F_LR_MACHINE__fp_one G F k {} {} {F_VALID_ITEM_SET_INITIAL G F k})")
   prefer 2
   apply(rule F_LR_MACHINE_complete)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: F_LR_MACHINE_def)
  apply(simp add: F_LR_MACHINE_def)
  done

lemma F_LR_MACHINE_goes_to_F_VALID_ITEM_SET_GOTO: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> X \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> e = \<lparr>edge_src = q, edge_event = Some X, edge_pop = [0], edge_push = [0], edge_trg = q'\<rparr>
  \<Longrightarrow> e \<in> epda_delta M
  \<Longrightarrow> q' = F_VALID_ITEM_SET_GOTO G F k X q"
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G F k X q"
      and s="F_DFA_GOTO (F_LR_MACHINE G F k) q X"
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
        apply(force)+
  apply(rule equalsFUNF_DFA_GOTO)
       apply(blast)+
     apply(rule F_LR_MACHINE_all_Connected)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: F_LR_MACHINE_def)
  apply(simp add: F_LR_MACHINE_def)
  done

theorem F_LR_MACHINE_all_SOUND: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> valid_item_set G k w = (if w = [] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
  apply(rule_tac
      t="valid_item_set G k w"
      and s="valid_item_set__recursive G F k w"
      in ssubst)
   apply(rule valid_item_set_to_valid_item_set__recursive)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "setA w \<subseteq> cfg_nonterminals G \<and> setB w \<subseteq> cfg_events G \<longrightarrow> valid_item_set__recursive G F k w = (if w = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))")
   apply(force)
  apply(thin_tac "setA w \<subseteq> cfg_nonterminals G")
  apply(thin_tac "setB w \<subseteq> cfg_events G")
  apply(induct w rule: length_induct)
  apply(rename_tac xs)(*strict*)
  apply(case_tac "length xs")
   apply(rename_tac xs)(*strict*)
   apply(clarsimp)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac xs nat)(*strict*)
  apply(rule impI)
  apply(rename_tac w n)
  apply(rename_tac w n)(*strict*)
  apply(rule_tac
      t="valid_item_set__recursive G F k w"
      and s="(case w of [] \<Rightarrow> F_VALID_ITEM_SET_INITIAL G F k | y#w' \<Rightarrow> F_VALID_ITEM_SET_GOTO G F k (last w) (valid_item_set__recursive G F k (butlast w)))"
      in ssubst)
   apply(rename_tac w n)(*strict*)
   apply(rule valid_item_set__recursive.simps)
  apply(rename_tac w n)(*strict*)
  apply(case_tac w)
   apply(rename_tac w n)(*strict*)
   apply(clarsimp)
  apply(rename_tac w n a list)(*strict*)
  defer
  apply(rule_tac
      t="(case w of [] \<Rightarrow> F_VALID_ITEM_SET_INITIAL G F k | y # w' \<Rightarrow> F_VALID_ITEM_SET_GOTO G F k (last w) (valid_item_set__recursive G F k (butlast w)))"
      and s="F_VALID_ITEM_SET_GOTO G F k (last w) (valid_item_set__recursive G F k (butlast w))"
      in ssubst)
   apply(rename_tac w n a list)(*strict*)
   apply(force)
  apply(rename_tac w n a list)(*strict*)
  apply(rule_tac
      t="(if w = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
   apply(rename_tac w n a list)(*strict*)
   apply(force)
  apply(rename_tac w n a list)(*strict*)
  apply(subgoal_tac "\<exists>w' x'. w = w' @ [x']")
   apply(rename_tac w n a list)(*strict*)
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(rename_tac w n a list)(*strict*)
  apply(erule exE)+
  apply(rename_tac w n a list w' x')(*strict*)
  apply(erule_tac
      x="w'"
      in allE)
  apply(erule impE)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(erule impE)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(erule impE)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(erule impE)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(erule impE)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(erule impE)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(erule impE)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(thin_tac "w=a#list")
   apply(rule conjI)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(simp only: setAConcat concat_asso)
    apply(blast)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(simp only: setBConcat concat_asso)
   apply(blast)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(rule_tac
      t="butlast w"
      and s="w'"
      in ssubst)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(rule_tac
      t="last w"
      and s="x'"
      in ssubst)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(subgoal_tac "epda_initial (F_LR_MACHINE G F k) \<in> epda_states (F_LR_MACHINE G F k)")
   apply(rename_tac w n a list w' x')(*strict*)
   prefer 2
   apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(subgoal_tac "set w' \<subseteq> epda_events (F_LR_MACHINE G F k)")
   apply(rename_tac w n a list w' x')(*strict*)
   prefer 2
   apply(rule_tac
      B="set w"
      in subset_trans)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(rule_tac
      t="epda_events (F_LR_MACHINE G F k)"
      and s="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in ssubst)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s=" if w'=[] then F_DFA_GOTO M (epda_initial M) x' else F_DFA_GOTO M (last(F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) x' "
      in ssubst)
   apply(rename_tac w n a list w' x')(*strict*)
   defer
   apply(rule_tac
      t="(valid_item_set__recursive G F k w')"
      and s="(if w' = [] then epda_initial M else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w'))"
      in ssubst)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(thin_tac "w=a#list")
   apply(case_tac "w'")
    apply(rename_tac w n a list w' x')(*strict*)
    apply(clarsimp)
    apply(rename_tac x')(*strict*)
    apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
         apply(rename_tac x')(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac x')(*strict*)
       apply(force)
      apply(rename_tac x')(*strict*)
      apply(force)
     apply(rename_tac x')(*strict*)
     apply(simp add: two_elements_construct_domain_def)
     apply(case_tac x')
      apply(rename_tac x' a)(*strict*)
      apply(force)
     apply(rename_tac x' b)(*strict*)
     apply(force)
    apply(rename_tac x')(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO G F k x' (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) = F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) x'")
    apply(rename_tac w n a list w' x' aa lista)(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(subgoal_tac "\<exists>w'' x'. w' = w'' @ [x']")
    apply(rename_tac w n a list w' x' aa lista)(*strict*)
    prefer 2
    apply(rule NonEmptyListHasTailElem)
    apply(force)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(erule exE)+
   apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
   apply(thin_tac "w'=aa#lista")
   apply(rule_tac
      t="M"
      and s="F_LR_MACHINE G F k"
      in ssubst)
    apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
        apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
    apply(case_tac x')
     apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal ab)(*strict*)
     apply(simp add: two_elements_construct_domain_def)
     apply(rename_tac w n w' x' w'' x'nonterminal ab)(*strict*)
     apply(rule disjI1)
     apply(clarsimp)
     apply(rename_tac w'' x'nonterminal ab)(*strict*)
     apply(simp only: setAConcat concat_asso)
     apply(clarsimp)
    apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal b)(*strict*)
    apply(simp add: two_elements_construct_domain_def)
    apply(rename_tac w n w' x' w'' x'nonterminal b)(*strict*)
    apply(rule disjI2)
    apply(clarsimp)
    apply(rename_tac w'' x'nonterminal b)(*strict*)
    apply(simp only: setBConcat concat_asso)
    apply(clarsimp)
   apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
   apply(rule_tac
      A="set ((F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G F k) (epda_initial (F_LR_MACHINE G F k)) w'))"
      in set_mp)
    apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
    apply(rule_tac
      w="w'"
      and q="(epda_initial (F_LR_MACHINE G F k))"
      in F_DFA_GOTO_SEQUENCESound_main3)
         apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
          apply(force)
         apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
      apply(force)
     apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
   apply(rule last_in_set)
   apply(subgoal_tac "length w'=length (F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G F k) (epda_initial (F_LR_MACHINE G F k)) w')")
    apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
   apply(rule_tac
      w="w'"
      and q="(epda_initial (F_LR_MACHINE G F k))"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
      apply(force)
     apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
     apply(force)
    apply(rename_tac w n a list w' x' aa lista w'' x'nonterminal)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(subgoal_tac "x' \<in> epda_events M")
   apply(rename_tac w n a list w' x')(*strict*)
   prefer 2
   apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in ssubst)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(rule_tac
      A="set [x']"
      in set_mp)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(thin_tac "w=a#list")
    apply(case_tac x')
     apply(rename_tac w n a list w' x' aa)(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac w n a list w' x' aa)(*strict*)
      apply(clarsimp)
     apply(rename_tac w n a list w' x' aa)(*strict*)
     apply(simp add: setAConcat concat_asso)
    apply(rename_tac w n a list w' x' b)(*strict*)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(rename_tac w n a list w' x' b)(*strict*)
     apply(simp only: setBConcat concat_asso)
     apply(clarsimp)
    apply(rename_tac w n a list w' x' b)(*strict*)
    apply(clarsimp)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x')(*strict*)
  apply(case_tac "w'")
   apply(rename_tac w n a list w' x')(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) w"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) [x']"
      in ssubst)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [x']"
      and s="[F_DFA_GOTO M (epda_initial M) x']"
      in ssubst)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
        apply(rename_tac w n a list w' x')(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x')(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x')(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac w n a list w' x')(*strict*)
         apply(force)
        apply(rename_tac w n a list w' x')(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x')(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x')(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in ssubst)
     apply(rename_tac w n a list w' x')(*strict*)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(rule_tac
      A="set [a]"
      in set_mp)
     apply(rename_tac w n a list w' x')(*strict*)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(rename_tac w n a list w' x')(*strict*)
      apply(force)
     apply(rename_tac w n a list w' x')(*strict*)
     apply(force)
    apply(rename_tac w n a list w' x')(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x')(*strict*)
   apply(clarsimp)
  apply(rename_tac w n a list w' x' aa lista)(*strict*)
  apply(rule_tac
      t="(if w' = [] then F_DFA_GOTO M (epda_initial M) x' else F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) x')"
      and s="F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) x'"
      in ssubst)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x' aa lista)(*strict*)
  apply(rule sym)
  apply(rule_tac
      t="F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) x'"
      and s="last [F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) x']"
      in ssubst)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x' aa lista)(*strict*)
  apply(rule_tac
      t="[F_DFA_GOTO M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) x']"
      and s="F_DFA_GOTO_SEQUENCE M (last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w')) [x']"
      in ssubst)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(rule sym)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(rename_tac w n a list w' x' aa lista)(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista)(*strict*)
      apply(force)
     apply(rename_tac w n a list w' x' aa lista)(*strict*)
     apply(rule F_LR_MACHINE_all_Connected)
        apply(rename_tac w n a list w' x' aa lista)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista)(*strict*)
      apply(force)
     apply(rename_tac w n a list w' x' aa lista)(*strict*)
     apply(force)
    apply(rename_tac w n a list w' x' aa lista)(*strict*)
    apply(rule_tac
      A="set ((F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G F k) (epda_initial (F_LR_MACHINE G F k)) w'))"
      in set_mp)
     apply(rename_tac w n a list w' x' aa lista)(*strict*)
     apply(rule_tac
      w="w'"
      and q="(epda_initial (F_LR_MACHINE G F k))"
      in F_DFA_GOTO_SEQUENCESound_main3)
          apply(rename_tac w n a list w' x' aa lista)(*strict*)
          apply(force)
         apply(rename_tac w n a list w' x' aa lista)(*strict*)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista)(*strict*)
        apply(rule F_LR_MACHINE_all_Connected)
           apply(rename_tac w n a list w' x' aa lista)(*strict*)
           apply(force)
          apply(force)
         apply(rename_tac w n a list w' x' aa lista)(*strict*)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista)(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista)(*strict*)
      apply(force)
     apply(rename_tac w n a list w' x' aa lista)(*strict*)
     apply(force)
    apply(rename_tac w n a list w' x' aa lista)(*strict*)
    apply(rule_tac
      t="M"
      and s="F_LR_MACHINE G F k"
      in ssubst)
     apply(rename_tac w n a list w' x' aa lista)(*strict*)
     apply(force)
    apply(rename_tac w n a list w' x' aa lista)(*strict*)
    apply(rule last_in_set)
    apply(subgoal_tac "length w'=length (F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G F k) (epda_initial (F_LR_MACHINE G F k)) w')")
     apply(rename_tac w n a list w' x' aa lista)(*strict*)
     apply(force)
    apply(rename_tac w n a list w' x' aa lista)(*strict*)
    apply(rule_tac
      w="w'"
      and q="(epda_initial (F_LR_MACHINE G F k))"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac w n a list w' x' aa lista)(*strict*)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac w n a list w' x' aa lista)(*strict*)
          apply(force)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista)(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista)(*strict*)
      apply(force)
     apply(rename_tac w n a list w' x' aa lista)(*strict*)
     apply(force)
    apply(rename_tac w n a list w' x' aa lista)(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x' aa lista)(*strict*)
  apply(rule_tac
      t="w"
      and s="w'@[x']"
      in ssubst)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x' aa lista)(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_concat)
         apply(rename_tac w n a list w' x' aa lista)(*strict*)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac w n a list w' x' aa lista)(*strict*)
          apply(force)
         apply(force)
        apply(rename_tac w n a list w' x' aa lista)(*strict*)
        apply(force)
       apply(rename_tac w n a list w' x' aa lista)(*strict*)
       apply(force)
      apply(rename_tac w n a list w' x' aa lista)(*strict*)
      apply(force)
     apply(rename_tac w n a list w' x' aa lista)(*strict*)
     apply(force)
    apply(rename_tac w n a list w' x' aa lista)(*strict*)
    apply(force)
   apply(rename_tac w n a list w' x' aa lista)(*strict*)
   apply(force)
  apply(rename_tac w n a list w' x' aa lista)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_all_SOUND_Nil: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> w = []
  \<Longrightarrow> valid_item_set G k w = epda_initial M"
  apply(rule_tac
      t="valid_item_set G k w"
      and s="(if w=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      in ssubst)
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(blast)+
  apply(force)
  done

lemma F_LR_MACHINE_all_SOUND_NotNil: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> valid_item_set G k w = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
  apply(rule_tac
      t="valid_item_set G k w"
      and s="(if w=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      in ssubst)
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(blast)+
  apply(force)
  done

lemma F_LR_MACHINE_all_SOUND_NotNil2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> valid_item_set G k w = last (q # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
  apply(rule_tac
      t="valid_item_set G k w"
      and s="(if w=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      in ssubst)
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(blast)+
  apply(clarsimp)
  apply(subgoal_tac "length w=length (F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G F k) (epda_initial (F_LR_MACHINE G F k)) w)")
   prefer 2
   apply(rule_tac
      w="w"
      and q="(epda_initial (F_LR_MACHINE G F k))"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: F_LR_MACHINE_def)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(simp add: F_LR_MACHINE_def)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_insertion_implies_F_VALID_ITEM_SET_GOTO_to_target: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> e \<in> epda_delta M
  \<Longrightarrow> \<exists>q X. q \<in> epda_states M \<and> edge_trg e = F_VALID_ITEM_SET_GOTO G' F k X q"
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G' F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})")
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK_prime)
    apply(force)
   apply(force)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rule_tac
      x="edge_src e"
      in exI)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac y)(*strict*)
   apply(erule conjE)+
   apply(rule_tac
      x="y"
      in exI)
   apply(simp add: F_LR_MACHINE_def)
  apply(simp add: F_LR_MACHINE_def)
  done

lemma F_LR_MACHINE_target_not_initial: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> e \<in> epda_delta M
  \<Longrightarrow> edge_trg e \<noteq> epda_initial M"
  apply(subgoal_tac "\<exists>q X. q \<in> epda_states M \<and> edge_trg e = F_VALID_ITEM_SET_GOTO G' F k X q")
   prefer 2
   apply(rule_tac
      G="G"
      in F_LR_MACHINE_insertion_implies_F_VALID_ITEM_SET_GOTO_to_target)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)+
  apply(rename_tac q X)(*strict*)
  apply(rule_tac
      t="edge_trg e"
      and s="F_VALID_ITEM_SET_GOTO G' F k X q"
      in ssubst)
   apply(rename_tac q X)(*strict*)
   apply(force)
  apply(rename_tac q X)(*strict*)
  apply(rule not_sym)
  apply(rule_tac
      t="epda_initial M"
      and s="F_VALID_ITEM_SET_INITIAL G' F k"
      in ssubst)
   apply(rename_tac q X)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac q X)(*strict*)
  apply(rule F_VALID_ITEM_SET_GOTO_does_not_reach_F_LR_MACHINE_initial)
        apply(rename_tac q X)(*strict*)
        apply(force)
       apply(rename_tac q X)(*strict*)
       apply(force)
      apply(rename_tac q X)(*strict*)
      apply(force)
     apply(rename_tac q X)(*strict*)
     apply(force)
    apply(rename_tac q X)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac q X)(*strict*)
  apply(subgoal_tac "q \<in> {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
   apply(rename_tac q X)(*strict*)
   prefer 2
   apply(rule_tac
      t="{valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}"
      and s="epda_states M"
      in ssubst)
    apply(rename_tac q X)(*strict*)
    apply(rule sym)
    apply(rule LRM_contains_theEqClasses)
      apply(rename_tac q X)(*strict*)
      apply(force)
     apply(rename_tac q X)(*strict*)
     apply(force)
    apply(rename_tac q X)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac q X)(*strict*)
  apply(rule ballI)
  apply(rename_tac q X I)(*strict*)
  apply(clarsimp)
  apply(rename_tac X I w)(*strict*)
  apply(rule_tac
      \<gamma>="w"
      in Fact6_12__2)
   apply(rename_tac X I w)(*strict*)
   apply(force)
  apply(rename_tac X I w)(*strict*)
  apply(clarsimp)
  done

lemma State_With_Item_from_G_is_reached_via_Dollar_w: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> cfg_item_lhs I \<in> cfg_nonterminals G
  \<Longrightarrow> \<exists>w. q = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w)) \<and> (set w \<subseteq> epda_events M)"
  apply(subgoal_tac "\<exists>w. q=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
    apply(force)
   apply(rule LRM_contains_theEqClasses)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)+
  apply(rename_tac w)(*strict*)
  apply(rule_tac
      x="drop (Suc 0) w"
      in exI)
  apply(erule conjE)+
  apply(rule conjI)
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rule_tac
      B="set w"
      in subset_trans)
    apply(rename_tac w)(*strict*)
    apply(thin_tac "q = valid_item_set G' k w")
    apply(thin_tac "set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(induct_tac w)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w a list)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac w)(*strict*)
  apply(case_tac "\<exists>w'. w=[teB Do]@w'")
   apply(rename_tac w)(*strict*)
   apply(erule exE)+
   apply(rename_tac w w')(*strict*)
   apply(rule_tac
      t="q"
      and s="valid_item_set G' k w"
      in ssubst)
    apply(rename_tac w w')(*strict*)
    apply(force)
   apply(rename_tac w w')(*strict*)
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # drop (Suc 0) w))"
      and s="(if w=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # drop (Suc 0) w)))"
      in ssubst)
    apply(rename_tac w w')(*strict*)
    apply(clarsimp)
   apply(rename_tac w w')(*strict*)
   apply(rule_tac
      t="teB Do # drop (Suc 0) w"
      and s="w"
      in ssubst)
    apply(rename_tac w w')(*strict*)
    apply(force)
   apply(rename_tac w w')(*strict*)
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(rename_tac w w')(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac w w')(*strict*)
       apply(force)
      apply(rename_tac w w')(*strict*)
      apply(force)
     apply(rename_tac w w')(*strict*)
     apply(force)
    apply(rename_tac w w')(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(force)
   apply(rename_tac w w')(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(case_tac w)
   apply(rename_tac w)(*strict*)
   apply(subgoal_tac "False")
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(subgoal_tac "I\<notin>valid_item_set G' k []")
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      t="valid_item_set G' k []"
      and s="(if []=[] then F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k) else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (essential_items (valid_item_set G' k [])))"
      in ssubst)
    apply(rename_tac w)(*strict*)
    apply(rule Lemma6__23)
       apply(rename_tac w)(*strict*)
       apply(force)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      t="(if [] = [] then F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k) else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (essential_items (valid_item_set G' k [])))"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k)"
      in ssubst)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k)"
      and s="(F_VALID_ITEM_SET_INITIAL G' F k)"
      in ssubst)
    apply(rename_tac w)(*strict*)
    apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL_F_VALID_ITEM_SET_GOTO__descent__fp)
         apply(rename_tac w)(*strict*)
         apply(force)
        apply(rename_tac w)(*strict*)
        apply(force)
       apply(rename_tac w)(*strict*)
       apply(force)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G' F k"
      and s="{\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
    apply(rename_tac w)(*strict*)
    apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL)
         apply(rename_tac w)(*strict*)
         apply(force)
        apply(rename_tac w)(*strict*)
        apply(force)
       apply(rename_tac w)(*strict*)
       apply(force)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(subgoal_tac "cfg_item_lhs I\<noteq>S'")
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(subgoal_tac "S' \<notin> cfg_nonterminals G")
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      t="S'"
      and s="F_FRESH (cfg_nonterminals G)"
      in ssubst)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rename_tac w a list)(*strict*)
  apply(subgoal_tac "I\<notin>valid_item_set G' k (a#list)")
   apply(rename_tac w a list)(*strict*)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(subgoal_tac "a\<noteq>teB Do")
   apply(rename_tac w a list)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(thin_tac "\<not> (\<exists>w'. w = [teB Do] @ w')")
  apply(case_tac "I \<notin> valid_item_set G' k (a # list)")
   apply(rename_tac w a list)(*strict*)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac w a list)(*strict*)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(subgoal_tac "\<exists>n. I \<in> valid_item_set_n G' k n w")
   apply(rename_tac w a list)(*strict*)
   prefer 2
   apply(simp only: valid_item_set_def)
   apply(clarsimp)
  apply(rename_tac w a list)(*strict*)
  apply(erule exE)+
  apply(rename_tac w a list n)(*strict*)
  apply(subgoal_tac "\<exists>A \<alpha> \<beta> y. I = \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr> \<and> (\<exists>d \<delta> e1 e2 z. cfgRM.derivation G' d \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=\<delta>@[teA A]@z\<rparr>) \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf=\<delta>@\<alpha>@\<beta>@z\<rparr>) \<and> take k z=liftB y \<and> w=\<delta>@\<alpha> \<and> maximum_of_domain d (Suc n) \<and> setA z = {})")
   apply(rename_tac w a list n)(*strict*)
   prefer 2
   apply(simp add: valid_item_set_n_def)
  apply(rename_tac w a list n)(*strict*)
  apply(erule exE)+
  apply(rename_tac w a list n A \<alpha> \<beta> y)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
   apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(blast)
  apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(subgoal_tac "\<exists>e w. d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w\<rparr>)")
   apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and m="Suc 0"
      and n="n"
      in terminal_at_beginning_are_never_modified)
       apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(erule exE)+
  apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
  apply(subgoal_tac "teB Do # wa\<noteq>\<delta> @ \<alpha> @ \<beta> @ z")
   apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
   apply(force)
  apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
  apply(rule_tac
      t="\<delta> @ \<alpha> @ \<beta> @ z"
      and s="w @ \<beta> @ z"
      in ssubst)
   apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
   apply(force)
  apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
  apply(rule_tac
      t="w"
      and s="a#list"
      in ssubst)
   apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
   apply(force)
  apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
  apply(rule_tac
      a="teB Do"
      and w="wa"
      and b="a"
      and v="list@\<beta>@z"
      in unequal_by_first_char)
    apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
    apply(blast)
   apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
   apply(force)
  apply(rename_tac w a list n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_States_contain_Items: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> valid_item G k I"
  apply(subgoal_tac "\<exists>w. q=valid_item_set G k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)}")
    prefer 2
    apply(rule LRM_contains_theEqClasses)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)+
  apply(rename_tac w)(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(force)
  done

lemma DollarTailStays: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> q \<in> (epda_states M)
  \<Longrightarrow> \<forall>I \<in> q. (cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (cfg_item_lhs I \<noteq> S' \<longrightarrow> ((cfg_item_look_ahead I) \<in> ((kPrefix k) ` ({w @ [Do]|w. set w \<subseteq> (cfg_events G)}))))"
  apply(rule_tac
      M="M"
      and P="\<lambda>q. \<forall>I \<in> q. (cfg_item_lhs I=S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (cfg_item_lhs I\<noteq>S' \<longrightarrow> ((cfg_item_look_ahead I) \<in> ((kPrefix k) ` ({w@[Do]|w. set w \<subseteq> (cfg_events G)})))) "
      in InductOverReachables)
     apply(rule_tac
      G="G'"
      and M="M"
      and k="k"
      in Theorem6__27_a1)
       apply(force)
      apply(force)
     apply(force)
    apply(rule_tac
      t="epda_initial M"
      and s="F_VALID_ITEM_SET_INITIAL G' F k"
      in ssubst)
     apply(simp add: F_LR_MACHINE_def)
    apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G' F k"
      and s="{\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
     apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
   apply(rule allI)+
   apply(rename_tac p e qa cp cq)(*strict*)
   apply(rule impI)+
   apply(subgoal_tac "p \<in> epda_states M")
    apply(rename_tac p e qa cp cq)(*strict*)
    prefer 2
    apply(simp add: epdaS_accessible_states_def)
   apply(rename_tac p e qa cp cq)(*strict*)
   apply(subgoal_tac "\<exists>w. p=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(rename_tac p e qa cp cq)(*strict*)
    prefer 2
    apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
     apply(rename_tac p e qa cp cq)(*strict*)
     apply(force)
    apply(rename_tac p e qa cp cq)(*strict*)
    apply(rule LRM_contains_theEqClasses)
      apply(rename_tac p e qa cp cq)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac p e qa cp cq)(*strict*)
    apply(force)
   apply(rename_tac p e qa cp cq)(*strict*)
   apply(erule exE)
   apply(rename_tac p e qa cp cq w)(*strict*)
   apply(erule conjE)+
   apply(subgoal_tac "valid_dfa M")
    apply(rename_tac p e qa cp cq w)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      in Theorem6__27_a)
      apply(rename_tac p e qa cp cq w)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac p e qa cp cq w)(*strict*)
    apply(force)
   apply(rename_tac p e qa cp cq w)(*strict*)
   apply(subgoal_tac "\<exists>a. e=\<lparr>edge_src=p, edge_event=Some a, edge_pop=[0], edge_push=[0], edge_trg=qa\<rparr>")
    apply(rename_tac p e qa cp cq w)(*strict*)
    prefer 2
    apply(case_tac e)
    apply(rename_tac p e qa cp cq w edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
    apply(clarsimp)
    apply(rename_tac cp cq w edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
    apply(simp add: epdaS_step_relation_def)
    apply(clarsimp)
    apply(rename_tac cp cq w edge_event edge_pop edge_push wa)(*strict*)
    apply(simp add: valid_dfa_def)
    apply(rename_tac cp cq w edge_eventa edge_popa edge_pusha wa)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>edge_src = epdaS_conf_state cp, edge_event = edge_eventa, edge_pop = edge_popa, edge_push = edge_pusha, edge_trg = epdaS_conf_state cq\<rparr>"
      in ballE)
     apply(rename_tac cp cq w edge_eventa edge_popa edge_pusha wa)(*strict*)
     apply(clarsimp)
     apply(rename_tac cp cq w wa y)(*strict*)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac cp cq w edge_event edge_pop edge_push wa)(*strict*)
    apply(force)
   apply(rename_tac p e qa cp cq w)(*strict*)
   apply(erule exE)+
   apply(rename_tac p e qa cp cq w a)(*strict*)
   apply(subgoal_tac "qa=valid_item_set G' k (w@[a])")
    apply(rename_tac p e qa cp cq w a)(*strict*)
    prefer 2
    apply(subgoal_tac "\<forall>x1 x2. x1 \<in> (snd(F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})) \<and> x2 \<in> (snd(F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})) \<and> (x1\<lparr>edge_trg:=edge_trg x2\<rparr>)=x2 \<longrightarrow> x1=x2")
     apply(rename_tac p e qa cp cq w a)(*strict*)
     prefer 2
     apply(rule F_LR_MACHINE_all_edgesDiffer)
      apply(force)
     apply(force)
    apply(rename_tac p e qa cp cq w a)(*strict*)
    apply(erule_tac
      x="e"
      in allE)
    apply(erule_tac
      x="e\<lparr>edge_trg:=valid_item_set G' k (w@[a])\<rparr>"
      in allE)
    apply(erule impE)
     apply(rename_tac p e qa cp cq w a)(*strict*)
     apply(rule conjI)
      apply(rename_tac p e qa cp cq w a)(*strict*)
      apply(simp add: F_LR_MACHINE_def epda_step_labels_def)
     apply(rename_tac p e qa cp cq w a)(*strict*)
     apply(rule conjI)
      apply(rename_tac p e qa cp cq w a)(*strict*)
      apply(subgoal_tac "\<lparr>edge_src = valid_item_set G' k w, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE G' F k)], edge_push = [epda_box (F_LR_MACHINE G' F k)], edge_trg = valid_item_set G' k (w @ [a])\<rparr> \<in> snd(F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})")
       apply(rename_tac p e qa cp cq w a)(*strict*)
       prefer 2
       apply(rule F_LR_MACHINE_all_insert_edge_valid_item_set)
           apply(rename_tac p e qa cp cq w a)(*strict*)
           apply(force)
          apply(force)
         apply(rename_tac p e qa cp cq w a)(*strict*)
         apply(force)
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(subgoal_tac "set (w@[a]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
         apply(rename_tac p e qa cp cq w a)(*strict*)
         apply(rule two_elements_construct_domain_setA)
         apply(force)
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(rule two_elements_construct_domain_append)
         apply(rename_tac p e qa cp cq w a)(*strict*)
         apply(force)
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(rule_tac
      t="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      and s="epda_events M"
      in ssubst)
         apply(rename_tac p e qa cp cq w a)(*strict*)
         apply(simp add: F_LR_MACHINE_def)
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(rule epda_read_in_epda_events)
          apply(rename_tac p e qa cp cq w a)(*strict*)
          apply(rule_tac
      G="G'"
      in Theorem6__27_a1)
            apply(rename_tac p e qa cp cq w a)(*strict*)
            apply(force)
           apply(force)
          apply(rename_tac p e qa cp cq w a)(*strict*)
          apply(force)
         apply(rename_tac p e qa cp cq w a)(*strict*)
         apply(simp add: epda_step_labels_def)
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(force)
       apply(rename_tac p e qa cp cq w a)(*strict*)
       apply(subgoal_tac "set (w@[a]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(rule two_elements_construct_domain_setB)
        apply(force)
       apply(rename_tac p e qa cp cq w a)(*strict*)
       apply(rule two_elements_construct_domain_append)
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(force)
       apply(rename_tac p e qa cp cq w a)(*strict*)
       apply(rule_tac
      t="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      and s="epda_events M"
      in ssubst)
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(simp add: F_LR_MACHINE_def)
       apply(rename_tac p e qa cp cq w a)(*strict*)
       apply(rule epda_read_in_epda_events)
         apply(rename_tac p e qa cp cq w a)(*strict*)
         apply(rule_tac
      G="G'"
      in Theorem6__27_a1)
           apply(rename_tac p e qa cp cq w a)(*strict*)
           apply(force)
          apply(force)
         apply(rename_tac p e qa cp cq w a)(*strict*)
         apply(force)
        apply(rename_tac p e qa cp cq w a)(*strict*)
        apply(simp add: epda_step_labels_def)
       apply(rename_tac p e qa cp cq w a)(*strict*)
       apply(force)
      apply(rename_tac p e qa cp cq w a)(*strict*)
      apply(rule_tac
      t="e\<lparr>edge_trg := valid_item_set G' k (w @ [a])\<rparr>"
      and s="\<lparr>edge_src = valid_item_set G' k w, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE G' F k)], edge_push = [epda_box (F_LR_MACHINE G' F k)], edge_trg = valid_item_set G' k (w @ [a])\<rparr>"
      in ssubst)
       apply(rename_tac p e qa cp cq w a)(*strict*)
       apply(clarsimp)
       apply(rename_tac cp cq w a)(*strict*)
       apply(simp add: F_LR_MACHINE_def)
      apply(rename_tac p e qa cp cq w a)(*strict*)
      apply(force)
     apply(rename_tac p e qa cp cq w a)(*strict*)
     apply(clarsimp)
    apply(rename_tac p e qa cp cq w a)(*strict*)
    apply(clarsimp)
   apply(rename_tac p e qa cp cq w a)(*strict*)
   apply(rule_tac
      t="qa"
      and s="F_VALID_ITEM_SET_GOTO G' F k a (valid_item_set G' k w)"
      in ssubst)
    apply(rename_tac p e qa cp cq w a)(*strict*)
    apply(rule_tac
      t="qa"
      and s="valid_item_set G' k (w @ [a])"
      in ssubst)
     apply(rename_tac p e qa cp cq w a)(*strict*)
     apply(force)
    apply(rename_tac p e qa cp cq w a)(*strict*)
    apply(subgoal_tac "a \<in> epda_events M")
     apply(rename_tac p e qa cp cq w a)(*strict*)
     prefer 2
     apply(simp only: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(erule conjE)+
     apply(erule_tac
      x="\<lparr>edge_src = p, edge_event = Some a, edge_pop = [0], edge_push = [0], edge_trg = qa\<rparr>"
      and P="\<lambda>x. valid_epda_step_label (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k) x"
      in ballE)
      apply(rename_tac p e qa cp cq w a)(*strict*)
      apply(simp add: valid_epda_step_label_def option_to_set_def)
     apply(rename_tac p e qa cp cq w a)(*strict*)
     apply(simp add: epda_step_labels_def)
    apply(rename_tac p e qa cp cq w a)(*strict*)
    apply(rule Lemma6__26)
       apply(rename_tac p e qa cp cq w a)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac p e qa cp cq w a)(*strict*)
     apply(simp add: F_LR_MACHINE_def)
     apply(rule two_elements_construct_domain_setA)
     apply(force)
    apply(rename_tac p e qa cp cq w a)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rename_tac p e qa cp cq w a)(*strict*)
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G' F k a (valid_item_set G' k w)"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w))"
      in ssubst)
    apply(rename_tac p e qa cp cq w a)(*strict*)
    apply(simp add: F_VALID_ITEM_SET_GOTO_def)
   apply(rename_tac p e qa cp cq w a)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_all_epdaS_accessible_states)
       apply(blast)+
    apply(rule_tac
      G="G'"
      in Theorem6__27_a)
      apply(blast)
     apply(force)
    apply(blast)
   apply(blast)
  apply(rename_tac p e qa cp cq w a)(*strict*)
  apply(subgoal_tac "\<forall>I \<in> F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w). (cfg_item_lhs I = S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_look_ahead I \<in> kPrefix k ` {w @ [Do] |w. set w \<subseteq> cfg_events G})")
   apply(rename_tac p e qa cp cq w a)(*strict*)
   apply(rule ballI)
   apply(rename_tac p e qa cp cq w a I)(*strict*)
   apply(rule_tac
      S="F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w)"
      in F_VALID_ITEM_SET_GOTO__descent__fp_new_is_from_old_G)
            apply(rename_tac p e qa cp cq w a I)(*strict*)
            apply(force)
           apply(force)
          apply(rename_tac p e qa cp cq w a I)(*strict*)
          apply(force)
         apply(rename_tac p e qa cp cq w a I)(*strict*)
         apply(force)
        apply(rename_tac p e qa cp cq w a I)(*strict*)
        apply(force)
       apply(rename_tac p e qa cp cq w a I)(*strict*)
       apply(force)
      apply(rename_tac p e qa cp cq w a I)(*strict*)
      apply(force)
     apply(rename_tac p e qa cp cq w a I)(*strict*)
     apply(force)
    apply(rename_tac p e qa cp cq w a I)(*strict*)
    apply(force)
   apply(rename_tac p e qa cp cq w a I)(*strict*)
   apply(rule ballI)
   apply(rename_tac p e qa cp cq w a I Ia)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__basis a p \<subseteq> Collect(valid_item G' k)")
    apply(rename_tac p e qa cp cq w a I Ia)(*strict*)
    apply(force)
   apply(rename_tac p e qa cp cq w a I Ia)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
   apply(clarsimp)
   apply(rename_tac cp cq w a I Ia x)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac cp cq w a I Ia x)(*strict*)
    apply(force)
   apply(rename_tac cp cq w a I Ia x)(*strict*)
   apply(force)
  apply(rename_tac p e qa cp cq w a)(*strict*)
  apply(clarsimp)
  apply(rename_tac cp cq w a I)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(clarsimp)
  apply(rename_tac cp cq w a I I1)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(clarsimp)
  apply(erule_tac
      x="I1"
      in ballE)
   apply(rename_tac cp cq w a I I1)(*strict*)
   apply(clarsimp)
  apply(rename_tac cp cq w a I I1)(*strict*)
  apply(force)
  done

lemma LRM_contains_theEqClasses_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> \<exists>w. q = valid_item_set G k w"
  apply(subgoal_tac "epda_states M = {valid_item_set G k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)}")
   prefer 2
   apply(rule LRM_contains_theEqClasses)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_item_in_state_rhs2_in_cfg_events: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> set (cfg_item_rhs2 I) \<subseteq> epda_events M"
  apply(subgoal_tac "\<exists>w. q=valid_item_set G k w")
   prefer 2
   apply(rule LRM_contains_theEqClasses_prime)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)+
  apply(rename_tac w)(*strict*)
  apply(subgoal_tac "valid_item G k I")
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rule Fact6_12__2)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(simp add: valid_item_def)
  apply(erule conjE)+
  apply(erule bexE)+
  apply(rename_tac w p)(*strict*)
  apply(erule conjE)+
  apply(simp add: valid_cfg_def)
  apply(erule conjE)+
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac w p)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
   apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
    apply(rename_tac w p)(*strict*)
    apply(simp add: setBConcat concat_asso)
   apply(rename_tac w p)(*strict*)
   apply(simp add: setAConcat concat_asso)
  apply(rename_tac w p)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_item_in_state_lhs_in_cfg_events: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> \<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr> \<in> cfg_productions G
  \<Longrightarrow> teA (cfg_item_lhs I) \<in> epda_events M"
  apply(subgoal_tac "set [teA (cfg_item_lhs I)] \<subseteq> epda_events M")
   prefer 2
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(simp only: valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_item_lhs I, prod_rhs = cfg_item_rhs1 I @ cfg_item_rhs2 I\<rparr>"
      in ballE)
     apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
      apply(clarsimp)
     apply(clarsimp)
    apply(force)
   apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
    apply(simp add: two_elements_construct_domain_def F_CFG_AUGMENT_def)
   apply(simp add: F_LR_MACHINE_def)
  apply(force)
  done

theorem F_LR_MACHINE_has_finite_states: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> finite q"
  apply(rule_tac
      B = "Collect (valid_item G k)"
      in finite_subset)
   prefer 2
   apply(rule finite_ItemSet)
   apply(force)
  apply(subgoal_tac "\<exists>w. q=valid_item_set G k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)}")
    apply(force)
   apply(rule LRM_contains_theEqClasses)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)
  apply(rename_tac w)(*strict*)
  apply(erule conjE)+
  apply(rule subsetI)
  apply(rename_tac w x)(*strict*)
  apply(subgoal_tac "valid_item G k x")
   apply(rename_tac w x)(*strict*)
   apply(force)
  apply(rename_tac w x)(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac w x)(*strict*)
   apply(force)
  apply(rename_tac w x)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_prefix_closureise_additionalItems_0: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> v = [teB Do, teA (cfg_initial G), teB Do]
  \<Longrightarrow> w = []
  \<Longrightarrow> (last ((epda_initial M) # (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))) = {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = w, cfg_item_rhs2 = v, cfg_item_look_ahead = []\<rparr>}"
  apply(subgoal_tac "epda_initial (F_LR_MACHINE G' F k) \<in> epda_states (F_LR_MACHINE G' F k)")
   prefer 2
   apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
  apply(rule_tac
      t="v"
      and s="[teB Do, teA (cfg_initial G), teB Do]"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="w"
      and s="[]"
      in ssubst)
   apply(force)
  apply(thin_tac "v = [teB Do, teA (cfg_initial G), teB Do]")
  apply(thin_tac "w = []")
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [])"
      and s="F_VALID_ITEM_SET_INITIAL G' F k"
      in ssubst)
   prefer 2
   apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) []"
      and s="[]"
      in ssubst)
   apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
    prefer 2
    apply(rule_tac
      w="[]"
      and q="(epda_initial (F_LR_MACHINE G' F k))"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(rule F_LR_MACHINE_all_Connected)
          prefer 3
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="last [epda_initial M]"
      and s="epda_initial M"
      in ssubst)
   apply(force)
  apply(simp add: F_LR_MACHINE_def)
  done

lemma F_LR_MACHINE_prefix_closureise_additionalItems_1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> v = [teA (cfg_initial G), teB Do]
  \<Longrightarrow> w = [teB Do]
  \<Longrightarrow> (last ((epda_initial M) # (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))) -{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} = {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = w, cfg_item_rhs2 = v, cfg_item_look_ahead = []\<rparr>}"
  apply(rule_tac
      t="w"
      and s="[teB Do]"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="v"
      and s="[teA (cfg_initial G), teB Do]"
      in ssubst)
   apply(force)
  apply(thin_tac "w = [teB Do]")
  apply(thin_tac "v = [teA (cfg_initial G), teB Do]")
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      and s="valid_item_set G' k [teB Do]"
      in ssubst)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
    apply(subgoal_tac "length [teB Do]=length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])")
     prefer 2
     apply(rule_tac
      w="[teB Do]"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(force)
         apply(force)
        apply(rule F_LR_MACHINE_all_Connected)
           prefer 3
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
     apply(force)
    apply(force)
   apply(rule sym)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(force)
  apply(rule order_antisym)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(rename_tac I)
   apply(rename_tac I)(*strict*)
   apply(subgoal_tac "valid_item G' k I")
    apply(rename_tac I)(*strict*)
    apply(subgoal_tac "\<exists>n. I \<in> valid_item_set_n G' k n [teB Do]")
     apply(rename_tac I)(*strict*)
     prefer 2
     apply(simp only: valid_item_set_def)
     apply(clarsimp)
    apply(rename_tac I)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n)(*strict*)
    apply(subgoal_tac "\<exists>A \<alpha> \<beta> y. I = \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr> \<and> (\<exists>d \<delta> e1 e2 z. cfgRM.derivation G' d \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=\<delta>@[teA A]@z\<rparr>) \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf=\<delta>@\<alpha>@\<beta>@z\<rparr>) \<and> take k z=liftB y \<and> [teB Do]=\<delta>@\<alpha> \<and> maximum_of_domain d (Suc n) \<and> setA z = {})")
     apply(rename_tac I n)(*strict*)
     prefer 2
     apply(simp add: valid_item_set_n_def)
    apply(rename_tac I n)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(erule conjE)+
    apply(subgoal_tac "I=\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     prefer 2
     apply(rule F_CFG_AUGMENT__FirstStep)
            apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
            apply(force)
           apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
           apply(force)
          apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(blast)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(case_tac n)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> z)(*strict*)
     apply(case_tac \<delta>)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> z)(*strict*)
      apply(clarsimp)
      apply(rename_tac y d)(*strict*)
      apply(rule conjI)
       apply(rename_tac y d)(*strict*)
       apply(simp add: F_CFG_AUGMENT_def)
      apply(rename_tac y d)(*strict*)
      apply(rule liftB_reflects_Nil)
      apply(force)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> z a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(subgoal_tac "\<exists>e w. d (Suc nat) = Some (pair e \<lparr>cfg_conf = teB Do # w\<rparr>)")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     prefer 2
     apply(rule_tac
      G="G'"
      and m="Suc 0"
      and n="Suc nat"
      in terminal_at_beginning_are_never_modified)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
         apply(rule cfgRM_derivations_are_cfg_derivations)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "setA (\<delta> @ [teA A] @ z) \<subseteq> cfg_nonterminals G")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(rule F_CFG_AUGMENT__later_at_old_grammar)
            apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
            apply(force)
           apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
           apply(force)
          apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
          apply(force)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "A \<in> cfg_nonterminals G")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(rule_tac
      ?w1.0="\<delta>"
      and ?w2.0="z"
      in suffixes_setA_2)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(rule suffixes_intro2)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "\<lparr>prod_lhs=A, prod_rhs=\<alpha>@\<beta>\<rparr> \<in> cfg_productions G'")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(simp add: valid_item_def)
     apply(clarsimp)
     apply(rename_tac \<alpha> \<beta> y d \<delta> e1 e2 z nat w p)(*strict*)
     apply(case_tac p)
     apply(rename_tac \<alpha> \<beta> y d \<delta> e1 e2 z nat w p prod_lhsa prod_rhsa)(*strict*)
     apply(clarsimp)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(case_tac "\<lparr>prod_lhs=A, prod_rhs=\<alpha>@\<beta>\<rparr> \<in> cfg_productions G")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(subgoal_tac "\<lparr>prod_lhs = A, prod_rhs = \<alpha> @ \<beta>\<rparr> = \<lparr>prod_lhs=S', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>")
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      prefer 2
      apply(simp add: F_CFG_AUGMENT_def)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      prefer 2
      apply(rule F_FRESH_is_fresh)
      apply(simp add: valid_cfg_def)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "item_core I=\<lparr>prod_lhs = A, prod_rhs = \<alpha> @ \<beta>\<rparr>")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(clarsimp)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(simp add: item_core_def)
   apply(rename_tac I)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac I)(*strict*)
    apply(force)
   apply(rename_tac I)(*strict*)
   apply(force)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k [teB Do]")
   prefer 2
   apply(simp add: valid_item_set_def valid_item_set_n_def)
   apply(clarsimp)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      x = "der2 \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr> \<lparr>prod_lhs=cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))), prod_rhs=[teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr> \<lparr>cfg_conf = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr> "
      in exI)
   apply(rule conjI)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(rule conjI)
     apply(simp add: F_CFG_AUGMENT_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rule conjI)
    apply(simp add: der2_def)
   apply(simp add: der2_def)
   apply(fold der2_def)
   apply(rule conjI)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rule der2_maximum_of_domain)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>\<notin>{I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}")
   prefer 2
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    prefer 2
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(simp add: item_core_def valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>"
      and P="\<lambda>x. prod_lhs x \<in> cfg_nonterminals G \<and> setA (prod_rhs x) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs x) \<subseteq> cfg_events G"
      in ballE)
    apply(clarsimp)
   apply(clarsimp)
  apply(force)
  done

lemma F_LR_MACHINE_prefix_closureise_additionalItems_2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> v = [teB Do]
  \<Longrightarrow> w = [teB Do, teA (cfg_initial G)]
  \<Longrightarrow> (last ((epda_initial M) # (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))) -{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} = {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = w, cfg_item_rhs2 = v, cfg_item_look_ahead = []\<rparr>}"
  apply(rule_tac
      t="w"
      and s="[teB Do, teA (cfg_initial G)]"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="v"
      and s="[teB Do]"
      in ssubst)
   apply(force)
  apply(thin_tac "v = [teB Do]")
  apply(thin_tac "w = [teB Do, teA (cfg_initial G)]")
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="valid_item_set G' k [teB Do, teA (cfg_initial G)]"
      in ssubst)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
    apply(subgoal_tac "length [teB Do, teA (cfg_initial G)]=length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
     prefer 2
     apply(rule_tac
      w="[teB Do, teA (cfg_initial G)]"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(force)
         apply(force)
        apply(rule F_LR_MACHINE_all_Connected)
           prefer 3
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
     apply(force)
    apply(force)
   apply(rule sym)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
    apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
   apply(force)
  apply(rule order_antisym)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(rename_tac I)
   apply(rename_tac I)(*strict*)
   apply(subgoal_tac "valid_item G' k I")
    apply(rename_tac I)(*strict*)
    apply(subgoal_tac "\<exists>n. I \<in> valid_item_set_n G' k n [teB Do, teA (cfg_initial G)]")
     apply(rename_tac I)(*strict*)
     prefer 2
     apply(simp only: valid_item_set_def)
     apply(clarsimp)
    apply(rename_tac I)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n)(*strict*)
    apply(subgoal_tac "\<exists>A \<alpha> \<beta> y. I = \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr> \<and> (\<exists>d \<delta> e1 e2 z. cfgRM.derivation G' d \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=\<delta>@[teA A]@z\<rparr>) \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf=\<delta>@\<alpha>@\<beta>@z\<rparr>) \<and> take k z=liftB y \<and> [teB Do, teA (cfg_initial G)]=\<delta>@\<alpha> \<and> maximum_of_domain d (Suc n) \<and> setA z = {})")
     apply(rename_tac I n)(*strict*)
     prefer 2
     apply(simp add: valid_item_set_n_def)
    apply(rename_tac I n)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(erule conjE)+
    apply(subgoal_tac "I=\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     prefer 2
     apply(rule F_CFG_AUGMENT__FirstStep)
            apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
            apply(force)
           apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
           apply(force)
          apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(blast)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(case_tac n)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> z)(*strict*)
     apply(case_tac \<delta>)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> z)(*strict*)
      apply(clarsimp)
      apply(rename_tac y d)(*strict*)
      apply(rule conjI)
       apply(rename_tac y d)(*strict*)
       apply(simp add: F_CFG_AUGMENT_def)
      apply(rename_tac y d)(*strict*)
      apply(rule liftB_reflects_Nil)
      apply(force)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> z a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(subgoal_tac "\<exists>e w. d (Suc nat) = Some (pair e \<lparr>cfg_conf = teB Do # w\<rparr>)")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     prefer 2
     apply(rule_tac
      G="G'"
      and m="Suc 0"
      and n="Suc nat"
      in terminal_at_beginning_are_never_modified)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
         apply(rule cfgRM_derivations_are_cfg_derivations)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "setA (\<delta> @ [teA A] @ z) \<subseteq> cfg_nonterminals G")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(rule F_CFG_AUGMENT__later_at_old_grammar)
            apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
            apply(force)
           apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
           apply(force)
          apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
          apply(force)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "False")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "A \<in> cfg_nonterminals G")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(rule_tac
      ?w1.0="\<delta>"
      and ?w2.0="z"
      in suffixes_setA_2)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(rule suffixes_intro2)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "\<lparr>prod_lhs=A, prod_rhs=\<alpha>@\<beta>\<rparr> \<in> cfg_productions G'")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(simp add: valid_item_def)
     apply(clarsimp)
     apply(rename_tac \<alpha> \<beta> y d \<delta> e1 e2 z nat w p)(*strict*)
     apply(case_tac p)
     apply(rename_tac \<alpha> \<beta> y d \<delta> e1 e2 z nat w p prod_lhsa prod_rhsa)(*strict*)
     apply(clarsimp)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(case_tac "\<lparr>prod_lhs=A, prod_rhs=\<alpha>@\<beta>\<rparr> \<in> cfg_productions G")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(subgoal_tac "\<lparr>prod_lhs = A, prod_rhs = \<alpha> @ \<beta>\<rparr> = \<lparr>prod_lhs=S', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>")
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      prefer 2
      apply(simp add: F_CFG_AUGMENT_def)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      prefer 2
      apply(rule F_FRESH_is_fresh)
      apply(simp add: valid_cfg_def)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "item_core I=\<lparr>prod_lhs = A, prod_rhs = \<alpha> @ \<beta>\<rparr>")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(clarsimp)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(simp add: item_core_def)
   apply(rename_tac I)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac I)(*strict*)
    apply(force)
   apply(rename_tac I)(*strict*)
   apply(force)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k [teB Do, teA (cfg_initial G)]")
   prefer 2
   apply(simp add: valid_item_set_def valid_item_set_n_def)
   apply(clarsimp)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      x = "der2 \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr> \<lparr>prod_lhs=cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))), prod_rhs=[teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr> \<lparr>cfg_conf = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr> "
      in exI)
   apply(rule conjI)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(rule conjI)
     apply(simp add: F_CFG_AUGMENT_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(simp add: der2_def)
   apply(fold der2_def)
   apply(rule conjI)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rule der2_maximum_of_domain)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>\<notin>{I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}")
   prefer 2
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    prefer 2
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(simp add: item_core_def valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>"
      and P="\<lambda>e. prod_lhs e \<in> cfg_nonterminals G \<and> setA (prod_rhs e) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs e) \<subseteq> cfg_events G"
      in ballE)
    apply(clarsimp)
   apply(clarsimp)
  apply(force)
  done

lemma F_LR_MACHINE_prefix_closureise_additionalItems_3: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> v = []
  \<Longrightarrow> w = [teB Do, teA (cfg_initial G), teB Do]
  \<Longrightarrow> (last ((epda_initial M) # (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))) = {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = w, cfg_item_rhs2 = v, cfg_item_look_ahead = []\<rparr>}"
  apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
   prefer 2
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(subgoal_tac "F_FRESH (cfg_events G) \<notin> cfg_events G")
   prefer 2
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(rule_tac
      t="w"
      and s="[teB Do, teA(cfg_initial G), teB Do]"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="v"
      and s="[]"
      in ssubst)
   apply(force)
  apply(thin_tac "w = [teB Do, teA(cfg_initial G), teB Do]")
  apply(thin_tac "v = []")
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA(cfg_initial G), teB Do])"
      and s="valid_item_set G' k [teB Do, teA(cfg_initial G), teB Do]"
      in ssubst)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA(cfg_initial G), teB Do])"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA(cfg_initial G), teB Do])"
      in ssubst)
    apply(subgoal_tac "length [teB Do, teA(cfg_initial G), teB Do]=length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA(cfg_initial G), teB Do])")
     prefer 2
     apply(rule_tac
      w="[teB Do, teA(cfg_initial G), teB Do]"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(force)
         apply(force)
        apply(rule F_LR_MACHINE_all_Connected)
           prefer 3
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
     apply(force)
    apply(force)
   apply(rule sym)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
    apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
   apply(force)
  apply(rule order_antisym)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(rename_tac I)
   apply(rename_tac I)(*strict*)
   apply(subgoal_tac "valid_item G' k I")
    apply(rename_tac I)(*strict*)
    apply(subgoal_tac "\<exists>n. I \<in> valid_item_set_n G' k n [teB Do, teA(cfg_initial G), teB Do]")
     apply(rename_tac I)(*strict*)
     prefer 2
     apply(simp only: valid_item_set_def)
     apply(clarsimp)
    apply(rename_tac I)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n)(*strict*)
    apply(subgoal_tac "\<exists>A \<alpha> \<beta> y. I = \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr> \<and> (\<exists>d \<delta> e1 e2 z. cfgRM.derivation G' d \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=\<delta>@[teA A]@z\<rparr>) \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf=\<delta>@\<alpha>@\<beta>@z\<rparr>) \<and> take k z=liftB y \<and> [teB Do, teA(cfg_initial G), teB Do]=\<delta>@\<alpha> \<and> maximum_of_domain d (Suc n) \<and> setA z = {})")
     apply(rename_tac I n)(*strict*)
     prefer 2
     apply(simp add: valid_item_set_n_def)
    apply(rename_tac I n)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y)(*strict*)
    apply(erule conjE)+
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(erule conjE)+
    apply(subgoal_tac "I=\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA(cfg_initial G), teB Do], cfg_item_rhs2 = [], cfg_item_look_ahead = []\<rparr>")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     prefer 2
     apply(rule F_CFG_AUGMENT__FirstStep)
            apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
            apply(force)
           apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
           apply(force)
          apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(blast)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(case_tac n)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(clarsimp)
     apply(rename_tac y d)(*strict*)
     apply(rule conjI)
      apply(rename_tac y d)(*strict*)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(rename_tac y d)(*strict*)
     apply(rule liftB_reflects_Nil)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(subgoal_tac "\<exists>e w. d (Suc nat) = Some (pair e \<lparr>cfg_conf = teB Do # w\<rparr>)")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     prefer 2
     apply(rule_tac
      w="[teA (cfg_initial G), teB Do]"
      and G="G'"
      and m="Suc 0"
      and n="Suc nat"
      in terminal_at_beginning_are_never_modified)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
         apply(rule cfgRM_derivations_are_cfg_derivations)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(erule exE)+
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "setA (\<delta> @ [teA A] @ z) \<subseteq> cfg_nonterminals G")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(rule F_CFG_AUGMENT__later_at_old_grammar)
            apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
            apply(force)
           apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
           apply(force)
          apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
          apply(force)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "\<exists>e w. d (Suc nat) = Some (pair e \<lparr>cfg_conf = w @ [teB Do]\<rparr>)")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(rule_tac
      w="[teB Do, teA (cfg_initial G)]"
      and G="G'"
      and m="Suc 0"
      and n="Suc nat"
      in terminal_at_ending_is_never_modified)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
         apply(rule cfgRM_derivations_are_cfg_derivations)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
        apply(force)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(force)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(subgoal_tac "\<exists>e w. d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>) \<and> (set w) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) ")
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     prefer 2
     apply(rule_tac
      m="Suc 0"
      and n="n"
      in cfgRM.property_preseved_under_steps_is_invariant2)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
         apply(force)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
        apply(rule_tac
      x="Some\<lparr>prod_lhs = cfg_initial G', prod_rhs = [teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in exI)
        apply(rule_tac
      x="[teA (cfg_initial G)]"
      in exI)
        apply(rule conjI)
         apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
         apply(clarsimp)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
        apply(simp add: two_elements_construct_domain_def valid_cfg_def)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
       apply(force)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
      apply(force)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
     apply(rule allI)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i)(*strict*)
     apply(rule impI)
     apply(erule conjE)+
     apply(erule exE)+
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb)(*strict*)
     apply(erule conjE)+
     apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb)(*strict*)
      prefer 2
      apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb)(*strict*)
        apply(blast)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb)(*strict*)
       apply(blast)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb)(*strict*)
      apply(arith)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb)(*strict*)
     apply(erule exE)+
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb ec c)(*strict*)
     apply(subgoal_tac "cfgRM_step_relation G' \<lparr>cfg_conf = teB Do # wb @ [teB Do]\<rparr> ec c")
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb ec c)(*strict*)
      prefer 2
      apply(rule_tac
      n="i"
      in cfgRM.position_change_due_to_step_relation)
        apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb ec c)(*strict*)
        apply(blast)
       apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb ec c)(*strict*)
       apply(blast)
      apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb ec c)(*strict*)
      apply(blast)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb ec c)(*strict*)
     apply(case_tac c)
     apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w i ea eb wa wb ec c cfg_conf)(*strict*)
     apply(simp add: cfgRM_step_relation_def)
     apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec l r)(*strict*)
     apply(case_tac l)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec l r)(*strict*)
      apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec l r a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec r list)(*strict*)
     apply(case_tac "r=[]")
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec r list)(*strict*)
      apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec r list)(*strict*)
     apply(subgoal_tac "\<exists>r' a. r=r'@[a]")
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec r list)(*strict*)
      apply(clarsimp)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
      apply(subgoal_tac "ec \<in> cfg_productions G")
       apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
       apply(simp add: valid_cfg_def)
       apply(clarsimp)
       apply(erule_tac
      x="ec"
      and P="\<lambda>ec. prod_lhs ec \<in> cfg_nonterminals G \<and> setA (prod_rhs ec) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs ec) \<subseteq> cfg_events G"
      in ballE)
        apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
        apply(clarsimp)
        apply(rule_tac
      A="set(prod_rhs ec)"
      in set_mp)
         apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
         apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
          apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
          apply(force)
         apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
         apply(force)
        apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
        apply(clarsimp)
       apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
       apply(force)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa ec list r' x)(*strict*)
      apply(simp add: F_CFG_AUGMENT_def)
      apply(clarsimp)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa list r' x)(*strict*)
      apply(subgoal_tac "teA (F_FRESH (cfg_nonterminals G)) \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
       apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa list r' x)(*strict*)
       apply(force)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa list r' x)(*strict*)
      apply(thin_tac "teA (F_FRESH (cfg_nonterminals G)) \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
      apply(simp add: two_elements_construct_domain_def)
      apply(rule conjI)
       apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa list r' x)(*strict*)
       prefer 2
       apply(clarsimp)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa list r' x)(*strict*)
      apply(rule teA_notInMap)
      apply(rule F_FRESH_is_fresh)
      apply(simp add: valid_cfg_def)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec r list)(*strict*)
     apply(rule_tac
      n="length r - 1"
      in NonEmptyListHasTailElem)
     apply(case_tac r)
      apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec r list)(*strict*)
      apply(force)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w i eb wa wb ec r list a lista)(*strict*)
     apply(clarsimp)
    apply(rename_tac I n A \<alpha> \<beta> y d \<delta> e1 e2 z nat e w)(*strict*)
    apply(clarsimp)
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w wa wb)(*strict*)
    apply(case_tac \<delta>)
     apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w wa wb)(*strict*)
     apply(clarsimp)
     apply(rename_tac A \<beta> y d e1 e2 z nat w wa wb)(*strict*)
     apply(subgoal_tac "\<exists>z'. z=z'@[teB (F_FRESH (cfg_events G))]")
      apply(rename_tac A \<beta> y d e1 e2 z nat w wa wb)(*strict*)
      apply(clarsimp)
     apply(rename_tac A \<beta> y d e1 e2 z nat w wa wb)(*strict*)
     apply(case_tac wa)
      apply(rename_tac A \<beta> y d e1 e2 z nat w wa wb)(*strict*)
      apply(clarsimp)
     apply(rename_tac A \<beta> y d e1 e2 z nat w wa wb a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac A \<alpha> \<beta> y d \<delta> e1 e2 z nat w wa wb a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w wa wb list)(*strict*)
    apply(subgoal_tac "\<exists>z'. z=z'@[teB (F_FRESH (cfg_events G))]")
     apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w wa wb list)(*strict*)
     apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list z')(*strict*)
     apply(case_tac list)
      apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list z')(*strict*)
      apply(clarsimp)
      apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
      apply(simp add: two_elements_construct_domain_def)
      apply(erule_tac
      P="teA (cfg_initial G) \<in> teA ` cfg_nonterminals G"
      in disjE)
       apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
       apply(clarsimp)
       apply(erule disjE)
        apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
        apply(clarsimp)
       apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
       apply(clarsimp)
      apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
      apply(erule disjE)
       apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
       apply(clarsimp)
      apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
      apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat list z' a lista)(*strict*)
     apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat z' lista)(*strict*)
     apply(case_tac lista)
      apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat z' lista)(*strict*)
      apply(clarsimp)
      apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
      apply(simp add: two_elements_construct_domain_def)
      apply(erule disjE)
       apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
       apply(clarsimp)
      apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
      apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d e1 e2 nat z' lista a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
     apply(simp add: two_elements_construct_domain_def)
     apply(erule disjE)
      apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
      apply(clarsimp)
     apply(rename_tac A \<beta> y d e1 e2 nat z')(*strict*)
     apply(clarsimp)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w wa wb list)(*strict*)
    apply(case_tac wa)
     apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w wa wb list)(*strict*)
     apply(clarsimp)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat w wa wb list a lista)(*strict*)
    apply(clarsimp)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat wb list lista)(*strict*)
    apply(rule_tac
      u="[]"
      in terminalTailEquals2)
      apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat wb list lista)(*strict*)
      apply(clarsimp)
     apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat wb list lista)(*strict*)
     apply(force)
    apply(rename_tac A \<alpha> \<beta> y d e1 e2 z nat wb list lista)(*strict*)
    apply(force)
   apply(rename_tac I)(*strict*)
   apply(rule Fact6_12__2)
    apply(rename_tac I)(*strict*)
    apply(force)
   apply(rename_tac I)(*strict*)
   apply(force)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2 = [], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k [teB Do, teA (cfg_initial G), teB Do]")
   prefer 2
   apply(simp add: valid_item_set_def valid_item_set_n_def)
   apply(clarsimp)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      x = "der2 \<lparr>cfg_conf = [teA (cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))]\<rparr> \<lparr>prod_lhs=cfg_initial (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))), prod_rhs=[teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr> \<lparr>cfg_conf = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(rule cfgRM.der2_is_derivation)
    apply(simp add: cfgRM_step_relation_def)
    apply(rule conjI)
     apply(simp add: F_CFG_AUGMENT_def)
    apply(rule_tac
      x="[]"
      in exI)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(simp add: der2_def)
   apply(fold der2_def)
   apply(rule conjI)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rule der2_maximum_of_domain)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>\<notin>{I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}")
   prefer 2
   apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
    prefer 2
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(simp add: item_core_def valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      in ballE)
    apply(clarsimp)
   apply(clarsimp)
  apply(force)
  done

lemma F_LR_MACHINE_DFAGTOTO_differs: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<noteq> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<noteq> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<noteq> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<noteq> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<noteq> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<noteq> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<noteq> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
  apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) []) -{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} = {\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}")
   prefer 2
   apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) []) = {\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}")
    prefer 2
    apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_0)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<notin> {I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}")
    apply(force)
   apply(simp add: item_core_def valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      in ballE)
    apply(clarsimp)
    apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
     apply(force)
    apply(rule F_FRESH_is_fresh)
    apply(force)
   apply(force)
  apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) -{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} = {\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do], cfg_item_rhs2=[teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}")
   prefer 2
   apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_1)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) -{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} = {\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G)], cfg_item_rhs2=[teB Do], cfg_item_look_ahead=[]\<rparr>}")
   prefer 2
   apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_2)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) -{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} = {\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2=[], cfg_item_look_ahead=[]\<rparr>}")
   prefer 2
   apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) = {\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2=[], cfg_item_look_ahead=[]\<rparr>}")
    prefer 2
    apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_3)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2 = [], cfg_item_look_ahead = []\<rparr> \<notin> {I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}")
    prefer 2
    apply(simp add: item_core_def valid_cfg_def)
    apply(clarsimp)
    apply(erule_tac
      x="\<lparr>prod_lhs = F_FRESH (cfg_nonterminals G), prod_rhs = [teB (F_FRESH (cfg_events G)), teA (cfg_initial G), teB (F_FRESH (cfg_events G))]\<rparr>"
      and P="\<lambda>p. prod_lhs p \<in> cfg_nonterminals G \<and> setA (prod_rhs p) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs p) \<subseteq> cfg_events G"
      in ballE)
     apply(clarsimp)
     apply(subgoal_tac "F_FRESH (cfg_nonterminals G) \<notin> cfg_nonterminals G")
      apply(force)
     apply(rule F_FRESH_is_fresh)
     apply(force)
    apply(force)
   apply(force)
  apply(rule conjI, force)+
  apply(force)
  done

lemma F_LR_MACHINE_DFAGTOTO_differs2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> \<exists>v. x @ v = [teB Do, teA (cfg_initial G), teB Do]
  \<Longrightarrow> \<exists>v. y @ v = [teB Do, teA (cfg_initial G), teB Do]
  \<Longrightarrow> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) y) \<noteq> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) x)"
  apply(subgoal_tac "last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<and> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) \<noteq> last((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
   prefer 2
   apply(rule F_LR_MACHINE_DFAGTOTO_differs)
           apply(blast)+
  apply(erule exE)+
  apply(rename_tac v va)(*strict*)
  apply(subgoal_tac "x=[] \<or> x=[teB Do] \<or> x=[teB Do, teA (cfg_initial G)] \<or> x=[teB Do, teA (cfg_initial G), teB Do]")
   apply(rename_tac v va)(*strict*)
   prefer 2
   apply(case_tac x)
    apply(rename_tac v va)(*strict*)
    apply(clarsimp)
   apply(rename_tac v va a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac v va a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac v va a list aa lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac v va a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac v va a list aa lista ab listb)(*strict*)
   apply(case_tac listb)
    apply(rename_tac v va a list aa lista ab listb)(*strict*)
    apply(clarsimp)
   apply(rename_tac v va a list aa lista ab listb ac listc)(*strict*)
   apply(clarsimp)
  apply(rename_tac v va)(*strict*)
  apply(subgoal_tac "y=[] \<or> y=[teB Do] \<or> y=[teB Do, teA (cfg_initial G)] \<or> y=[teB Do, teA (cfg_initial G), teB Do]")
   apply(rename_tac v va)(*strict*)
   prefer 2
   apply(case_tac y)
    apply(rename_tac v va)(*strict*)
    apply(clarsimp)
   apply(rename_tac v va a list)(*strict*)
   apply(case_tac list)
    apply(rename_tac v va a list)(*strict*)
    apply(clarsimp)
   apply(rename_tac v va a list aa lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac v va a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac v va a list aa lista ab listb)(*strict*)
   apply(case_tac listb)
    apply(rename_tac v va a list aa lista ab listb)(*strict*)
    apply(clarsimp)
   apply(rename_tac v va a list aa lista ab listb ac listc)(*strict*)
   apply(clarsimp)
  apply(rename_tac v va)(*strict*)
  apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(force)
  apply(rename_tac v va)(*strict*)
  apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(force)
  apply(rename_tac v va)(*strict*)
  apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(force)
  apply(rename_tac v va)(*strict*)
  apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(force)
  apply(rename_tac v va)(*strict*)
  apply(erule disjE)+
    apply(rename_tac v va)(*strict*)
    apply(force)
   apply(rename_tac v va)(*strict*)
   apply(force)
  apply(rename_tac v va)(*strict*)
  apply(erule disjE)+
   apply(rename_tac v va)(*strict*)
   apply(force)
  apply(rename_tac v va)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_DFAGTOTO_differs_hlp1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) = F_DFA_GOTO M (epda_initial M) (teB Do)"
  apply(rule_tac
      t="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])))"
      and s="(last ((F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])))"
      in ssubst)
   apply(subgoal_tac "length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) = length [teB Do]")
    apply(force)
   apply(rule sym)
   apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(rule F_LR_MACHINE_all_Connected)
         prefer 3
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
      and s="[F_DFA_GOTO M (epda_initial M) (teB Do)]"
      in ssubst)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(force)
      apply(force)
     apply(rule F_LR_MACHINE_all_Connected)
        prefer 3
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(force)
  done

lemma F_LR_MACHINE_DFAGTOTO_differs_hlp2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) []) = epda_initial M"
  apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
   apply(force)
  apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
       apply(force)
      apply(force)
     apply(rule F_LR_MACHINE_all_Connected)
        prefer 3
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO_to_1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G' F k X q = valid_item_set G' k []
  \<Longrightarrow> Q"
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO G' F k X q \<noteq> valid_item_set G' k []")
   apply(force)
  apply(rule not_sym)
  apply(rule_tac
      t="valid_item_set G' k []"
      and s="(if []=[] then F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k) else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (essential_items (valid_item_set G' k [])))"
      in ssubst)
   apply(rule Lemma6__23)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="(if [] = [] then F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k) else F_VALID_ITEM_SET_GOTO__descent__fp G' F k (essential_items (valid_item_set G' k [])))"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k)"
      in ssubst)
   apply(clarsimp)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_INITIAL G' F k)"
      and s="F_VALID_ITEM_SET_INITIAL G' F k"
      in ssubst)
   apply(simp add: F_VALID_ITEM_SET_INITIAL_def)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_idemp)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(rule F_VALID_ITEM_SET_INITIAL__fp_start_contains_valid_item)
  apply(rule F_VALID_ITEM_SET_GOTO_does_not_reach_F_LR_MACHINE_initial)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "q \<in> {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
   prefer 2
   apply(rule_tac
      t="{valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}"
      and s="epda_states M"
      in ssubst)
    apply(rule sym)
    apply(rule LRM_contains_theEqClasses)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule ballI)
  apply(rename_tac I)(*strict*)
  apply(clarsimp)
  apply(rename_tac I w)(*strict*)
  apply(rule_tac
      \<gamma>="w"
      in Fact6_12__2)
   apply(rename_tac I w)(*strict*)
   apply(force)
  apply(rename_tac I w)(*strict*)
  apply(clarsimp)
  done

lemma F_VALID_ITEM_SET_GOTO_to_2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> set v \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G' F k X (valid_item_set G' k v) = valid_item_set G' k [teB Do]
  \<Longrightarrow> valid_item_set G' k v = valid_item_set G' k [] \<and> X = teB Do"
  apply(subgoal_tac "\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do], cfg_item_rhs2=[teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr> \<in> valid_item_set G' k [teB Do]")
   prefer 2
   apply(rule_tac
      A="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])))- {I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      in set_mp)
    apply(rule_tac
      t="valid_item_set G' k [teB Do]"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
     apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(force)
    apply(force)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) - {I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      and s="{\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do], cfg_item_rhs2=[teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
    apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_1)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X=teB Do")
   prefer 2
   apply(rule_tac
      S="(valid_item_set G' k v)"
      and I="\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>"
      and w="[]"
      and G="G"
      in F_VALID_ITEM_SET_GOTO_uses_every_last_cfg_item_rhs1_symbol)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule Fact6_12__2)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(force)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k v")
   prefer 2
   apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>\<lparr>cfg_item_rhs1:=[], cfg_item_rhs2:=teB Do#(cfg_item_rhs2 \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>)\<rparr> \<in> valid_item_set G' k v")
    apply(force)
   apply(rule F_LR_MACHINE_shift_back_in_pre_state)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "valid_item_set G' k v \<in> epda_states M")
    prefer 2
    apply(rule_tac
      t="epda_states M"
      and s="{valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}"
      in ssubst)
     apply(rule_tac
      G="G'"
      in LRM_contains_theEqClasses)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "v=[]")
   apply(force)
  apply(rule F_CFG_AUGMENT__Initial_only_in_F_VALID_ITEM_SET_INITIAL)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma DollarReadItem_OnlyIn_Specific_Valid2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = x\<rparr> \<in> (last ((epda_initial M) # (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)))
  \<Longrightarrow> w = [teB Do] \<and> x = []"
  apply(rule DollarReadItem_OnlyIn_Specific_Valid)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(simp add: F_LR_MACHINE_def)
  apply(rule_tac
      t="valid_item_set (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) k w"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)" for k
      in ssubst)
   defer
   apply(force)
  apply(case_tac w)
   apply(subgoal_tac "(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) []))) ={\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}")
    prefer 2
    apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_0)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac a list)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(rename_tac a list)(*strict*)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac a list)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(subgoal_tac " last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w) = valid_item_set G' k w")
   apply(rename_tac a list)(*strict*)
   prefer 2
   apply(rule sym)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rename_tac a list)(*strict*)
    apply(force)
   apply(rename_tac a list)(*strict*)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(rename_tac a list)(*strict*)
          apply(force)
         apply(rename_tac a list)(*strict*)
         apply(force)
        apply(rename_tac a list)(*strict*)
        apply(force)
       apply(rename_tac a list)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac a list)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac a list)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac a list)(*strict*)
   apply(force)
  apply(rename_tac a list)(*strict*)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO_to_3: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> set v \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G' F k X (valid_item_set G' k v) = valid_item_set G' k [teB Do, teA (cfg_initial G)]
  \<Longrightarrow> valid_item_set G' k v = valid_item_set G' k [teB Do] \<and> X = teA (cfg_initial G)"
  apply(subgoal_tac "\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G)], cfg_item_rhs2=[teB Do], cfg_item_look_ahead=[]\<rparr> \<in> valid_item_set G' k [teB Do, teA (cfg_initial G)]")
   prefer 2
   apply(rule_tac
      A="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA(cfg_initial G)])))-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      in set_mp)
    apply(rule_tac
      t="valid_item_set G' k [teB Do, teA (cfg_initial G)]"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
     apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(force)
    apply(force)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) - {I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)}"
      and s="{\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G)], cfg_item_rhs2=[teB Do], cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
    apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_2)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X=teA (cfg_initial G)")
   prefer 2
   apply(rule_tac
      S="(valid_item_set G' k v)"
      and I="\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>"
      and w="[teB Do]"
      and G="G"
      in F_VALID_ITEM_SET_GOTO_uses_every_last_cfg_item_rhs1_symbol)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule Fact6_12__2)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(force)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k v")
   prefer 2
   apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>\<lparr>cfg_item_rhs1:=[teB Do], cfg_item_rhs2:=teA (cfg_initial G)#(cfg_item_rhs2 \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr>)\<rparr> \<in> valid_item_set G' k v")
    apply(force)
   apply(rule F_LR_MACHINE_shift_back_in_pre_state)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "valid_item_set G' k v \<in> epda_states M")
   prefer 2
   apply(rule_tac
      t="epda_states M"
      and s="{valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}"
      in ssubst)
    apply(rule_tac
      G="G'"
      in LRM_contains_theEqClasses)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "v=[teB Do] \<and> []=[]")
   apply(force)
  apply(rule DollarReadItem_OnlyIn_Specific_Valid)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_VALID_ITEM_SET_GOTO_to_4: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> set v \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')
  \<Longrightarrow> F_VALID_ITEM_SET_GOTO G' F k X (valid_item_set G' k v) = valid_item_set G' k [teB Do, teA (cfg_initial G), teB Do]
  \<Longrightarrow> valid_item_set G' k v = valid_item_set G' k [teB Do, teA (cfg_initial G)] \<and> X = teB Do"
  apply(subgoal_tac "\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2=[], cfg_item_look_ahead=[]\<rparr> \<in> valid_item_set G' k [teB Do, teA (cfg_initial G), teB Do]")
   prefer 2
   apply(rule_tac
      A="(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA(cfg_initial G), teB Do])))"
      in set_mp)
    apply(rule_tac
      t="valid_item_set G' k [teB Do, teA (cfg_initial G), teB Do]"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])"
      in ssubst)
     apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(force)
    apply(force)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])"
      and s="{\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2=[], cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
    apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_3)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "X=teB Do")
   prefer 2
   apply(rule_tac
      S="valid_item_set G' k v"
      and I="\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2 = [], cfg_item_look_ahead = []\<rparr>"
      and w="[teB Do, teA (cfg_initial G)]"
      and G="G"
      in F_VALID_ITEM_SET_GOTO_uses_every_last_cfg_item_rhs1_symbol)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(rule Fact6_12__2)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(force)
  apply(rule conjI)
   prefer 2
   apply(force)
  apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G)], cfg_item_rhs2 = [teB Do], cfg_item_look_ahead = []\<rparr> \<in> valid_item_set G' k v")
   prefer 2
   apply(subgoal_tac "\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2 = [], cfg_item_look_ahead = []\<rparr>\<lparr>cfg_item_rhs1:=[teB Do, teA (cfg_initial G)], cfg_item_rhs2:=teB Do#(cfg_item_rhs2 \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2 = [], cfg_item_look_ahead = []\<rparr>)\<rparr> \<in> valid_item_set G' k v")
    apply(force)
   apply(rule F_LR_MACHINE_shift_back_in_pre_state)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "valid_item_set G' k v \<in> epda_states M")
   prefer 2
   apply(rule_tac
      t="epda_states M"
      and s="{valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}"
      in ssubst)
    apply(rule_tac
      G="G'"
      in LRM_contains_theEqClasses)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "v=[teB Do, teA (cfg_initial G)]")
   apply(force)
  apply(rule DollarInitialReadItem_OnlyIn_Specific_Valid)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma nonEmptyStatesViaDoS_primeDo: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q' \<in> set (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])
  \<Longrightarrow> q' \<noteq> {}"
  apply(subgoal_tac " q'=last(epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) []) \<or> q'=last(epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<or> q'=last(epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<or> q'=last(epda_initial M #F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) ")
   apply(erule disjE)
    apply(subgoal_tac "(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) []))) ={\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}")
     apply(force)
    apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_0)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(erule disjE)
    apply(subgoal_tac "(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])))-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} ={\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do], cfg_item_rhs2=[teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}")
     apply(force)
    apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_1)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(erule disjE)
    apply(subgoal_tac "(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])))-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} ={\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G)], cfg_item_rhs2=[teB Do], cfg_item_look_ahead=[]\<rparr>}")
     apply(force)
    apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_2)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]))) ={\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G), teB Do], cfg_item_rhs2=[], cfg_item_look_ahead=[]\<rparr>}")
    apply(force)
   apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_3)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>i<length SSw. SSw ! i = q'" for SSw)
   prefer 2
   apply(rule set_elem_nth)
   apply(blast)
  apply(erule exE)
  apply(rename_tac i)(*strict*)
  apply(erule conjE)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(rule_tac disjI1)
   apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) []=[]")
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac i)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(force)
  apply(rename_tac i nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac i nat)(*strict*)
   apply(rule_tac disjI2)
   apply(rule_tac disjI1)
   apply(rule_tac
      t="q'"
      and s="(epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) ! i"
      in ssubst)
    apply(rename_tac i nat)(*strict*)
    apply(force)
   apply(rename_tac i nat)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (take i ([teB Do, teA (cfg_initial G), teB Do]))"
      in ssubst)
    apply(rename_tac i nat)(*strict*)
    apply(force)
   apply(rename_tac i nat)(*strict*)
   apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE_prime)
        apply(rename_tac i nat)(*strict*)
        apply(force)
       apply(rename_tac i nat)(*strict*)
       apply(force)
      apply(rename_tac i nat)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac i nat)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac i nat)(*strict*)
       apply(force)
      apply(rename_tac i nat)(*strict*)
      apply(force)
     apply(rename_tac i nat)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac i nat)(*strict*)
    apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
   apply(rename_tac i nat)(*strict*)
   apply(force)
  apply(rename_tac i nat nata)(*strict*)
  apply(case_tac nata)
   apply(rename_tac i nat nata)(*strict*)
   apply(rule_tac disjI2)
   apply(rule disjI2)
   apply(rule_tac disjI1)
   apply(rule_tac
      t="q'"
      and s="(epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) ! i"
      in ssubst)
    apply(rename_tac i nat nata)(*strict*)
    apply(force)
   apply(rename_tac i nat nata)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (take i ([teB Do, teA (cfg_initial G), teB Do]))"
      in ssubst)
    apply(rename_tac i nat nata)(*strict*)
    apply(force)
   apply(rename_tac i nat nata)(*strict*)
   apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE_prime)
        apply(rename_tac i nat nata)(*strict*)
        apply(force)
       apply(rename_tac i nat nata)(*strict*)
       apply(force)
      apply(rename_tac i nat nata)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac i nat nata)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac i nat nata)(*strict*)
       apply(force)
      apply(rename_tac i nat nata)(*strict*)
      apply(force)
     apply(rename_tac i nat nata)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac i nat nata)(*strict*)
    apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
   apply(rename_tac i nat nata)(*strict*)
   apply(force)
  apply(rename_tac i nat nata natb)(*strict*)
  apply(case_tac natb)
   apply(rename_tac i nat nata natb)(*strict*)
   apply(rule_tac disjI2)
   apply(rule disjI2)
   apply(rule disjI2)
   apply(rule_tac
      t="[teB Do, teA (cfg_initial G), teB Do]"
      and s="(take i ([teB Do, teA (cfg_initial G), teB Do]))"
      in ssubst)
    apply(rename_tac i nat nata natb)(*strict*)
    apply(force)
   apply(rename_tac i nat nata natb)(*strict*)
   apply(rule_tac
      t="q'"
      and s="(epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]) ! i"
      in ssubst)
    apply(rename_tac i nat nata natb)(*strict*)
    apply(force)
   apply(rename_tac i nat nata natb)(*strict*)
   apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE_prime)
        apply(rename_tac i nat nata natb)(*strict*)
        apply(force)
       apply(rename_tac i nat nata natb)(*strict*)
       apply(force)
      apply(rename_tac i nat nata natb)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac i nat nata natb)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac i nat nata natb)(*strict*)
       apply(force)
      apply(rename_tac i nat nata natb)(*strict*)
      apply(force)
     apply(rename_tac i nat nata natb)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac i nat nata natb)(*strict*)
    apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
   apply(rename_tac i nat nata natb)(*strict*)
   apply(force)
  apply(rename_tac i nat nata natb natc)(*strict*)
  apply(subgoal_tac "length [teB Do, teA (cfg_initial G), teB Do] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
   apply(rename_tac i nat nata natb natc)(*strict*)
   apply(force)
  apply(rename_tac i nat nata natb natc)(*strict*)
  apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
       apply(rename_tac i nat nata natb natc)(*strict*)
       apply(force)
      apply(rename_tac i nat nata natb natc)(*strict*)
      apply(force)
     apply(rename_tac i nat nata natb natc)(*strict*)
     apply(rule F_LR_MACHINE_all_Connected)
        apply(rename_tac i nat nata natb natc)(*strict*)
        prefer 3
        apply(force)
       apply(force)
      apply(rename_tac i nat nata natb natc)(*strict*)
      apply(force)
     apply(rename_tac i nat nata natb natc)(*strict*)
     apply(force)
    apply(rename_tac i nat nata natb natc)(*strict*)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(rename_tac i nat nata natb natc)(*strict*)
   apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def valid_cfg_def)
  apply(rename_tac i nat nata natb natc)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_edges_have_valid_item_set: "
  M = F_LR_MACHINE G' F k
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> e \<in> epda_delta M
  \<Longrightarrow> \<exists>w a. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G') \<and> e = \<lparr>edge_src = valid_item_set G' k w, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE G' F k)], edge_push = [epda_box (F_LR_MACHINE G' F k)], edge_trg = valid_item_set G' k (w @ [a]) \<rparr>"
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G' F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})")
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK_prime)
    apply(force)
   apply(force)
  apply(erule_tac
      x="e"
      in ballE)
   apply(subgoal_tac "\<exists>w. set w \<subseteq> (two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')) \<and> (edge_src e)=valid_item_set G' k w")
    prefer 2
    apply(rule F_LR_MACHINE__fp_one_unfold_03)
      apply(rule F_LR_MACHINE__fp_one_TERM_ARGS_TEST_initial)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(rename_tac y)(*strict*)
     apply(rule_tac
      x="[]"
      in exI)
     apply(clarsimp)
     apply(rule sym)
     apply(rule Lemma6__23_1)
      apply(force)
     apply(force)
    apply(force)
   apply(erule exE)+
   apply(rename_tac w)(*strict*)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac w y)(*strict*)
   apply(erule conjE)+
   apply(rule_tac
      x="w"
      in exI)
   apply(rule_tac
      x="y"
      in exI)
   apply(rule context_conjI)
    apply(rename_tac w y)(*strict*)
    apply(force)
   apply(rename_tac w y)(*strict*)
   apply(subgoal_tac "valid_item_set G' k (w @ [y]) = F_VALID_ITEM_SET_GOTO G' F k y (valid_item_set G' k w)")
    apply(rename_tac w y)(*strict*)
    apply(clarsimp)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac w y)(*strict*)
   prefer 2
   apply(simp add: F_LR_MACHINE_def)
  apply(rename_tac w y)(*strict*)
  apply(rule Lemma6__26)
     apply(rename_tac w y)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac w y)(*strict*)
   apply(subgoal_tac "set (w@[y]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
    apply(rename_tac w y)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(force)
   apply(rename_tac w y)(*strict*)
   apply(rule two_elements_construct_domain_append)
    apply(rename_tac w y)(*strict*)
    apply(force)
   apply(rename_tac w y)(*strict*)
   apply(force)
  apply(rename_tac w y)(*strict*)
  apply(subgoal_tac "set (w@[y]) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   apply(rename_tac w y)(*strict*)
   apply(rule two_elements_construct_domain_setB)
   apply(force)
  apply(rename_tac w y)(*strict*)
  apply(rule two_elements_construct_domain_append)
   apply(rename_tac w y)(*strict*)
   apply(force)
  apply(rename_tac w y)(*strict*)
  apply(force)
  done

lemma uniqueEntryEdgeForReadingDollarInitialDollar: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q' \<in> set (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])
  \<Longrightarrow> e1 \<in> epda_delta M
  \<Longrightarrow> e2 \<in> epda_delta M
  \<Longrightarrow> edge_trg e2 = edge_trg e1
  \<Longrightarrow> edge_trg e1 = q'
  \<Longrightarrow> e1 = e2"
  apply(subgoal_tac "q'\<noteq>{}")
   prefer 2
   apply(rule nonEmptyStatesViaDoS_primeDo)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "edge_event e1=edge_event e2")
   prefer 2
   apply(rule_tac
      G="G'"
      and p="q'"
      in Theorem6__27_b)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G' F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})")
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK_prime)
    apply(force)
   apply(force)
  apply(erule_tac
      x="e1"
      in ballE)
   prefer 2
   apply(simp add: F_LR_MACHINE_def)
  apply(subgoal_tac "\<forall>x \<in> snd (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k}). edge_src x \<in> fst (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k}) \<and> (\<exists>y. (edge_event x)=Some y \<and> y \<in> (two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')) \<and> (edge_trg x = F_VALID_ITEM_SET_GOTO G' F k y (edge_src x))) \<and> (edge_pop x) = [0] \<and> (edge_push x) = [0] \<and> edge_trg x \<in> fst (F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})")
   prefer 2
   apply(rule F_LR_MACHINE_all_edgesOK_prime)
    apply(force)
   apply(force)
  apply(erule_tac
      x="e2"
      in ballE)
   prefer 2
   apply(simp add: F_LR_MACHINE_def)
  apply(subgoal_tac "edge_src e1 = edge_src e2")
   apply(case_tac e1)
   apply(rename_tac edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(case_tac e2)
   apply(rename_tac edge_srca edge_eventa edge_popa edge_pusha edge_trga edge_srcaa edge_eventaa edge_popaa edge_pushaa edge_trgaa)(*strict*)
   apply(clarsimp)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac y ya)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "\<exists>w a. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G') \<and> e1=\<lparr>edge_src = valid_item_set G' k w, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE G' F k)], edge_push = [epda_box (F_LR_MACHINE G' F k)], edge_trg = valid_item_set G' k (w @ [a])\<rparr>")
   apply(rename_tac y ya)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_edges_have_valid_item_set)
      apply(rename_tac y ya)(*strict*)
      apply(force)
     apply(rename_tac y ya)(*strict*)
     apply(force)
    apply(rename_tac y ya)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac y ya)(*strict*)
  apply(subgoal_tac "\<exists>w a. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G') \<and> e2=\<lparr>edge_src = valid_item_set G' k w, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE G' F k)], edge_push = [epda_box (F_LR_MACHINE G' F k)], edge_trg = valid_item_set G' k (w @ [a])\<rparr>")
   apply(rename_tac y ya)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_edges_have_valid_item_set)
      apply(rename_tac y ya)(*strict*)
      apply(force)
     apply(rename_tac y ya)(*strict*)
     apply(force)
    apply(rename_tac y ya)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac y ya)(*strict*)
  apply(erule exE)+
  apply(rename_tac y ya w wa a aa)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "y=ya")
   apply(rename_tac y ya w wa a aa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac y ya w wa a aa)(*strict*)
  apply(subgoal_tac "valid_item_set G' k w = valid_item_set G' k wa")
   apply(rename_tac y ya w wa a aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac y ya w wa a aa)(*strict*)
  apply(subgoal_tac "\<exists>qa. qa= edge_src e2")
   apply(rename_tac y ya w wa a aa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac y ya w wa a aa)(*strict*)
  apply(erule exE)+
  apply(rename_tac y ya w wa a aa qa)(*strict*)
  apply(rename_tac X Xa w wa a aa qa)
  apply(rename_tac X Xa w wa a aa qa)(*strict*)
  apply(subgoal_tac " F_VALID_ITEM_SET_GOTO G' F k Xa qa = valid_item_set G' k [] \<or> F_VALID_ITEM_SET_GOTO G' F k Xa qa = valid_item_set G' k [teB Do] \<or> F_VALID_ITEM_SET_GOTO G' F k Xa qa = valid_item_set G' k [teB Do, teA (cfg_initial G)] \<or> F_VALID_ITEM_SET_GOTO G' F k Xa qa = valid_item_set G' k [teB Do, teA (cfg_initial G), teB Do]")
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   prefer 2
   apply(case_tac "F_VALID_ITEM_SET_GOTO G' F k Xa qa = epda_initial M")
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(rule disjI1)
    apply(rule_tac
      t="valid_item_set G' k []"
      and s="(if []=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) []))"
      in ssubst)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(rule F_LR_MACHINE_all_SOUND)
           apply(rename_tac X Xa w wa a aa qa)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(subgoal_tac "\<exists>i. i<(length((F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]))) \<and> F_VALID_ITEM_SET_GOTO G' F k Xa qa = (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])!i")
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    prefer 2
    apply(rule_tac
      b="epda_initial M"
      in hasPositionInSet)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(erule exE)
   apply(rename_tac X Xa w wa a aa qa i)(*strict*)
   apply(erule conjE)
   apply(subgoal_tac "i<3")
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    prefer 2
    apply(rule_tac
      t="3"
      and s="length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])"
      in ssubst)
     apply(rename_tac X Xa w wa a aa qa i)(*strict*)
     apply(rule_tac
      t="length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])"
      and s="length ([teB Do, teA (cfg_initial G), teB Do])"
      in ssubst)
      apply(rename_tac X Xa w wa a aa qa i)(*strict*)
      apply(rule sym)
      apply(rule_tac
      q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
           apply(rename_tac X Xa w wa a aa qa i)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa i)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa i)(*strict*)
         apply(rule F_LR_MACHINE_all_Connected)
            apply(rename_tac X Xa w wa a aa qa i)(*strict*)
            prefer 3
            apply(force)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa i)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa i)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa i)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac X Xa w wa a aa qa i)(*strict*)
       apply(rule set_take_head2)
        apply(rename_tac X Xa w wa a aa qa i)(*strict*)
        apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
       apply(rename_tac X Xa w wa a aa qa i)(*strict*)
       apply(rule set_take_head2)
        apply(rename_tac X Xa w wa a aa qa i)(*strict*)
        apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
       apply(rename_tac X Xa w wa a aa qa i)(*strict*)
       apply(rule set_take_head2)
        apply(rename_tac X Xa w wa a aa qa i)(*strict*)
        apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
       apply(rename_tac X Xa w wa a aa qa i)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa i)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa i)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa i)(*strict*)
   apply(thin_tac "i < length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
   apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do] ! i = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (take (Suc i) [teB Do, teA (cfg_initial G), teB Do]))")
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    prefer 2
    apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE)
         apply(rename_tac X Xa w wa a aa qa i)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa i)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa i)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac X Xa w wa a aa qa i)(*strict*)
          prefer 3
          apply(force)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa i)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa i)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa i)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac X Xa w wa a aa qa i)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    apply(rule set_take_head2)
     apply(rename_tac X Xa w wa a aa qa i)(*strict*)
     apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    apply(rule set_take_head2)
     apply(rename_tac X Xa w wa a aa qa i)(*strict*)
     apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    apply(rule set_take_head2)
     apply(rename_tac X Xa w wa a aa qa i)(*strict*)
     apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa i)(*strict*)
   apply(subgoal_tac "F_VALID_ITEM_SET_GOTO G' F k Xa qa = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (take (Suc i) [teB Do, teA (cfg_initial G), teB Do]))")
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac X Xa w wa a aa qa i)(*strict*)
   apply(thin_tac "F_VALID_ITEM_SET_GOTO G' F k Xa qa = F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do] ! i")
   apply(case_tac i)
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    apply(rule disjI2, rule disjI1)
    apply(rule_tac
      t="valid_item_set G' k [teB Do]"
      and s="(if [teB Do]=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]))"
      in ssubst)
     apply(rename_tac X Xa w wa a aa qa i)(*strict*)
     apply(rule F_LR_MACHINE_all_SOUND)
           apply(rename_tac X Xa w wa a aa qa i)(*strict*)
           apply(force)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa i)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa i)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa i)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa i)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa i)(*strict*)
     apply(simp add: F_CFG_AUGMENT_def)
    apply(rename_tac X Xa w wa a aa qa i)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
   apply(case_tac nat)
    apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
    apply(rule disjI2, rule disjI2, rule disjI1)
    apply(rule_tac
      t="valid_item_set G' k [teB Do, teA (cfg_initial G)]"
      and s="(if [teB Do, teA (cfg_initial G)]=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]))"
      in ssubst)
     apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
     apply(rule F_LR_MACHINE_all_SOUND)
           apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
           apply(force)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
      apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
     apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
     apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
    apply(rename_tac X Xa w wa a aa qa i nat)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
   apply(rule disjI2, rule disjI2, rule disjI2)
   apply(rule_tac
      t="valid_item_set G' k [teB Do, teA (cfg_initial G), teB Do]"
      and s="(if [teB Do, teA (cfg_initial G), teB Do]=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]))"
      in ssubst)
    apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND)
          apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
          apply(force)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
     apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
    apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def valid_cfg_def)
   apply(rename_tac X Xa w wa a aa qa i nat nata)(*strict*)
   apply(force)
  apply(rename_tac X Xa w wa a aa qa)(*strict*)
  apply(thin_tac "q' \<in> set (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do])")
  apply(rename_tac X Xa w wa a aa qa)(*strict*)
  apply(erule disjE)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(rule_tac
      q="qa"
      in F_VALID_ITEM_SET_GOTO_to_1)
             apply(rename_tac X Xa w wa a aa qa)(*strict*)
             apply(force)
            apply(rename_tac X Xa w wa a aa qa)(*strict*)
            apply(force)
           apply(rename_tac X Xa w wa a aa qa)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(rule_tac
      t="epda_states (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)"
      and s="{valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}"
      in ssubst)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(simp only: LRM_contains_theEqClasses)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(force)
  apply(rename_tac X Xa w wa a aa qa)(*strict*)
  apply(erule disjE)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(subgoal_tac "valid_item_set G' k wa=valid_item_set G' k [] \<and> X=teB Do")
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO_to_2)
              apply(rename_tac X Xa w wa a aa qa)(*strict*)
              apply(force)
             apply(force)
            apply(rename_tac X Xa w wa a aa qa)(*strict*)
            apply(force)
           apply(rename_tac X Xa w wa a aa qa)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(subgoal_tac "valid_item_set G' k w=valid_item_set G' k [] \<and> X=teB Do")
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO_to_2)
              apply(rename_tac X Xa w wa a aa qa)(*strict*)
              apply(force)
             apply(force)
            apply(rename_tac X Xa w wa a aa qa)(*strict*)
            apply(force)
           apply(rename_tac X Xa w wa a aa qa)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(force)
  apply(rename_tac X Xa w wa a aa qa)(*strict*)
  apply(erule disjE)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(subgoal_tac "valid_item_set G' k wa=valid_item_set G' k [teB Do] \<and> X=teA (cfg_initial G)")
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO_to_3)
              apply(rename_tac X Xa w wa a aa qa)(*strict*)
              apply(force)
             apply(force)
            apply(rename_tac X Xa w wa a aa qa)(*strict*)
            apply(force)
           apply(rename_tac X Xa w wa a aa qa)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(subgoal_tac "valid_item_set G' k w=valid_item_set G' k [teB Do] \<and> X=teA (cfg_initial G)")
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    prefer 2
    apply(rule F_VALID_ITEM_SET_GOTO_to_3)
              apply(rename_tac X Xa w wa a aa qa)(*strict*)
              apply(force)
             apply(force)
            apply(rename_tac X Xa w wa a aa qa)(*strict*)
            apply(force)
           apply(rename_tac X Xa w wa a aa qa)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(force)
  apply(rename_tac X Xa w wa a aa qa)(*strict*)
  apply(subgoal_tac "valid_item_set G' k wa=valid_item_set G' k [teB Do, teA(cfg_initial G)] \<and> X=teB Do")
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO_to_4)
             apply(rename_tac X Xa w wa a aa qa)(*strict*)
             apply(force)
            apply(force)
           apply(rename_tac X Xa w wa a aa qa)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(force)
  apply(rename_tac X Xa w wa a aa qa)(*strict*)
  apply(subgoal_tac "valid_item_set G' k w=valid_item_set G' k [teB Do, teA(cfg_initial G)] \<and> X=teB Do")
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO_to_4)
             apply(rename_tac X Xa w wa a aa qa)(*strict*)
             apply(force)
            apply(force)
           apply(rename_tac X Xa w wa a aa qa)(*strict*)
           apply(force)
          apply(rename_tac X Xa w wa a aa qa)(*strict*)
          apply(force)
         apply(rename_tac X Xa w wa a aa qa)(*strict*)
         apply(force)
        apply(rename_tac X Xa w wa a aa qa)(*strict*)
        apply(force)
       apply(rename_tac X Xa w wa a aa qa)(*strict*)
       apply(force)
      apply(rename_tac X Xa w wa a aa qa)(*strict*)
      apply(force)
     apply(rename_tac X Xa w wa a aa qa)(*strict*)
     apply(force)
    apply(rename_tac X Xa w wa a aa qa)(*strict*)
    apply(force)
   apply(rename_tac X Xa w wa a aa qa)(*strict*)
   apply(force)
  apply(rename_tac X Xa w wa a aa qa)(*strict*)
  apply(force)
  done

lemma ReadInitialIsEmpty: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q = F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))
  \<Longrightarrow> q = {}"
  apply(rule_tac
      t="q"
      and s="F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))"
      and s="last [F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))]"
      in ssubst)
   apply(force)
  apply(rule_tac
      t="[F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))]"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teA (cfg_initial G)]"
      in ssubst)
   apply(rule sym)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(force)
      apply(force)
     apply(rule F_LR_MACHINE_all_Connected)
        prefer 3
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teA (cfg_initial G)])"
      and s="valid_item_set G' k [teA (cfg_initial G)]"
      in subst)
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_all_SOUND_NotNil)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(rule two_elements_construct_domain_setA)
     apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
    apply(rule_tac
      A="cfg_nonterminals G'"
      in two_elements_construct_domain_setB)
    apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
   apply(force)
  apply(case_tac "\<exists>I. I \<in> valid_item_set G' k [teA (cfg_initial G)]")
   prefer 2
   apply(force)
  apply(erule exE)+
  apply(rename_tac I)(*strict*)
  apply(subgoal_tac "\<exists>n. I \<in> valid_item_set_n G' k n [teA (cfg_initial G)]")
   apply(rename_tac I)(*strict*)
   prefer 2
   apply(simp add: valid_item_set_def)
  apply(rename_tac I)(*strict*)
  apply(erule exE)+
  apply(rename_tac I n)(*strict*)
  apply(subgoal_tac "\<forall>A \<alpha> \<beta> y. I = \<lparr>cfg_item_lhs = A, cfg_item_rhs1 = \<alpha>, cfg_item_rhs2 = \<beta>, cfg_item_look_ahead = y\<rparr> \<longrightarrow> (\<exists>d \<delta> e1 e2 z. cfgRM.derivation G' d \<and> d 0 = Some (pair None \<lparr>cfg_conf=[teA (cfg_initial G')]\<rparr>) \<and> d n = Some (pair e1 \<lparr>cfg_conf=\<delta>@[teA A]@z\<rparr>) \<and> d (Suc n) = Some (pair e2 \<lparr>cfg_conf=\<delta>@\<alpha>@\<beta>@z\<rparr>) \<and> take k z=liftB y \<and> [teA (cfg_initial G)]=\<delta>@\<alpha> \<and> maximum_of_domain d (Suc n) \<and> setA z = {})")
   apply(rename_tac I n)(*strict*)
   prefer 2
   apply(simp add: valid_item_set_n_def)
   apply(clarsimp)
   apply(rename_tac n Aa \<alpha>' \<beta>' ya d \<delta> e1 e2 z)(*strict*)
   apply(rule_tac
      x="d"
      in exI)
   apply(clarsimp)
  apply(rename_tac I n)(*strict*)
  apply(thin_tac "I \<in> valid_item_set G' k [teA (cfg_initial G)]")
  apply(thin_tac "I \<in> valid_item_set_n G' k n [teA (cfg_initial G)]")
  apply(subgoal_tac "False")
   apply(rename_tac I n)(*strict*)
   apply(clarsimp)
  apply(rename_tac I n)(*strict*)
  apply(erule_tac
      x="cfg_item_lhs I"
      in allE)
  apply(erule_tac
      x="cfg_item_rhs1 I"
      in allE)
  apply(erule_tac
      x="cfg_item_rhs2 I"
      in allE)
  apply(erule_tac
      x="cfg_item_look_ahead I"
      in allE)
  apply(erule impE)
   apply(rename_tac I n)(*strict*)
   apply(force)
  apply(rename_tac I n)(*strict*)
  apply(erule exE)+
  apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
   apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
   apply(blast)
  apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
  apply(subgoal_tac "\<exists>e w. d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w\<rparr>)")
   apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and m="Suc 0"
      and n="n"
      in terminal_at_beginning_are_never_modified)
       apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac I n d \<delta> e1 e2 z)(*strict*)
  apply(erule exE)+
  apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
  apply(subgoal_tac "\<exists>e w. d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w @ [teB Do]\<rparr>) \<and> (set w) \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) ")
   apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc 0"
      and n="n"
      in cfgRM.property_preseved_under_steps_is_invariant2)
       apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
       apply(force)
      apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
      apply(rule_tac
      x="Some\<lparr>prod_lhs = cfg_initial G', prod_rhs = [teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in exI)
      apply(rule_tac
      x="[teA (cfg_initial G)]"
      in exI)
      apply(rule conjI)
       apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
       apply(clarsimp)
      apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
      apply(thin_tac "[teA (cfg_initial G)] = \<delta> @ cfg_item_rhs1 I")
      apply(simp add: two_elements_construct_domain_def valid_cfg_def)
     apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
     apply(force)
    apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
    apply(force)
   apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
   apply(rule allI)
   apply(rename_tac I n d \<delta> e1 e2 z e w i)(*strict*)
   apply(rule impI)
   apply(erule conjE)+
   apply(erule exE)+
   apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa)(*strict*)
   apply(erule conjE)+
   apply(subgoal_tac "\<exists>e c. d (Suc i) = Some (pair (Some e) c)")
    apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa)(*strict*)
    prefer 2
    apply(rule cfgRM.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa)(*strict*)
      apply(blast)
     apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa)(*strict*)
     apply(blast)
    apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa)(*strict*)
    apply(arith)
   apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa)(*strict*)
   apply(erule exE)+
   apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa eb c)(*strict*)
   apply(subgoal_tac "cfgRM_step_relation G' \<lparr>cfg_conf = teB Do # wa @ [teB Do]\<rparr> eb c")
    apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa eb c)(*strict*)
    prefer 2
    apply(rule cfgRM.position_change_due_to_step_relation)
      apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa eb c)(*strict*)
      apply(blast)
     apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa eb c)(*strict*)
     apply(blast)
    apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa eb c)(*strict*)
    apply(blast)
   apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa eb c)(*strict*)
   apply(case_tac c)
   apply(rename_tac I n d \<delta> e1 e2 z e w i ea wa eb c cfg_conf)(*strict*)
   apply(simp add: cfgRM_step_relation_def)
   apply(clarsimp)
   apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb l r)(*strict*)
   apply(case_tac l)
    apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb l r)(*strict*)
    apply(clarsimp)
   apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb l r a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb r list)(*strict*)
   apply(case_tac "r=[]")
    apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb r list)(*strict*)
    apply(clarsimp)
   apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb r list)(*strict*)
   apply(subgoal_tac "\<exists>r' a. r=r'@[a]")
    apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb r list)(*strict*)
    apply(clarsimp)
    apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
    apply(subgoal_tac "eb \<in> cfg_productions G")
     apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="eb"
      and P="\<lambda>eb. prod_lhs eb \<in> cfg_nonterminals G \<and> setA (prod_rhs eb) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs eb) \<subseteq> cfg_events G"
      in ballE)
      apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
      apply(clarsimp)
      apply(rule_tac
      A="set(prod_rhs eb)"
      in set_mp)
       apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
       apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
        apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
        apply(force)
       apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
       apply(force)
      apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
      apply(clarsimp)
     apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
     apply(force)
    apply(rename_tac I n d \<delta> e1 e2 z w i ea eb list r' x)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
    apply(clarsimp)
    apply(rename_tac I n d \<delta> e1 e2 z w i ea list r' x)(*strict*)
    apply(subgoal_tac "teA (F_FRESH (cfg_nonterminals G)) \<notin> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
     apply(rename_tac I n d \<delta> e1 e2 z w i ea list r' x)(*strict*)
     apply(force)
    apply(rename_tac I n d \<delta> e1 e2 z w i ea list r' x)(*strict*)
    apply(thin_tac "teA (F_FRESH (cfg_nonterminals G)) \<in> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
    apply(simp add: two_elements_construct_domain_def)
    apply(rule conjI)
     apply(rename_tac I n d \<delta> e1 e2 z w i ea list r' x)(*strict*)
     prefer 2
     apply(clarsimp)
    apply(rename_tac I n d \<delta> e1 e2 z w i ea list r' x)(*strict*)
    apply(rule teA_notInMap)
    apply(rule F_FRESH_is_fresh)
    apply(simp add: valid_cfg_def)
   apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb r list)(*strict*)
   apply(rule_tac
      n="length r - 1"
      in NonEmptyListHasTailElem)
   apply(case_tac r)
    apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb r list)(*strict*)
    apply(force)
   apply(rename_tac I n d \<delta> e1 e2 z w i ea wa eb r list a lista)(*strict*)
   apply(clarsimp)
  apply(rename_tac I n d \<delta> e1 e2 z e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac I n d \<delta> e1 e2 z wa)(*strict*)
  apply(subgoal_tac "[teA (cfg_initial G)] @ cfg_item_rhs2 I @ z = teB (F_FRESH (cfg_events G)) # wa @ [teB (F_FRESH (cfg_events G))]")
   apply(rename_tac I n d \<delta> e1 e2 z wa)(*strict*)
   prefer 2
   apply(rule_tac
      t="[teA (cfg_initial G)]"
      and s="\<delta> @ cfg_item_rhs1 I"
      in ssubst)
    apply(rename_tac I n d \<delta> e1 e2 z wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac I n d \<delta> e1 e2 z wa)(*strict*)
   apply(clarsimp)
  apply(rename_tac I n d \<delta> e1 e2 z wa)(*strict*)
  apply(thin_tac "[teA (cfg_initial G)] = \<delta> @ cfg_item_rhs1 I")
  apply(force)
  done

lemma F_LR_MACHINE_states_are_sets_of_items: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> q \<subseteq> (Collect (valid_item G' k))"
  apply(subgoal_tac "\<exists>w. q=valid_item_set G' k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G' k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
    apply(force)
   apply(rule LRM_contains_theEqClasses)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)
  apply(rename_tac w)(*strict*)
  apply(rule_tac
      t="q"
      and s="valid_item_set G' k w"
      in ssubst)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(rule subsetI)
  apply(rename_tac w x)(*strict*)
  apply(clarsimp)
  apply(rule Fact6_12__2)
   apply(rename_tac w x)(*strict*)
   apply(force)
  apply(rename_tac w x)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_shifted_item_in_next_state: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> valid_item G' k I
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> cfg_item_rhs2 I = a # w
  \<Longrightarrow> J = I\<lparr>cfg_item_rhs1 := cfg_item_rhs1 I @ [a], cfg_item_rhs2 := w\<rparr>
  \<Longrightarrow> q' = F_DFA_GOTO M q a
  \<Longrightarrow> J \<in> q'"
  apply(subgoal_tac "q \<subseteq> (Collect (valid_item G' k))")
   prefer 2
   apply(rule F_LR_MACHINE_states_are_sets_of_items)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="q'"
      and s="F_VALID_ITEM_SET_GOTO G' F k a q"
      in subst)
   apply(rule_tac
      t="q'"
      and s="F_DFA_GOTO (F_LR_MACHINE G' F k) q a"
      in subst)
    apply(force)
   apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(rule_tac
      A="set (a#w)"
      in set_mp)
     apply(rule Item_rhs2_in_CFG)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G' F k a q"
      and s="F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis a q)"
      in ssubst)
   apply(simp add: F_VALID_ITEM_SET_GOTO_def)
  apply(rule_tac
      A="F_VALID_ITEM_SET_GOTO__basis a q"
      in set_mp)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_mono)
     apply(force)
    apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>I1 \<in> q. F_VALID_ITEM_SET_GOTO__passes a I1 J")
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(rule_tac
      x="I"
      in bexI)
   apply(simp add: F_VALID_ITEM_SET_GOTO__passes_def)
  apply(force)
  done

lemma F_LR_MACHINE_all_connected: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> \<exists>w. last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) w) = q \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
  apply(subgoal_tac "\<exists>w. q=valid_item_set G k w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)")
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G k w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)}")
    apply(force)
   apply(rule LRM_contains_theEqClasses)
     apply(force)
    apply(force)
   apply(force)
  apply(erule exE)+
  apply(rename_tac w)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
   apply(rename_tac w)(*strict*)
   prefer 2
   apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac w)(*strict*)
        apply(force)
       apply(rename_tac w)(*strict*)
       apply(force)
      apply(rename_tac w)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac w)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac w)(*strict*)
       apply(force)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac w)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac w)(*strict*)
   apply(force)
  apply(rename_tac w)(*strict*)
  apply(case_tac w)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="epda_initial M"
      in ssubst)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(rename_tac w)(*strict*)
   apply(rule_tac
      t="epda_initial M"
      and s="valid_item_set G k w"
      in subst)
    apply(rename_tac w)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND_Nil)
           apply(rename_tac w)(*strict*)
           apply(force)
          apply(rename_tac w)(*strict*)
          apply(force)
         apply(rename_tac w)(*strict*)
         apply(force)
        apply(rename_tac w)(*strict*)
        apply(force)
       apply(rename_tac w)(*strict*)
       apply(force)
      apply(rename_tac w)(*strict*)
      apply(force)
     apply(rename_tac w)(*strict*)
     apply(force)
    apply(rename_tac w)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
   apply(rename_tac w a list)(*strict*)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="valid_item_set G k w"
      in subst)
   apply(rename_tac w a list)(*strict*)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(rename_tac w a list)(*strict*)
          apply(force)+
     apply(rename_tac w a list)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(force)
    apply(rename_tac w a list)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rename_tac w a list)(*strict*)
   apply(force)
  apply(rename_tac w a list)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_shifted_item_in_next_states: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> n \<le> length (cfg_item_rhs2 I)
  \<Longrightarrow> J = I\<lparr>cfg_item_rhs1 := cfg_item_rhs1 I @ (take n (cfg_item_rhs2 I)), cfg_item_rhs2 := drop n (cfg_item_rhs2 I) \<rparr>
  \<Longrightarrow> q' = last (q # F_DFA_GOTO_SEQUENCE M q (take n (cfg_item_rhs2 I)))
  \<Longrightarrow> J \<in> q'"
  apply(case_tac n)
   apply(rule_tac
      t="J"
      and s="I"
      in ssubst)
    apply(force)
   apply(rule_tac
      t="q'"
      and s="q"
      in ssubst)
    apply(rule_tac
      t="q'"
      and s="last (q # F_DFA_GOTO_SEQUENCE M q (take 0 (cfg_item_rhs2 I)))"
      in ssubst)
     apply(force)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q (take 0 (cfg_item_rhs2 I))"
      and s="[]"
      in ssubst)
     apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M q [])")
      prefer 2
      apply(rule_tac
      w="[]"
      and q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
           apply(force)
          apply(force)
         apply(rule F_LR_MACHINE_all_Connected)
            prefer 3
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "q \<subseteq> (Collect (valid_item G' k))")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule F_LR_MACHINE_states_are_sets_of_items)
          apply(rename_tac nat)(*strict*)
          apply(force)
         apply(rename_tac nat)(*strict*)
         apply(force)
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "valid_item G' k I")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "length (take n (cfg_item_rhs2 I)) = length (F_DFA_GOTO_SEQUENCE M q (take n (cfg_item_rhs2 I)))")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      w="(take n (cfg_item_rhs2 I))"
      and q="q"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac nat)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(rule_tac
      B="set (cfg_item_rhs2 I)"
      in subset_trans)
     apply(rename_tac nat)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac nat)(*strict*)
    apply(rule_tac
      t="epda_events (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(rename_tac nat)(*strict*)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac nat)(*strict*)
    apply(rule Item_rhs2_in_CFG)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(subgoal_tac "\<exists>w. last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) w)=q \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_all_connected)
        apply(rename_tac nat)(*strict*)
        apply(force)
       apply(rename_tac nat)(*strict*)
       apply(force)
      apply(rename_tac nat)(*strict*)
      apply(force)
     apply(rename_tac nat)(*strict*)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(erule exE)+
  apply(rename_tac nat w)(*strict*)
  apply(subgoal_tac "length w = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)")
   apply(rename_tac nat w)(*strict*)
   prefer 2
   apply(rule_tac
      w="w"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac nat w)(*strict*)
        apply(force)
       apply(rename_tac nat w)(*strict*)
       apply(force)
      apply(rename_tac nat w)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac nat w)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac nat w)(*strict*)
       apply(force)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac nat w)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac nat w)(*strict*)
   apply(force)
  apply(rename_tac nat w)(*strict*)
  apply(subgoal_tac "valid_item_set G' k (w@take n (cfg_item_rhs2 I))=q'")
   apply(rename_tac nat w)(*strict*)
   prefer 2
   apply(rule_tac
      t="q'"
      and s="last (q # F_DFA_GOTO_SEQUENCE M q (take n (cfg_item_rhs2 I)))"
      in subst)
    apply(rename_tac nat w)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(rule_tac
      t="last (q # F_DFA_GOTO_SEQUENCE M q (take n (cfg_item_rhs2 I)))"
      and s="last (F_DFA_GOTO_SEQUENCE M q (take n (cfg_item_rhs2 I)))"
      in ssubst)
    apply(rename_tac nat w)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(rule_tac
      t="q"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rename_tac nat w)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)) (take n (cfg_item_rhs2 I)))"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@(take n (cfg_item_rhs2 I))))"
      in ssubst)
    apply(rename_tac nat w)(*strict*)
    apply(case_tac w)
     apply(rename_tac nat w)(*strict*)
     apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="epda_initial M"
      in ssubst)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w a list)(*strict*)
    apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
     apply(rename_tac nat w a list)(*strict*)
     apply(force)
    apply(rename_tac nat w a list)(*strict*)
    apply(rule F_DFA_GOTO_SEQUENCE_concat)
           apply(rename_tac nat w a list)(*strict*)
           apply(force)
          apply(rename_tac nat w a list)(*strict*)
          apply(force)
         apply(rename_tac nat w a list)(*strict*)
         apply(rule F_LR_MACHINE_all_Connected)
            apply(rename_tac nat w a list)(*strict*)
            prefer 3
            apply(force)
           apply(force)
          apply(rename_tac nat w a list)(*strict*)
          apply(force)
         apply(rename_tac nat w a list)(*strict*)
         apply(force)
        apply(rename_tac nat w a list)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac nat w a list)(*strict*)
       apply(simp add: F_LR_MACHINE_def)
      apply(rename_tac nat w a list)(*strict*)
      apply(rule_tac
      B="set (cfg_item_rhs2 I)"
      in subset_trans)
       apply(rename_tac nat w a list)(*strict*)
       apply(rule set_take_subset)
      apply(rename_tac nat w a list)(*strict*)
      apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
       apply(rename_tac nat w a list)(*strict*)
       apply(simp add: F_LR_MACHINE_def)
      apply(rename_tac nat w a list)(*strict*)
      apply(rule Item_rhs2_in_CFG)
        apply(rename_tac nat w a list)(*strict*)
        apply(force)
       apply(rename_tac nat w a list)(*strict*)
       apply(force)
      apply(rename_tac nat w a list)(*strict*)
      apply(force)
     apply(rename_tac nat w a list)(*strict*)
     apply(force)
    apply(rename_tac nat w a list)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(rename_tac nat w)(*strict*)
          apply(force)
         apply(rename_tac nat w)(*strict*)
         apply(force)
        apply(rename_tac nat w)(*strict*)
        apply(force)
       apply(rename_tac nat w)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(rule set_concat_subset)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(rule_tac
      B="set (cfg_item_rhs2 I)"
      in subset_trans)
      apply(rename_tac nat w)(*strict*)
      apply(rule set_take_subset)
     apply(rename_tac nat w)(*strict*)
     apply(rule_tac
      t="two_elements_construct_domain (cfg_nonterminals G') (cfg_events (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))))"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(rule Item_rhs2_in_CFG)
       apply(rename_tac nat w)(*strict*)
       apply(force)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(rule set_concat_subset)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(rule_tac
      B="set (cfg_item_rhs2 I)"
      in subset_trans)
     apply(rename_tac nat w)(*strict*)
     apply(rule set_take_subset)
    apply(rename_tac nat w)(*strict*)
    apply(rule_tac
      t="two_elements_construct_domain (cfg_nonterminals (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G)))) (cfg_events G')"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(rule Item_rhs2_in_CFG)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(force)
  apply(rename_tac nat w)(*strict*)
  apply(subgoal_tac "valid_item_set G' k w=q")
   apply(rename_tac nat w)(*strict*)
   prefer 2
   apply(rule_tac
      t="q"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rename_tac nat w)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(case_tac w)
    apply(rename_tac nat w)(*strict*)
    apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="epda_initial M"
      in ssubst)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(rename_tac nat w)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND_Nil)
           apply(rename_tac nat w)(*strict*)
           apply(force)
          apply(rename_tac nat w)(*strict*)
          apply(force)
         apply(rename_tac nat w)(*strict*)
         apply(force)
        apply(rename_tac nat w)(*strict*)
        apply(force)
       apply(rename_tac nat w)(*strict*)
       apply(force)
      apply(rename_tac nat w)(*strict*)
      apply(force)
     apply(rename_tac nat w)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac nat w a list)(*strict*)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rename_tac nat w a list)(*strict*)
    apply(force)
   apply(rename_tac nat w a list)(*strict*)
   apply(rule F_LR_MACHINE_all_SOUND_NotNil)
          apply(rename_tac nat w a list)(*strict*)
          apply(force)
         apply(rename_tac nat w a list)(*strict*)
         apply(force)
        apply(rename_tac nat w a list)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac nat w a list)(*strict*)
      apply(force)
     apply(rename_tac nat w a list)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(force)
    apply(rename_tac nat w a list)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rename_tac nat w a list)(*strict*)
   apply(force)
  apply(rename_tac nat w)(*strict*)
  apply(subgoal_tac "\<exists>n. I \<in> valid_item_set_n G' k n w")
   apply(rename_tac nat w)(*strict*)
   prefer 2
   apply(simp only: valid_item_set_def)
   apply(clarsimp)
  apply(rename_tac nat w)(*strict*)
  apply(subgoal_tac "\<exists>n'. J \<in> valid_item_set_n G' k n' (w @ take n (cfg_item_rhs2 I))")
   apply(rename_tac nat w)(*strict*)
   apply(rule_tac
      t="q'"
      and s="valid_item_set G' k (w @ take n (cfg_item_rhs2 I))"
      in ssubst)
    apply(rename_tac nat w)(*strict*)
    apply(force)
   apply(rename_tac nat w)(*strict*)
   apply(erule exE)+
   apply(rename_tac nat w na n')(*strict*)
   apply(rule valid_item_set_n_subset_valid_item_set)
   apply(blast)
  apply(rename_tac nat w)(*strict*)
  apply(erule exE)+
  apply(rename_tac nat w na)(*strict*)
  apply(rule_tac
      x="na"
      in exI)
  apply(rule_tac
      t="J"
      and s="\<lparr>cfg_item_lhs=cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs1 I @ take n (cfg_item_rhs2 I), cfg_item_rhs2 = drop n (cfg_item_rhs2 I), cfg_item_look_ahead=cfg_item_look_ahead I\<rparr>"
      in ssubst)
   apply(rename_tac nat w na)(*strict*)
   apply(force)
  apply(rename_tac nat w na)(*strict*)
  apply(rule Lemma6__24_2)
  apply(rule_tac
      t="\<lparr>cfg_item_lhs = cfg_item_lhs I, cfg_item_rhs1 = cfg_item_rhs1 I, cfg_item_rhs2 = take n (cfg_item_rhs2 I) @ drop n (cfg_item_rhs2 I), cfg_item_look_ahead = cfg_item_look_ahead I\<rparr>"
      and s="I"
      in ssubst)
   apply(rename_tac nat w na)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat w na)(*strict*)
  apply(clarsimp)
  done

lemma F_LR_MACHINE_Do_in_cfg_events: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> teB Do \<in> epda_events M"
  apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
  done

lemma F_LR_MACHINE_DoS_in_cfg_events: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> set [teB Do, teA (cfg_initial G)] \<subseteq> epda_events M"
  apply(simp add: F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def valid_cfg_def)
  done

lemma F_LR_MACHINE_has_elem_shifts_back: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_dfa (F_LR_MACHINE G F k)
  \<Longrightarrow> some_step_from_every_configuration (F_LR_MACHINE G F k)
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> p \<in> epda_states M
  \<Longrightarrow> a \<in> epda_events M
  \<Longrightarrow> F_DFA_GOTO M p a \<noteq> {}
  \<Longrightarrow> p \<noteq> {}"
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO G F k a p \<noteq> {}")
   prefer 2
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G F k a p"
      and s="F_DFA_GOTO (F_LR_MACHINE G F k) p a"
      in ssubst)
    apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: F_LR_MACHINE_def)
    apply(force)
   apply(force)
  apply(case_tac "p={}")
   prefer 2
   apply(force)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO G F k a p = {}")
   apply(force)
  apply(simp add: F_VALID_ITEM_SET_GOTO_def)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__basis a {}={}")
   apply(clarsimp)
   prefer 2
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G F k {} = {}")
   apply(force)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G F k {}"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp G F k (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s G F k SSS))" for SSS
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  done

lemma F_LR_MACHINE_no_empty_states_when_reading_items: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> q_seq = F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> \<forall>i < length q_seq. q_seq ! i \<noteq> {}"
  apply(rule_tac
      t="length q_seq"
      and s="length (cfg_item_rhs2 I)"
      in ssubst)
   prefer 2
   apply(rule_tac
      t="q_seq"
      and s="F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)"
      in ssubst)
    apply(blast)
   apply(rule allI)
   apply(rename_tac i)(*strict*)
   apply(rule impI)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I) ! i"
      and s="(q#F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) ! (Suc i)"
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      t="(q#F_DFA_GOTO_SEQUENCE M q (cfg_item_rhs2 I)) ! (Suc i)"
      and s="last (q#F_DFA_GOTO_SEQUENCE SSM SSq (take (Suc SSi) SSw))" for SSM SSq SSi SSw
      in ssubst)
    apply(rename_tac i)(*strict*)
    apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE_prime)
         apply(rename_tac i)(*strict*)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac i)(*strict*)
          prefer 3
          apply(force)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(rule_tac
      G="G'"
      in F_LR_MACHINE_item_in_state_rhs2_in_cfg_events)
         apply(rename_tac i)(*strict*)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "I\<lparr>cfg_item_rhs1:=cfg_item_rhs1 I @ (take (Suc i) (cfg_item_rhs2 I)), cfg_item_rhs2:=drop (Suc i) (cfg_item_rhs2 I)\<rparr> \<in> last (q # F_DFA_GOTO_SEQUENCE M q (take (Suc i) (cfg_item_rhs2 I)))")
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(rule_tac
      n="Suc i"
      in F_LR_MACHINE_shifted_item_in_next_states)
                apply(rename_tac i)(*strict*)
                apply(force)
               apply(rename_tac i)(*strict*)
               apply(force)
              apply(rename_tac i)(*strict*)
              apply(force)
             apply(rename_tac i)(*strict*)
             apply(force)
            apply(rename_tac i)(*strict*)
            apply(force)
           apply(rename_tac i)(*strict*)
           apply(force)
          apply(rename_tac i)(*strict*)
          apply(force)
         apply(rename_tac i)(*strict*)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(force)
  apply(rule sym)
  apply(rule F_DFA_GOTO_SEQUENCESound_main1)
       apply(force)
      apply(force)
     apply(rule F_LR_MACHINE_all_Connected)
        prefer 3
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rule_tac
      G="G'"
      in F_LR_MACHINE_item_in_state_rhs2_in_cfg_events)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_nonempty_shifts_back_mult_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> (F_DFA_GOTO_SEQUENCE M q w) ! i = {}
  \<Longrightarrow> i \<le> j
  \<Longrightarrow> j < length w
  \<Longrightarrow> (F_DFA_GOTO_SEQUENCE M q w) ! j = {}"
  apply(induct j arbitrary: i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
  apply(rename_tac j i)(*strict*)
  apply(case_tac "i=Suc j")
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule_tac
      x="i"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO M ((q # (F_DFA_GOTO_SEQUENCE M q w)) ! (Suc j)) (w!(Suc j)) = (F_DFA_GOTO_SEQUENCE M q w) ! (Suc j)")
   apply(rename_tac j i)(*strict*)
   prefer 2
   apply(subgoal_tac "\<forall>i<length SSw. F_DFA_GOTO SSM ((SSq # SSqseq) ! i) (SSw ! i) = SSqseq ! i" for SSw SSM SSq SSqseq)
    apply(rename_tac j i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCESound_main2)
         apply(rename_tac j i)(*strict*)
         apply(force)
        apply(rename_tac j i)(*strict*)
        apply(force)
       apply(rename_tac j i)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac j i)(*strict*)
          prefer 3
          apply(force)
         apply(force)
        apply(rename_tac j i)(*strict*)
        apply(force)
       apply(rename_tac j i)(*strict*)
       apply(force)
      apply(rename_tac j i)(*strict*)
      apply(force)
     apply(rename_tac j i)(*strict*)
     apply(force)
    apply(rename_tac j i)(*strict*)
    apply(force)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q w ! Suc j"
      and s="F_DFA_GOTO M ((q # F_DFA_GOTO_SEQUENCE M q w) ! Suc j) (w ! Suc j)"
      in ssubst)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO M ((q # F_DFA_GOTO_SEQUENCE M q w) ! Suc j) (w ! Suc j)"
      and s="F_VALID_ITEM_SET_GOTO G' F k (w!(Suc j)) ((q # F_DFA_GOTO_SEQUENCE M q w) ! Suc j)"
      in subst)
   apply(rename_tac j i)(*strict*)
   apply(rule_tac
      t="M"
      and s="F_LR_MACHINE G' F k"
      in ssubst)
    apply(rename_tac j i)(*strict*)
    apply(force)
   apply(rename_tac j i)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO_vs_F_DFA_GOTO_in_F_LR_MACHINE)
        apply(rename_tac j i)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac j i)(*strict*)
      apply(force)
     apply(rename_tac j i)(*strict*)
     apply(force)
    apply(rename_tac j i)(*strict*)
    apply(simp add: F_LR_MACHINE_def)
    apply(force)
   apply(rename_tac j i)(*strict*)
   apply(subgoal_tac "set (F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G' F k) q w) \<subseteq> epda_states SSM" for SSM)
    apply(rename_tac j i)(*strict*)
    prefer 2
    apply(rule F_DFA_GOTO_SEQUENCESound_main3)
         apply(rename_tac j i)(*strict*)
         apply(force)
        apply(rename_tac j i)(*strict*)
        apply(force)
       apply(rename_tac j i)(*strict*)
       apply(rule F_LR_MACHINE_all_Connected)
          apply(rename_tac j i)(*strict*)
          prefer 3
          apply(force)
         apply(force)
        apply(rename_tac j i)(*strict*)
        apply(force)
       apply(rename_tac j i)(*strict*)
       apply(force)
      apply(rename_tac j i)(*strict*)
      apply(force)
     apply(rename_tac j i)(*strict*)
     apply(force)
    apply(rename_tac j i)(*strict*)
    apply(force)
   apply(rename_tac j i)(*strict*)
   apply(rule_tac
      t="(q # F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G' F k) q w) ! Suc j"
      and s="(F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G' F k) q w) ! j"
      in ssubst)
    apply(rename_tac j i)(*strict*)
    apply(force)
   apply(rename_tac j i)(*strict*)
   apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G' F k) q w)"
      in set_mp)
    apply(rename_tac j i)(*strict*)
    apply(force)
   apply(rename_tac j i)(*strict*)
   apply(rule nth_mem)
   apply(subgoal_tac "length w= length (F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G' F k) q w)")
    apply(rename_tac j i)(*strict*)
    apply(force)
   apply(rename_tac j i)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac j i)(*strict*)
        apply(force)
       apply(rename_tac j i)(*strict*)
       apply(force)
      apply(rename_tac j i)(*strict*)
      apply(rule F_LR_MACHINE_all_Connected)
         apply(rename_tac j i)(*strict*)
         prefer 3
         apply(force)
        apply(force)
       apply(rename_tac j i)(*strict*)
       apply(force)
      apply(rename_tac j i)(*strict*)
      apply(force)
     apply(rename_tac j i)(*strict*)
     apply(force)
    apply(rename_tac j i)(*strict*)
    apply(force)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(rule_tac
      t="((q # F_DFA_GOTO_SEQUENCE M q w) ! Suc j)"
      and s="{}"
      in ssubst)
   apply(rename_tac j i)(*strict*)
   apply(force)
  apply(rename_tac j i)(*strict*)
  apply(simp (no_asm_use) only: F_VALID_ITEM_SET_GOTO_def)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__basis (w ! Suc j) {}"
      and s="{}"
      in ssubst)
   apply(rename_tac j i)(*strict*)
   apply(simp add: F_VALID_ITEM_SET_GOTO__basis_def)
  apply(rename_tac j i)(*strict*)
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G' F k {}"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS = SSS then SSS else F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk SSS))" for SSG SSF SSk SSS
      in ssubst)
   apply(rename_tac j i)(*strict*)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
  apply(rename_tac j i)(*strict*)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def)
  done

lemma rhs1_empty_items_due_to_specific_item: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> q \<in> (epda_states M)
  \<Longrightarrow> \<forall>I \<in> q. (cfg_item_lhs I \<noteq> S' \<longrightarrow> (cfg_item_rhs1 I = [] \<longrightarrow> (\<exists>J. setA (cfg_item_rhs2 J) \<subseteq> cfg_nonterminals G' \<and> (\<exists>w. cfg_item_rhs2 J = teA (cfg_item_lhs I) # w) \<and> J \<in> q)))"
  apply(rule_tac
      M="M"
      and P="\<lambda>q. \<forall>I \<in> q. (cfg_item_lhs I\<noteq>S' \<longrightarrow> (cfg_item_rhs1 I = [] \<longrightarrow> (\<exists>J. setA (cfg_item_rhs2 J) \<subseteq> cfg_nonterminals G' \<and> (\<exists>w. cfg_item_rhs2 J = teA (cfg_item_lhs I) # w) \<and> J \<in> q)))"
      in InductOverReachables)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def)
    apply(rule ballI)
    apply(rename_tac I)(*strict*)
    apply(rule impI)+
    apply(subgoal_tac "False")
     apply(rename_tac I)(*strict*)
     apply(force)
    apply(rename_tac I)(*strict*)
    prefer 2
    apply(rule allI)+
    apply(rename_tac p e qa cp cq)(*strict*)
    apply(rule impI)+
    apply(rule ballI)+
    apply(rename_tac p e qa cp cq I)(*strict*)
    apply(rule impI)+
    apply(subgoal_tac "e \<in> epda_delta M")
     apply(rename_tac p e qa cp cq I)(*strict*)
     prefer 2
     apply(simp add: epda_step_labels_def)
    apply(rename_tac p e qa cp cq I)(*strict*)
    apply(subgoal_tac "edge_src e = p \<and> edge_trg e = qa")
     apply(rename_tac p e qa cp cq I)(*strict*)
     prefer 2
     apply(case_tac cp)
     apply(rename_tac p e qa cp cq I epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack)(*strict*)
     apply(case_tac cq)
     apply(rename_tac p e qa cp cq I epdaS_conf_statea epdaS_conf_scheduler epdaS_conf_stack epdaS_conf_stateaa epdaS_conf_schedulera epdaS_conf_stacka)(*strict*)
     apply(simp add: epdaS_step_relation_def)
    apply(rename_tac p e qa cp cq I)(*strict*)
    apply(erule conjE)
    apply(subgoal_tac "\<exists>w a. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G') \<and> e=\<lparr>edge_src = valid_item_set G' k w, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE G' F k)], edge_push = [epda_box (F_LR_MACHINE G' F k)], edge_trg = valid_item_set G' k (w @ [a])\<rparr>")
     apply(rename_tac p e qa cp cq I)(*strict*)
     prefer 2
     apply(rule F_LR_MACHINE_edges_have_valid_item_set)
        apply(rename_tac p e qa cp cq I)(*strict*)
        apply(force)
       apply(rename_tac p e qa cp cq I)(*strict*)
       apply(force)
      apply(rename_tac p e qa cp cq I)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac p e qa cp cq I)(*strict*)
    apply(erule exE)+
    apply(rename_tac p e qa cp cq I w a)(*strict*)
    apply(subgoal_tac "qa=F_VALID_ITEM_SET_GOTO G' F k a (valid_item_set G' k w)")
     apply(rename_tac p e qa cp cq I w a)(*strict*)
     prefer 2
     apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G' F k a (valid_item_set G' k w)"
      and s="valid_item_set G' k (w@[a])"
      in subst)
      apply(rename_tac p e qa cp cq I w a)(*strict*)
      apply(rule Lemma6__26)
         apply(rename_tac p e qa cp cq I w a)(*strict*)
         apply(force)
        apply(force)
       apply(rename_tac p e qa cp cq I w a)(*strict*)
       defer
       defer
       apply(force)
      apply(rename_tac p e qa cp cq I w a)(*strict*)
      apply(erule conjE)
      apply(thin_tac "valid_cfg G")
      apply(thin_tac "Do = F_FRESH (cfg_events G)")
      apply(thin_tac "S' = F_FRESH (cfg_nonterminals G)")
      apply(thin_tac "G' = F_CFG_AUGMENT G S' Do")
      apply(thin_tac "M = F_LR_MACHINE G' F k")
      apply(thin_tac "valid_dfa M")
      apply(thin_tac "q \<in> epda_states M")
      apply(rename_tac p e q cp cq I w a)(*strict*)
      apply(thin_tac "cp \<in> epdaS_configurations M")
      apply(thin_tac "cq \<in> epdaS_configurations M")
      apply(thin_tac "p \<in> epdaS_accessible_states M")
      apply(thin_tac "\<forall>I \<in> p. cfg_item_lhs I \<noteq> S' \<longrightarrow> cfg_item_rhs1 I = [] \<longrightarrow> (\<exists>J. setA (cfg_item_rhs2 J) \<subseteq> cfg_nonterminals G' \<and> (\<exists>w. cfg_item_rhs2 J = teA (cfg_item_lhs I) # w) \<and> J \<in> p)")
      apply(thin_tac "epdaS_conf_state cp = p")
      apply(thin_tac "epdaS_conf_state cq = q")
      apply(thin_tac "epdaS_step_relation M cp e cq")
      apply(thin_tac "e \<in> epda_step_labels M")
      apply(thin_tac "e \<in> epda_delta M")
      apply(thin_tac "edge_src e = p")
      apply(thin_tac "edge_trg e = q")
      apply(thin_tac "e = \<lparr>edge_src = valid_item_set G' k w, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE G' F k)], edge_push = [epda_box (F_LR_MACHINE G' F k)], edge_trg = valid_item_set G' k (w @ [a])\<rparr>")
      apply(thin_tac "cfg_item_lhs I \<noteq> S'")
      apply(clarsimp)
      apply(rename_tac I w a)(*strict*)
      apply(simp only: F_VALID_ITEM_SET_GOTO_def)
      apply(case_tac "(F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w)) = F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w))")
       apply(rename_tac I w a)(*strict*)
       apply(subgoal_tac "False")
        apply(rename_tac I w a)(*strict*)
        apply(force)
       apply(rename_tac I w a)(*strict*)
       apply(rule F_VALID_ITEM_SET_GOTO__basis_makes_nonempty_rhs1)
        apply(rename_tac I w a)(*strict*)
        apply(force)
       apply(rename_tac I w a)(*strict*)
       apply(force)
      apply(rename_tac I w a)(*strict*)
      apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w) \<subseteq> Collect (valid_item G' k)")
       apply(rename_tac I w a)(*strict*)
       prefer 2
       apply(rule F_VALID_ITEM_SET_GOTO__basis_preserves_item_set)
       apply(clarsimp)
       apply(rename_tac I w a x)(*strict*)
       apply(rule Fact6_12__2)
        apply(rename_tac I w a x)(*strict*)
        apply(force)
       apply(rename_tac I w a x)(*strict*)
       apply(force)
      apply(rename_tac I w a)(*strict*)
      apply(subgoal_tac "I \<notin> F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w)")
       apply(rename_tac I w a)(*strict*)
       prefer 2
       apply(case_tac "I \<notin> F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w)")
        apply(rename_tac I w a)(*strict*)
        apply(force)
       apply(rename_tac I w a)(*strict*)
       apply(clarsimp)
       apply(rule F_VALID_ITEM_SET_GOTO__basis_makes_nonempty_rhs1)
        apply(rename_tac I w a)(*strict*)
        apply(force)
       apply(rename_tac I w a)(*strict*)
       apply(force)
      apply(rename_tac I w a)(*strict*)
      apply(subgoal_tac "\<exists>J \<in> F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk SSS. \<exists>w. cfg_item_rhs2 J = teA (cfg_item_lhs SSI) # w" for SSG SSF SSk SSS SSI)
       apply(rename_tac I w a)(*strict*)
       prefer 2
       apply(rule_tac
      S="F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w)"
      in F_VALID_ITEM_SET_GOTO__descent__fp_has_reason_prime)
          apply(rename_tac I w a)(*strict*)
          apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
          apply(rule conjI)
           apply(rename_tac I w a)(*strict*)
           apply(force)
          apply(rename_tac I w a)(*strict*)
          apply(force)
         apply(rename_tac I w a)(*strict*)
         apply(force)
        apply(rename_tac I w a)(*strict*)
        apply(force)
       apply(rename_tac I w a)(*strict*)
       apply(force)
      apply(rename_tac I w a)(*strict*)
      apply(clarsimp)
      apply(rename_tac I w a J wa)(*strict*)
      apply(rule_tac
      x="J"
      in exI)
      apply(rule context_conjI)
       apply(rename_tac I w a J wa)(*strict*)
       apply(subgoal_tac "valid_item G' k J")
        apply(rename_tac I w a J wa)(*strict*)
        apply(simp only: valid_item_def)
        apply(erule conjE)+
        apply(erule bexE)+
        apply(rename_tac I w a J wa p)(*strict*)
        apply(erule conjE)+
        apply(simp only: valid_cfg_def)
        apply(erule conjE)+
        apply(erule_tac
      x="p"
      in ballE)
         apply(rename_tac I w a J wa p)(*strict*)
         apply(rule_tac
      B="setA (prod_rhs p)"
      in subset_trans)
          apply(rename_tac I w a J wa p)(*strict*)
          apply(simp only: setAConcat concat_asso)
          apply(force)
         apply(rename_tac I w a J wa p)(*strict*)
         apply(force)
        apply(rename_tac I w a J wa p)(*strict*)
        apply(force)
       apply(rename_tac I w a J wa)(*strict*)
       apply(subgoal_tac "Ball (F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis a (valid_item_set G' k w))) (valid_item G' k)")
        apply(rename_tac I w a J wa)(*strict*)
        prefer 2
        apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_F_VALID_ITEM_SET_GOTO__descent__fp_EXTRA_02_unfold)
        apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
        apply(force)
       apply(rename_tac I w a J wa)(*strict*)
       apply(force)
      apply(rename_tac I w a J wa)(*strict*)
      apply(clarsimp)
     apply(rename_tac I)(*strict*)
     apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_INITIAL G' F k")
      apply(rename_tac I)(*strict*)
      apply(subgoal_tac "I \<in> {\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}")
       apply(rename_tac I)(*strict*)
       apply(force)
      apply(rename_tac I)(*strict*)
      apply(rule_tac
      t="{\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}"
      and s="F_VALID_ITEM_SET_INITIAL G' F k"
      in subst)
       apply(rename_tac I)(*strict*)
       apply(rule F_CFG_AUGMENT__F_VALID_ITEM_SET_INITIAL)
            apply(rename_tac I)(*strict*)
            apply(force)
           apply(rename_tac I)(*strict*)
           apply(force)
          apply(rename_tac I)(*strict*)
          apply(force)
         apply(rename_tac I)(*strict*)
         apply(force)
        apply(rename_tac I)(*strict*)
        apply(force)
       apply(rename_tac I)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac I)(*strict*)
     apply(simp add: F_LR_MACHINE_def)
    apply(rule_tac
      G="G'"
      in F_LR_MACHINE_all_epdaS_accessible_states)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rename_tac p e qa cp cq I w a)(*strict*)
   apply(simp (no_asm_use) only: setAConcat concat_asso)
   apply(rule Un_least)
    apply(rename_tac p e qa cp cq I w a)(*strict*)
    apply(rule two_elements_construct_domain_setA)
    apply(force)
   apply(rename_tac p e qa cp cq I w a)(*strict*)
   prefer 2
   apply(simp (no_asm_use) only: setBConcat concat_asso)
   apply(rule Un_least)
    apply(rename_tac p e qa cp cq I w a)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(rename_tac p e qa cp cq I w a)(*strict*)
   apply(subgoal_tac "a \<in> epda_events M")
    apply(rename_tac p e qa cp cq I w a)(*strict*)
    prefer 2
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(clarsimp)
    apply(rename_tac cp cq I w a)(*strict*)
    apply(erule_tac
      x="\<lparr>edge_src = epdaS_conf_state cp, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)], edge_push = [epda_box (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)], edge_trg = epdaS_conf_state cq\<rparr>"
      and P="\<lambda>e. valid_epda_step_label (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k) e"
      in ballE)
     apply(rename_tac cp cq I w a)(*strict*)
     apply(simp add: valid_epda_step_label_def option_to_set_def)
    apply(rename_tac cp cq I w a)(*strict*)
    apply(clarsimp)
   apply(rename_tac p e qa cp cq I w a)(*strict*)
   apply(case_tac a)
    apply(rename_tac p e qa cp cq I w a aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac p e qa cp cq I w a b)(*strict*)
   apply(simp add: F_LR_MACHINE_def)
   apply(clarsimp)
   apply(rename_tac cp cq I w b)(*strict*)
   apply(simp add: two_elements_construct_domain_def)
   apply(erule disjE)
    apply(rename_tac cp cq I w b)(*strict*)
    apply(clarsimp)
   apply(rename_tac cp cq I w b)(*strict*)
   apply(clarsimp)
  apply(rename_tac p e qa cp cq I w a)(*strict*)
  apply(subgoal_tac "a \<in> epda_events M")
   apply(rename_tac p e qa cp cq I w a)(*strict*)
   prefer 2
   apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(clarsimp)
   apply(rename_tac cp cq I w a)(*strict*)
   apply(erule_tac
      x="\<lparr>edge_src = epdaS_conf_state cp, edge_event = Some a, edge_pop = [epda_box (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)], edge_push = [epda_box (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k)], edge_trg = epdaS_conf_state cq\<rparr>"
      and P="\<lambda>e. valid_epda_step_label (F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k) e"
      in ballE)
    apply(rename_tac cp cq I w a)(*strict*)
    apply(simp add: valid_epda_step_label_def option_to_set_def)
   apply(rename_tac cp cq I w a)(*strict*)
   apply(clarsimp)
  apply(rename_tac p e qa cp cq I w a)(*strict*)
  apply(case_tac a)
   apply(rename_tac p e qa cp cq I w a aa)(*strict*)
   prefer 2
   apply(rename_tac p e qa cp cq I w a b)(*strict*)
   apply(clarsimp)
  apply(rename_tac p e qa cp cq I w a aa)(*strict*)
  apply(simp add: F_LR_MACHINE_def)
  apply(clarsimp)
  apply(rename_tac cp cq I w aa)(*strict*)
  apply(simp add: two_elements_construct_domain_def)
  apply(erule disjE)
   apply(rename_tac cp cq I w aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac cp cq I w aa)(*strict*)
  apply(clarsimp)
  done

lemma DollarTailStays_notS_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> q \<in> (epda_states M)
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> cfg_item_lhs I \<noteq> S'
  \<Longrightarrow> (cfg_item_look_ahead I) \<in> ((kPrefix k) ` {w @ [Do]|w. set w \<subseteq> (cfg_events G)})"
  apply(subgoal_tac "\<forall>I \<in> q. (cfg_item_lhs I=S' \<longrightarrow> cfg_item_look_ahead I = []) \<and> (cfg_item_lhs I\<noteq>S' \<longrightarrow> ((cfg_item_look_ahead I) \<in> ((kPrefix k) ` ({w@[Do]|w. set w \<subseteq> (cfg_events G)}))))")
   prefer 2
   apply(rule DollarTailStays)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(erule_tac
      x="I"
      in ballE)
   prefer 2
   apply(force)
  apply(clarsimp)
  done

lemma F_LR_MACHINE_elem_in_GOTO_Do: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> \<lparr>cfg_item_lhs = F_FRESH (cfg_nonterminals G), cfg_item_rhs1 = [teB Do], cfg_item_rhs2 = [teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr> \<in> F_DFA_GOTO M (epda_initial M) (teB Do)"
  apply(subgoal_tac "(last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])))-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} ={\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do], cfg_item_rhs2=[teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}")
   prefer 2
   apply(rule F_LR_MACHINE_prefix_closureise_additionalItems_1)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      A="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) - {I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}"
      in set_mp)
   apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      and s="F_DFA_GOTO M (epda_initial M) (teB Do)"
      in ssubst)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]"
      and s="[F_DFA_GOTO M (epda_initial M) (teB Do)]"
      in ssubst)
     apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
         apply(force)
        apply(force)
       apply(rule F_LR_MACHINE_all_Connected)
          prefer 3
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def F_LR_MACHINE_def)
     apply(rule F_LR_MACHINE_Do_in_cfg_events)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma LRM_contains_theEqClasses2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)
  \<Longrightarrow> valid_item_set G k w \<in> epda_states M"
  apply(rule_tac
      t="epda_states M"
      and s="{valid_item_set SSG SSk w |w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals SSG) (cfg_events SSG)}" for SSG SSk
      in ssubst)
   apply(rule LRM_contains_theEqClasses)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_all_SOUND_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> M = F_LR_MACHINE G F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> valid_item_set G k w = last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
  apply(rule_tac
      t="valid_item_set G k w"
      and s="(if w=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w))"
      in ssubst)
   apply(rule F_LR_MACHINE_all_SOUND)
         apply(blast)+
  apply(clarsimp)
  apply(subgoal_tac "length w=length (F_DFA_GOTO_SEQUENCE (F_LR_MACHINE G F k) (epda_initial (F_LR_MACHINE G F k)) w)")
   prefer 2
   apply(rule_tac
      w="w"
      and q="(epda_initial (F_LR_MACHINE G F k))"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(rule F_LR_MACHINE_all_Connected)
         prefer 3
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: F_LR_MACHINE_def)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(simp add: F_LR_MACHINE_def)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_last_not_empty_starts_with_dollar: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> w \<noteq> []
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w) \<noteq> {}
  \<Longrightarrow> \<exists>w'. w = teB Do # w'"
  apply(subgoal_tac "valid_item_set G' k w \<noteq> {}")
   prefer 2
   apply(rule_tac
      t="valid_item_set G' k w"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w)"
      in ssubst)
    apply(rule F_LR_MACHINE_all_SOUND_NotNil)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(rule two_elements_construct_domain_setA)
      apply(simp add: F_LR_MACHINE_def)
     apply(rule two_elements_construct_domain_setB)
     apply(simp add: F_LR_MACHINE_def)
    apply(force)
   apply(force)
  apply(thin_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) w) \<noteq> {}")
  apply(simp add: valid_item_set_def valid_item_set_n_def)
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d \<delta>)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(blast)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(subgoal_tac "\<exists>e w. d (Suc n) = Some (pair e \<lparr>cfg_conf = teB Do # w\<rparr>)")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule_tac
      G="G'"
      and m="Suc 0"
      and n="n"
      in terminal_at_beginning_are_never_modified)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(rule cfgRM_derivations_are_cfg_derivations)
       apply(force)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(force)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
  apply(case_tac \<delta>)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
   apply(case_tac \<alpha>)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa)(*strict*)
    apply(clarsimp)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z e wa a list)(*strict*)
  apply(clarsimp)
  done

lemma F_LR_MACHINE_F_DFA_GOTO_SEQUENCE_inj: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> set v \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w) = F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # v)
  \<Longrightarrow> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # v)) \<noteq> {}
  \<Longrightarrow> w = v"
  apply(subgoal_tac "teB Do # w=teB Do#v")
   apply(force)
  apply(rule_tac
      q="epda_initial M"
      and r="F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w)"
      and P="\<lambda>x. x\<noteq>{}"
      in F_DFA_GOTO_SEQUENCE_injective_prime)
           apply(blast)
          apply(blast)
         apply(rule F_LR_MACHINE_all_Connected)
            prefer 3
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(rule valid_epda_initial_in_states)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(simp add: set_Cons)
       apply(rule_tac
      G="G"
      in F_LR_MACHINE_Do_in_cfg_events)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: set_Cons)
      apply(rule_tac
      G="G"
      in F_LR_MACHINE_Do_in_cfg_events)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(subgoal_tac "length (teB Do # w) = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w))")
    apply(rule allI)
    apply(rename_tac i)(*strict*)
    apply(rule impI)
    apply(case_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w) ! i = {}")
     apply(rename_tac i)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w)) = {}")
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w))"
      and s=" (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w))! ((length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (teB Do # w))) - 1)"
      in ssubst)
     apply(rename_tac i)(*strict*)
     apply(rule last_nth3)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(rule_tac
      G="G"
      and q="epda_initial M"
      in F_LR_MACHINE_nonempty_shifts_back_mult_prime)
                 apply(rename_tac i)(*strict*)
                 apply(force)
                apply(rename_tac i)(*strict*)
                apply(force)
               apply(rename_tac i)(*strict*)
               apply(force)
              apply(rename_tac i)(*strict*)
              apply(force)
             apply(rename_tac i)(*strict*)
             apply(force)
            apply(rename_tac i)(*strict*)
            apply(force)
           apply(force)
          apply(rename_tac i)(*strict*)
          apply(force)
         apply(rename_tac i)(*strict*)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(rule valid_epda_initial_in_states)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac i)(*strict*)
       apply(simp add: set_Cons)
       apply(rule_tac
      G="G"
      in F_LR_MACHINE_Do_in_cfg_events)
            apply(rename_tac i)(*strict*)
            apply(force)
           apply(rename_tac i)(*strict*)
           apply(force)
          apply(rename_tac i)(*strict*)
          apply(force)
         apply(rename_tac i)(*strict*)
         apply(force)
        apply(rename_tac i)(*strict*)
        apply(force)
       apply(rename_tac i)(*strict*)
       apply(force)
      apply(rename_tac i)(*strict*)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(force)
   apply(rule_tac
      q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(rule F_LR_MACHINE_all_Connected)
         prefer 3
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(clarsimp)
     apply(rule valid_epda_initial_in_states)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(simp add: set_Cons)
    apply(rule_tac
      G="G"
      in F_LR_MACHINE_Do_in_cfg_events)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule_tac
      t="epda_delta M"
      and s="snd(F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})"
      in ssubst)
   apply(simp add: F_LR_MACHINE_def)
  apply(rule F_LR_MACHINE_all_uniqueEntry)
   apply(force)
  apply(force)
  done

lemma F_LR_MACHINE_la_not_empty: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> M = F_LR_MACHINE G' F (Suc k)
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> I \<in> valid_item_set G' (Suc k) (teB Do # w)
  \<Longrightarrow> w \<noteq> [teA (cfg_initial G), teB Do]
  \<Longrightarrow> setA (teB Do # w) \<subseteq> cfg_nonterminals G'
  \<Longrightarrow> setB (teB Do # w) \<subseteq> cfg_events G'
  \<Longrightarrow> cfg_item_rhs2 I @ liftB (cfg_item_look_ahead I) \<noteq> []"
  apply(simp (no_asm_use) add: valid_item_set_def valid_item_set_n_def)
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d)(*strict*)
  apply(erule conjE)+
  apply(erule exE)+
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(erule conjE)+
  apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   prefer 2
   apply(rule F_CFG_AUGMENT__FirstStep)
          apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
          apply(force)
         apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
         apply(force)
        apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
        apply(force)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
       apply(force)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
      apply(force)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
     apply(rule cfgRM_derivations_are_cfg_derivations)
     apply(force)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(force)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
  apply(case_tac n)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z)(*strict*)
   apply(clarsimp)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
  apply(subgoal_tac "\<exists>e w. teB Do \<notin> set w \<and> (teA S') \<notin> set w \<and> d (Suc nat) = Some (pair e \<lparr>cfg_conf=teB Do#w@[teB Do]\<rparr>)")
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      in F_CFG_AUGMENT__on_old_grammar_basically)
           apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
           apply(force)
          apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
          apply(force)
         apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
         apply(force)
        apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
        apply(force)
       apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
       apply(force)
      apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(force)
     apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
     apply(force)
    apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
   apply(force)
  apply(rename_tac n A \<alpha> \<beta> y d \<delta> e1 e2 z nat)(*strict*)
  apply(clarsimp)
  done

lemma F_LR_MACHINE_items_with_core_from_old_grammar_have_nonempty_lookahead: "
  F_CFG_AUGMENT__input G Do S' G'
  \<Longrightarrow> cfgSTD_first_compatible F (Suc k)
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> M = F_LR_MACHINE G' F (Suc k)
  \<Longrightarrow> q \<in> epda_states M
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> item_core I \<in> cfg_productions G
  \<Longrightarrow> cfg_item_look_ahead I \<noteq> []"
  apply(subgoal_tac "\<exists>w. q=valid_item_set G' (Suc k) w")
   apply(thin_tac "q \<in> epda_states M")
   apply(thin_tac "M = F_LR_MACHINE G' F (Suc k)")
   apply(clarsimp)
   apply(rename_tac w)(*strict*)
   apply(simp add: valid_item_set_def valid_item_set_n_def)
   apply(clarsimp)
   apply(rename_tac n A \<alpha> \<beta> d \<delta> e1 e2)(*strict*)
   apply(case_tac n)
    apply(rename_tac n A \<alpha> \<beta> d \<delta> e1 e2)(*strict*)
    apply(clarsimp)
    apply(rename_tac \<alpha> \<beta> d e2)(*strict*)
    apply(simp add: item_core_def)
    apply(simp (no_asm_use) add: F_CFG_AUGMENT__input_def valid_cfg_def)
    apply(erule conjE)+
    apply(erule_tac
      x="\<lparr>prod_lhs = cfg_initial G', prod_rhs = \<alpha> @ \<beta>\<rparr>"
      and A="cfg_productions G"
      in ballE)
     apply(rename_tac \<alpha> \<beta> d e2)(*strict*)
     apply(erule conjE)+
     apply(simp (no_asm_use))
     apply(subgoal_tac "cfg_initial G' \<notin> cfg_nonterminals G")
      apply(rename_tac \<alpha> \<beta> d e2)(*strict*)
      apply(force)
     apply(rename_tac \<alpha> \<beta> d e2)(*strict*)
     apply(simp (no_asm_use) add: F_CFG_AUGMENT_def)
     apply(simp (no_asm_simp))
     apply(rule F_FRESH_is_fresh)
     apply(force)
    apply(rename_tac \<alpha> \<beta> d e2)(*strict*)
    apply(force)
   apply(rename_tac n A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
   apply(subgoal_tac "d (Suc 0)= Some (pair (Some \<lparr>prod_lhs=cfg_initial G', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>) \<lparr>cfg_conf=[teB Do, teA (cfg_initial G), teB Do]\<rparr>)")
    apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
    prefer 2
    apply(rule F_CFG_AUGMENT__FirstStep)
           apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
           apply(simp add: F_CFG_AUGMENT__input_def)
          apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
          apply(simp add: F_CFG_AUGMENT__input_def)
         apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
         apply(force)
        apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
        apply(simp add: F_CFG_AUGMENT__input_def)
       apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
       apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
      apply(simp add: F_CFG_AUGMENT__input_def)
      apply(rule cfgRM_derivations_are_cfg_derivations)
      apply(force)
     apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
     apply(force)
    apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
   apply(subgoal_tac "\<exists>e w. d (Suc nat) = Some (pair e \<lparr>cfg_conf = w @ [teB Do]\<rparr>)")
    apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
    prefer 2
    apply(rule_tac
      G="G'"
      and m="Suc 0"
      in terminals_at_ending_are_never_modified_list)
         apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
         apply(rule cfgRM_derivations_are_cfg_derivations)
         apply(force)
        apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
        apply(force)
       apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
       apply(force)
      apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
      apply(force)
     apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
     apply(force)
    apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
    apply(force)
   apply(rename_tac A \<alpha> \<beta> d \<delta> e1 e2 nat)(*strict*)
   apply(clarsimp)
  apply(subgoal_tac "\<exists>w. q=valid_item_set G' (Suc k) w \<and> set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')")
   prefer 2
   apply(subgoal_tac "epda_states M = {valid_item_set G' (Suc k) w|w. set w \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')}")
    prefer 2
    apply(rule LRM_contains_theEqClasses)
      apply(simp add: F_CFG_AUGMENT__input_def)
     apply(force)
    apply(simp add: F_CFG_AUGMENT__input_def)
   apply(force)
  apply(force)
  done

lemma partial_F_DFA_GOTO_SEQUENCE_eq_implies_existence_of_sub_F_DFA_GOTO_SEQUENCEs: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> q1 = epda_initial M
  \<Longrightarrow> set w1 \<subseteq> epda_events M
  \<Longrightarrow> set w2 \<subseteq> epda_events M
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M q1 w1 = v @ q2 # F_DFA_GOTO_SEQUENCE M q2 w2
  \<Longrightarrow> q2 \<noteq> {}
  \<Longrightarrow> last (q2 # F_DFA_GOTO_SEQUENCE M q2 w2) \<noteq> {}
  \<Longrightarrow> \<exists>w x. w @ x # w2 = w1 \<and> v = F_DFA_GOTO_SEQUENCE M q1 w \<and> q2 = F_DFA_GOTO M (last (q1 # v)) x"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(subgoal_tac "q2 \<in> epda_states M")
   prefer 2
   apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE M q1 w1)"
      in set_mp)
    apply(rule F_DFA_GOTO_SEQUENCESound_main3)
         apply(force)
        apply(force)
       prefer 4
       apply(force)
      prefer 2
      apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
     prefer 2
     apply(force)
    prefer 2
    apply(force)
   apply(force)
  apply(subgoal_tac "length w1=length v+Suc 0+length w2")
   prefer 2
   apply(subgoal_tac "length w1=length (F_DFA_GOTO_SEQUENCE M q1 w1)")
    apply(subgoal_tac "length w2=length (F_DFA_GOTO_SEQUENCE M q2 w2)")
     apply(force)
    apply(rule F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     prefer 3
     apply(force)
    apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
   apply(force)
  apply(subgoal_tac "\<exists>w x wX. w @ x # wX = w1 \<and> length wX=length w2")
   prefer 2
   apply(rule_tac
      x="take (length v) w1"
      in exI)
   apply(rule_tac
      x="hd (drop (length v) w1)"
      in exI)
   apply(rule_tac
      x="drop (Suc(length v)) w1"
      in exI)
   apply(rule word_decompose)
   apply(blast)
  apply(erule exE)+
  apply(rename_tac w x wX)(*strict*)
  apply(rule_tac
      x="w"
      in exI)
  apply(rule_tac
      x="x"
      in exI)
  apply(subgoal_tac "length w2=length (F_DFA_GOTO_SEQUENCE M q2 w2)")
   apply(rename_tac w x wX)(*strict*)
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(subgoal_tac "length w=length (F_DFA_GOTO_SEQUENCE M q1 w)")
   apply(rename_tac w x wX)(*strict*)
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
   apply(rename_tac w x wX)(*strict*)
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(subgoal_tac "length (w@[x])=length (F_DFA_GOTO_SEQUENCE M q1 (w@[x]))")
   apply(rename_tac w x wX)(*strict*)
   prefer 2
   apply(rule F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
   apply(rename_tac w x wX)(*strict*)
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(subgoal_tac "length w=length v")
   apply(rename_tac w x wX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M q1 w1 = (F_DFA_GOTO_SEQUENCE M q1 w) @ (F_DFA_GOTO M (last (q1 # (F_DFA_GOTO_SEQUENCE M q1 w))) x) # F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (last (q1 # (F_DFA_GOTO_SEQUENCE M q1 w))) x) wX")
   apply(rename_tac w x wX)(*strict*)
   apply(subgoal_tac "v = F_DFA_GOTO_SEQUENCE M q1 w")
    apply(rename_tac w x wX)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(subgoal_tac "q2 = F_DFA_GOTO M (last (q1 # v)) x")
    apply(rename_tac w x wX)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(subgoal_tac "w2=wX")
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(subgoal_tac "F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) x) wX = F_DFA_GOTO_SEQUENCE M q2 w2")
    apply(rename_tac w x wX)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(subgoal_tac "w@x#wX=w@x#w2")
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      q="epda_initial M"
      and r="F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@x#wX)"
      and P="\<lambda>x. x\<noteq>{}"
      in F_DFA_GOTO_SEQUENCE_injective_prime)
            apply(rename_tac w x wX)(*strict*)
            apply(force)
           apply(rename_tac w x wX)(*strict*)
           apply(force)
          apply(rename_tac w x wX)(*strict*)
          apply(force)
         apply(rename_tac w x wX)(*strict*)
         apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(rule_tac
      t="w@x#wX"
      and s="w1"
      in ssubst)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(rule_tac
      t="F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k"
      and s="M"
      in ssubst)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ x # w2)"
      and s="F_DFA_GOTO_SEQUENCE M q1 w @ F_DFA_GOTO M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) x # F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) x) w2"
      in ssubst)
      apply(rename_tac w x wX)(*strict*)
      defer
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(rule allI)
     apply(rename_tac w x wX i)(*strict*)
     apply(rule impI)
     apply(case_tac "F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@x#wX) ! i = {}")
      apply(rename_tac w x wX i)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac w x wX i)(*strict*)
     apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@x#wX)) = {}")
      apply(rename_tac w x wX i)(*strict*)
      apply(force)
     apply(rename_tac w x wX i)(*strict*)
     apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@x#wX))"
      and s=" (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@x#wX))! ((length (F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@x#wX))) - 1)"
      in ssubst)
      apply(rename_tac w x wX i)(*strict*)
      apply(rule last_nth3)
      apply(rename_tac w x wX i)(*strict*)
      apply(force)
     apply(rename_tac w x wX i)(*strict*)
     apply(rule_tac
      G="G"
      and q="epda_initial M"
      in F_LR_MACHINE_nonempty_shifts_back_mult_prime)
                  apply(rename_tac w x wX i)(*strict*)
                  apply(force)
                 apply(force)
                apply(rename_tac w x wX i)(*strict*)
                apply(force)
               apply(rename_tac w x wX i)(*strict*)
               apply(force)
              apply(rename_tac w x wX i)(*strict*)
              apply(force)
             apply(rename_tac w x wX i)(*strict*)
             apply(force)
            apply(rename_tac w x wX i)(*strict*)
            apply(force)
           apply(rename_tac w x wX i)(*strict*)
           apply(force)
          apply(rename_tac w x wX i)(*strict*)
          apply(force)
         apply(rename_tac w x wX i)(*strict*)
         apply(rule valid_epda_initial_in_states)
         apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
        apply(rename_tac w x wX i)(*strict*)
        apply(simp add: set_Cons)
       apply(rename_tac w x wX i)(*strict*)
       apply(force)
      apply(rename_tac w x wX i)(*strict*)
      apply(force)
     apply(rename_tac w x wX i)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(rule_tac
      t="F_LR_MACHINE (F_CFG_AUGMENT G (F_FRESH (cfg_nonterminals G)) (F_FRESH (cfg_events G))) F k"
      and s="M"
      in ssubst)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(rule_tac
      t="epda_delta M"
      and s="snd(F_LR_MACHINE__fp_one G' F k {} {} {F_VALID_ITEM_SET_INITIAL G' F k})"
      in ssubst)
     apply(rename_tac w x wX)(*strict*)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac w x wX)(*strict*)
    apply(rule F_LR_MACHINE_all_uniqueEntry)
     apply(force)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      t="w1"
      and s="(w@[x])@wX"
      in ssubst)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q1 ((w @ [x]) @ wX)"
      and s="F_DFA_GOTO_SEQUENCE M q1 (w @ [x]) @ (F_DFA_GOTO_SEQUENCE M (last (q1#(F_DFA_GOTO_SEQUENCE M q1 (w@[x])))) wX)"
      in ssubst)
    apply(rename_tac w x wX)(*strict*)
    apply(rule F_DFA_GOTO_SEQUENCE_append_split)
         apply(rename_tac w x wX)(*strict*)
         apply(force)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 (w @ [x]))) wX"
      and s="F_DFA_GOTO_SEQUENCE M (F_DFA_GOTO M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) x) wX"
      in ssubst)
    apply(rename_tac w x wX)(*strict*)
    apply(rule_tac
      t="(last (q1 # F_DFA_GOTO_SEQUENCE M q1 (w @ [x])))"
      and s="(F_DFA_GOTO M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) x)"
      in ssubst)
     apply(rename_tac w x wX)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(rule_tac
      t="last (q1 # F_DFA_GOTO_SEQUENCE M q1 (w @ [x]))"
      and s="last(F_DFA_GOTO_SEQUENCE M q1 (w @ [x]))"
      in ssubst)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(rule F_DFA_GOTO_SEQUENCE_dropTerminal_last)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q1 (w @ [x])"
      and s="F_DFA_GOTO_SEQUENCE M q1 w @ [F_DFA_GOTO M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) x]"
      in ssubst)
    apply(rename_tac w x wX)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q1 (w @ [x])"
      and s="F_DFA_GOTO_SEQUENCE M q1 w @ (F_DFA_GOTO_SEQUENCE M (last (q1#(F_DFA_GOTO_SEQUENCE M q1 w))) [x])"
      in ssubst)
    apply(rename_tac w x wX)(*strict*)
    apply(rule F_DFA_GOTO_SEQUENCE_append_split)
         apply(rename_tac w x wX)(*strict*)
         apply(force)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) [x]"
      and s="[F_DFA_GOTO M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) x]"
      in ssubst)
    apply(rename_tac w x wX)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(case_tac w)
    apply(rename_tac w x wX)(*strict*)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q1 w"
      and s="[]"
      in ssubst)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(rule_tac
      t="last [q1]"
      and s="q1"
      in ssubst)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
   apply(rename_tac w x wX a list)(*strict*)
   apply(rule_tac
      t="last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)"
      and s="last (F_DFA_GOTO_SEQUENCE M q1 w)"
      in ssubst)
    apply(rename_tac w x wX a list)(*strict*)
    apply(force)
   apply(rename_tac w x wX a list)(*strict*)
   apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE M q1 w)"
      in set_mp)
    apply(rename_tac w x wX a list)(*strict*)
    apply(rule F_DFA_GOTO_SEQUENCESound_main3)
         apply(rename_tac w x wX a list)(*strict*)
         apply(force)
        apply(rename_tac w x wX a list)(*strict*)
        apply(force)
       apply(rename_tac w x wX a list)(*strict*)
       prefer 4
       apply(force)
      apply(rename_tac w x wX a list)(*strict*)
      prefer 2
      apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
     apply(rename_tac w x wX a list)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac w x wX a list)(*strict*)
    apply(force)
   apply(rename_tac w x wX a list)(*strict*)
   apply(rule last_in_set)
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(rule_tac
      t="w@x#w2"
      and s="(w@[x])@w2"
      in ssubst)
   apply(rename_tac w x wX)(*strict*)
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) ((w @ [x]) @ w2)"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@[x]) @ (F_DFA_GOTO_SEQUENCE M (last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) (w@[x])))) w2)"
      in ssubst)
   apply(rename_tac w x wX)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_append_split)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) (w @ [x])"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) w @ (F_DFA_GOTO_SEQUENCE M (last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) w))) [x])"
      in ssubst)
   apply(rename_tac w x wX)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCE_append_split)
        apply(rename_tac w x wX)(*strict*)
        apply(force)
       apply(rename_tac w x wX)(*strict*)
       apply(force)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(rule_tac
      t="epda_initial M"
      and s="q1"
      in ssubst)
   apply(rename_tac w x wX)(*strict*)
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) [x]"
      and s="[F_DFA_GOTO M (last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)) x]"
      in ssubst)
   apply(rename_tac w x wX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(rule DFA_F_DFA_GOTO_SEQUENCE_to_F_DFA_GOTO)
      apply(rename_tac w x wX)(*strict*)
      apply(force)
     apply(rename_tac w x wX)(*strict*)
     apply(force)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac w x wX)(*strict*)
  apply(case_tac w)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M q1 w"
      and s="[]"
      in ssubst)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(rule_tac
      t="last [q1]"
      and s="q1"
      in ssubst)
    apply(rename_tac w x wX)(*strict*)
    apply(force)
   apply(rename_tac w x wX)(*strict*)
   apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
  apply(rename_tac w x wX a list)(*strict*)
  apply(rule_tac
      t="last (q1 # F_DFA_GOTO_SEQUENCE M q1 w)"
      and s="last (F_DFA_GOTO_SEQUENCE M q1 w)"
      in ssubst)
   apply(rename_tac w x wX a list)(*strict*)
   apply(force)
  apply(rename_tac w x wX a list)(*strict*)
  apply(rule_tac
      A="set (F_DFA_GOTO_SEQUENCE M q1 w)"
      in set_mp)
   apply(rename_tac w x wX a list)(*strict*)
   apply(rule F_DFA_GOTO_SEQUENCESound_main3)
        apply(rename_tac w x wX a list)(*strict*)
        apply(force)
       apply(rename_tac w x wX a list)(*strict*)
       apply(force)
      apply(rename_tac w x wX a list)(*strict*)
      prefer 4
      apply(force)
     apply(rename_tac w x wX a list)(*strict*)
     prefer 2
     apply(simp add: valid_dfa_def valid_pda_def valid_dpda_def valid_epda_def)
    apply(rename_tac w x wX a list)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac w x wX a list)(*strict*)
   apply(force)
  apply(rename_tac w x wX a list)(*strict*)
  apply(rule last_in_set)
  apply(force)
  done

lemma F_LR_MACHINE_Single_Initial_Item: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> I \<in> epda_initial M
  \<Longrightarrow> I = \<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>"
  apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_INITIAL G' F k")
   prefer 2
   apply(rule_tac
      t="F_VALID_ITEM_SET_INITIAL G' F k"
      and s="valid_item_set G' k []"
      in subst)
    apply(rule Lemma6__23_1)
     apply(force)
    apply(force)
   apply(rule_tac
      t="valid_item_set G' k []"
      and s="epda_initial M"
      in ssubst)
    apply(rule F_LR_MACHINE_all_SOUND_Nil)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp (no_asm_use) only: F_VALID_ITEM_SET_INITIAL_def F_VALID_ITEM_SET_INITIAL__fp_start_def)
  apply(subgoal_tac "{\<lparr>cfg_item_lhs = cfg_initial G', cfg_item_rhs1 = [],
              cfg_item_rhs2 = prod_rhs p, cfg_item_look_ahead = []\<rparr> |
           p. p \<in> cfg_productions G' \<and>
              prod_lhs p = cfg_initial G'} = {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}")
   prefer 2
   apply(rule order_antisym)
    prefer 2
    apply(rule subsetI)
    apply(rename_tac x)(*strict*)
    apply(simp (no_asm))
    apply(simp add: F_CFG_AUGMENT_def)
    apply(rule_tac
      x="\<lparr>prod_lhs=S', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in exI)
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(simp add: F_CFG_AUGMENT_def)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(simp (no_asm))
   apply(simp (no_asm_use))
   apply(clarsimp)
   apply(erule disjE)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(thin_tac "\<forall>e \<in> cfg_productions G.
            setA (prod_rhs e)
           \<subseteq> insert (F_FRESH (cfg_nonterminals G))
                (cfg_nonterminals G) \<and>
            setB (prod_rhs e)
           \<subseteq> insert (F_FRESH (cfg_events G)) (cfg_events G)")
   apply(erule_tac
      x="p"
      in ballE)
    prefer 2
    apply(force)
   apply(subgoal_tac "prod_lhs p \<notin> cfg_nonterminals G")
    apply(rename_tac p)(*strict*)
    apply(force)
   apply(rename_tac p)(*strict*)
   apply(rule_tac
      t="prod_lhs p"
      and s="F_FRESH (cfg_nonterminals G)"
      in ssubst)
    apply(rename_tac p)(*strict*)
    apply(simp add: F_CFG_AUGMENT_def)
   apply(rename_tac p)(*strict*)
   apply(rule F_FRESH_is_fresh)
   apply(simp add: valid_cfg_def)
  apply(subgoal_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}")
   prefer 2
   apply(force)
  apply(thin_tac "{\<lparr>cfg_item_lhs = cfg_initial G', cfg_item_rhs1 = [],
        cfg_item_rhs2 = prod_rhs p, cfg_item_look_ahead = []\<rparr> |
     p. p \<in> cfg_productions G' \<and> prod_lhs p = cfg_initial G'} =
    {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [],
        cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do],
        cfg_item_look_ahead = []\<rparr>}")
  apply(thin_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k
          {\<lparr>cfg_item_lhs = cfg_initial G', cfg_item_rhs1 = [],
              cfg_item_rhs2 = prod_rhs p, cfg_item_look_ahead = []\<rparr> |
           p. p \<in> cfg_productions G' \<and>
              prod_lhs p = cfg_initial G'} ")
  apply(subgoal_tac "F_VALID_ITEM_SET_GOTO__descent__fp G' F k {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>} = {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}")
   apply(force)
  apply(thin_tac "I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}")
  apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO__descent__fp G' F k {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}"
      and s="(if F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>} = {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>} then {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>} else F_VALID_ITEM_SET_GOTO__descent__fp SSG SSF SSk (F_VALID_ITEM_SET_GOTO__descent__fp_one_1s SSG SSF SSk {\<lparr>cfg_item_lhs = S', cfg_item_rhs1 = [], cfg_item_rhs2 = [teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead = []\<rparr>}))" for SSG SSF SSk
      in ssubst)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp.psimps)
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_termination)
   apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_valid_input_def)
   apply(simp add: valid_item_def)
   apply(rule_tac
      x="\<lparr>prod_lhs=S', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in bexI)
    apply(clarsimp)
   apply(simp add: F_CFG_AUGMENT_def)
  apply(simp add: F_VALID_ITEM_SET_GOTO__descent__fp_one_1s_def F_VALID_ITEM_SET_GOTO__descent__fp_one_1_def)
  done

lemma F_LR_MACHINE_preserves_Sentential: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfgRM.Nonblockingness_branching G'
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> q = last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> Sentential G' (w @ (cfg_item_rhs2 I) @ (liftB (cfg_item_look_ahead I)))"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add:)
     apply(force)
    apply(simp add:)
   apply(simp add:)
  apply(induct w arbitrary: q I rule: rev_induct)
   apply(rename_tac q I)(*strict*)
   apply(subgoal_tac "q=epda_initial M")
    apply(rename_tac q I)(*strict*)
    apply(subgoal_tac "I=\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>")
     apply(rename_tac q I)(*strict*)
     apply(rule Sentential_from_viable_prefix)
      apply(rename_tac q I)(*strict*)
      apply(force)
     apply(rename_tac q I)(*strict*)
     apply(rule_tac
      p="\<lparr>prod_lhs=S', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in F_CFG_AUGMENT__ONE_step_viable_prefix)
        apply(rename_tac q I)(*strict*)
        apply(force)
       apply(rename_tac q I)(*strict*)
       apply(simp add: F_CFG_AUGMENT_def)
      apply(rename_tac q I)(*strict*)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(rename_tac q I)(*strict*)
     apply(clarsimp)
    apply(rename_tac q I)(*strict*)
    apply(rule F_LR_MACHINE_Single_Initial_Item)
             apply(rename_tac q I)(*strict*)
             apply(force)
            apply(rename_tac q I)(*strict*)
            apply(force)
           apply(rename_tac q I)(*strict*)
           apply(force)
          apply(rename_tac q I)(*strict*)
          apply(force)
         apply(force)
        apply(rename_tac q I)(*strict*)
        apply(force)
       apply(rename_tac q I)(*strict*)
       apply(force)
      apply(rename_tac q I)(*strict*)
      apply(force)
     apply(rename_tac q I)(*strict*)
     apply(force)
    apply(rename_tac q I)(*strict*)
    apply(force)
   apply(rename_tac q I)(*strict*)
   apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
    apply(rename_tac q I)(*strict*)
    apply(force)
   apply(rename_tac q I)(*strict*)
   apply(rule_tac
      w="[]"
      and q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac q I)(*strict*)
        apply(force)
       apply(rename_tac q I)(*strict*)
       apply(force)
      apply(rename_tac q I)(*strict*)
      apply(force)
     apply(rename_tac q I)(*strict*)
     apply(simp add:  valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac q I)(*strict*)
    apply(force)
   apply(rename_tac q I)(*strict*)
   apply(force)
  apply(rename_tac x xs q I)(*strict*)
  apply(subgoal_tac "q=valid_item_set G' k (xs@[x])")
   apply(rename_tac x xs q I)(*strict*)
   prefer 2
   apply(rule_tac
      t="valid_item_set G' k (xs @ [x])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (xs @ [x]))"
      in ssubst)
    apply(rename_tac x xs q I)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
           apply(rename_tac x xs q I)(*strict*)
           apply(force)
          apply(rename_tac x xs q I)(*strict*)
          apply(force)
         apply(force)
        apply(rename_tac x xs q I)(*strict*)
        apply(force)
       apply(rename_tac x xs q I)(*strict*)
       apply(force)
      apply(rename_tac x xs q I)(*strict*)
      apply(rule two_elements_construct_domain_setA)
      apply(simp add: F_LR_MACHINE_def)
     apply(rename_tac x xs q I)(*strict*)
     apply(rule two_elements_construct_domain_setB)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac x xs q I)(*strict*)
    apply(force)
   apply(rename_tac x xs q I)(*strict*)
   apply(force)
  apply(rename_tac x xs q I)(*strict*)
  apply(thin_tac "q = last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (xs@[x]))")
  apply(erule_tac
      x="valid_item_set G' k xs"
      in meta_allE)
  apply(subgoal_tac "q=F_VALID_ITEM_SET_GOTO G' F k x (valid_item_set G' k xs)")
   apply(rename_tac x xs q I)(*strict*)
   prefer 2
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G' F k x (valid_item_set G' k xs)"
      and s="valid_item_set G' k (xs @ [x])"
      in subst)
    apply(rename_tac x xs q I)(*strict*)
    apply(rule Lemma6__26)
       apply(rename_tac x xs q I)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac x xs q I)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac x xs q I)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac x xs q I)(*strict*)
   apply(force)
  apply(rename_tac x xs q I)(*strict*)
  apply(thin_tac "q = valid_item_set G' k (xs @ [x])")
  apply(simp (no_asm_use) add: F_VALID_ITEM_SET_GOTO_def)
  apply(subgoal_tac "\<exists>J \<in> valid_item_set G' k xs. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis x {J})")
   apply(rename_tac x xs q I)(*strict*)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_exists_origin)
       apply(rename_tac x xs q I)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac x xs q I)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs I xa)(*strict*)
     apply(rule Fact6_12__2)
      apply(rename_tac x xs I xa)(*strict*)
      apply(force)
     apply(rename_tac x xs I xa)(*strict*)
     apply(force)
    apply(rename_tac x xs q I)(*strict*)
    apply(force)
   apply(rename_tac x xs q I)(*strict*)
   apply(force)
  apply(rename_tac x xs q I)(*strict*)
  apply(erule bexE)+
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule_tac
      x="J"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(rule_tac
      t="valid_item_set G' k xs"
      and s="(if xs=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) xs))"
      in ssubst)
    apply(rename_tac x xs q I J)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND)
          apply(rename_tac x xs q I J)(*strict*)
          apply(force)
         apply(rename_tac x xs q I J)(*strict*)
         apply(force)
        apply(rename_tac x xs q I J)(*strict*)
        apply(force)
       apply(rename_tac x xs q I J)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac x xs q I J)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(simp add: F_LR_MACHINE_def)
     apply(force)
    apply(rename_tac x xs q I J)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(simp add: F_LR_MACHINE_def)
    apply(force)
   apply(rename_tac x xs q I J)(*strict*)
   apply(subgoal_tac "xs=[] \<longleftrightarrow> F_DFA_GOTO_SEQUENCE M (epda_initial M) xs = []")
    apply(rename_tac x xs q I J)(*strict*)
    apply(force)
   apply(rename_tac x xs q I J)(*strict*)
   apply(subgoal_tac "length xs = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) xs)")
    apply(rename_tac x xs q I J)(*strict*)
    prefer 2
    apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac x xs q I J)(*strict*)
         apply(force)
        apply(rename_tac x xs q I J)(*strict*)
        apply(force)
       apply(rename_tac x xs q I J)(*strict*)
       apply(force)
      apply(rename_tac x xs q I J)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac x xs q I J)(*strict*)
     apply(force)
    apply(rename_tac x xs q I J)(*strict*)
    apply(force)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(thin_tac "q = F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis x (valid_item_set G' k xs))")
  apply(thin_tac "I \<in> q")
  apply(erule conjE)+
  apply(rule GOTO_preserves_Sentential)
      apply(rename_tac x xs q I J)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac x xs q I J)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac x xs q I J)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_preserves_SententialRM: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> cfgRM.Nonblockingness_branching G'
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> set w \<subseteq> epda_events M
  \<Longrightarrow> q = last ((epda_initial M) # F_DFA_GOTO_SEQUENCE M (epda_initial M) w)
  \<Longrightarrow> I \<in> q
  \<Longrightarrow> SententialRM G' (w @ (cfg_item_rhs2 I) @ (liftB (cfg_item_look_ahead I)))"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add:)
     apply(force)
    apply(simp add:)
   apply(simp add:)
  apply(induct w arbitrary: q I rule: rev_induct)
   apply(rename_tac q I)(*strict*)
   apply(subgoal_tac "q=epda_initial M")
    apply(rename_tac q I)(*strict*)
    apply(subgoal_tac "I=\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[], cfg_item_rhs2=[teB Do, teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>")
     apply(rename_tac q I)(*strict*)
     apply(rule SententialRM_from_viable_prefix)
      apply(rename_tac q I)(*strict*)
      apply(force)
     apply(rename_tac q I)(*strict*)
     apply(rule_tac
      p="\<lparr>prod_lhs=S', prod_rhs=[teB Do, teA (cfg_initial G), teB Do]\<rparr>"
      in F_CFG_AUGMENT__ONE_step_viable_prefix)
        apply(rename_tac q I)(*strict*)
        apply(force)
       apply(rename_tac q I)(*strict*)
       apply(simp add: F_CFG_AUGMENT_def)
      apply(rename_tac q I)(*strict*)
      apply(simp add: F_CFG_AUGMENT_def)
     apply(rename_tac q I)(*strict*)
     apply(clarsimp)
    apply(rename_tac q I)(*strict*)
    apply(rule F_LR_MACHINE_Single_Initial_Item)
             apply(rename_tac q I)(*strict*)
             apply(force)
            apply(rename_tac q I)(*strict*)
            apply(force)
           apply(rename_tac q I)(*strict*)
           apply(force)
          apply(rename_tac q I)(*strict*)
          apply(force)
         apply(rename_tac q I)(*strict*)
         apply(force)
        apply(rename_tac q I)(*strict*)
        apply(force)
       apply(rename_tac q I)(*strict*)
       apply(force)
      apply(rename_tac q I)(*strict*)
      apply(force)
     apply(rename_tac q I)(*strict*)
     apply(force)
    apply(force)
   apply(rename_tac q I)(*strict*)
   apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
    apply(rename_tac q I)(*strict*)
    apply(force)
   apply(rename_tac q I)(*strict*)
   apply(rule_tac
      w="[]"
      and q="(epda_initial M)"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(rename_tac q I)(*strict*)
        apply(force)
       apply(rename_tac q I)(*strict*)
       apply(force)
      apply(rename_tac q I)(*strict*)
      apply(force)
     apply(rename_tac q I)(*strict*)
     apply(simp add:  valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rename_tac q I)(*strict*)
    apply(force)
   apply(rename_tac q I)(*strict*)
   apply(force)
  apply(rename_tac x xs q I)(*strict*)
  apply(subgoal_tac "q=valid_item_set G' k (xs@[x])")
   apply(rename_tac x xs q I)(*strict*)
   prefer 2
   apply(rule_tac
      t="valid_item_set G' k (xs @ [x])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (xs @ [x]))"
      in ssubst)
    apply(rename_tac x xs q I)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND_NotNil2)
           apply(rename_tac x xs q I)(*strict*)
           apply(force)
          apply(rename_tac x xs q I)(*strict*)
          apply(force)
         apply(rename_tac x xs q I)(*strict*)
         apply(force)
        apply(rename_tac x xs q I)(*strict*)
        apply(force)
       apply(force)
      apply(rename_tac x xs q I)(*strict*)
      apply(rule two_elements_construct_domain_setA)
      apply(simp add: F_LR_MACHINE_def)
     apply(rename_tac x xs q I)(*strict*)
     apply(rule two_elements_construct_domain_setB)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac x xs q I)(*strict*)
    apply(force)
   apply(rename_tac x xs q I)(*strict*)
   apply(force)
  apply(rename_tac x xs q I)(*strict*)
  apply(thin_tac "q = last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) (xs@[x]))")
  apply(erule_tac
      x="valid_item_set G' k xs"
      in meta_allE)
  apply(subgoal_tac "q=F_VALID_ITEM_SET_GOTO G' F k x (valid_item_set G' k xs)")
   apply(rename_tac x xs q I)(*strict*)
   prefer 2
   apply(rule_tac
      t="F_VALID_ITEM_SET_GOTO G' F k x (valid_item_set G' k xs)"
      and s="valid_item_set G' k (xs @ [x])"
      in subst)
    apply(rename_tac x xs q I)(*strict*)
    apply(rule Lemma6__26)
       apply(rename_tac x xs q I)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac x xs q I)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(simp add: F_LR_MACHINE_def)
    apply(rename_tac x xs q I)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(simp add: F_LR_MACHINE_def)
   apply(rename_tac x xs q I)(*strict*)
   apply(force)
  apply(rename_tac x xs q I)(*strict*)
  apply(thin_tac "q = valid_item_set G' k (xs @ [x])")
  apply(simp (no_asm_use) add: F_VALID_ITEM_SET_GOTO_def)
  apply(subgoal_tac "\<exists>J \<in> valid_item_set G' k xs. I \<in> F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis x {J})")
   apply(rename_tac x xs q I)(*strict*)
   prefer 2
   apply(rule F_VALID_ITEM_SET_GOTO__descent__fp_exists_origin)
       apply(rename_tac x xs q I)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac x xs q I)(*strict*)
     apply(clarsimp)
     apply(rename_tac x xs I xa)(*strict*)
     apply(rule Fact6_12__2)
      apply(rename_tac x xs I xa)(*strict*)
      apply(force)
     apply(rename_tac x xs I xa)(*strict*)
     apply(force)
    apply(rename_tac x xs q I)(*strict*)
    apply(force)
   apply(rename_tac x xs q I)(*strict*)
   apply(force)
  apply(rename_tac x xs q I)(*strict*)
  apply(erule bexE)+
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule_tac
      x="J"
      in meta_allE)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(rule_tac
      t="valid_item_set G' k xs"
      and s="(if xs=[] then (epda_initial M) else last (F_DFA_GOTO_SEQUENCE M (epda_initial M) xs))"
      in ssubst)
    apply(rename_tac x xs q I J)(*strict*)
    apply(rule F_LR_MACHINE_all_SOUND)
          apply(rename_tac x xs q I J)(*strict*)
          apply(force)
         apply(rename_tac x xs q I J)(*strict*)
         apply(force)
        apply(rename_tac x xs q I J)(*strict*)
        apply(force)
       apply(rename_tac x xs q I J)(*strict*)
       apply(force)
      apply(force)
     apply(rename_tac x xs q I J)(*strict*)
     apply(rule two_elements_construct_domain_setA)
     apply(simp add: F_LR_MACHINE_def)
     apply(force)
    apply(rename_tac x xs q I J)(*strict*)
    apply(rule two_elements_construct_domain_setB)
    apply(simp add: F_LR_MACHINE_def)
    apply(force)
   apply(rename_tac x xs q I J)(*strict*)
   apply(subgoal_tac "xs=[] \<longleftrightarrow> F_DFA_GOTO_SEQUENCE M (epda_initial M) xs = []")
    apply(rename_tac x xs q I J)(*strict*)
    apply(force)
   apply(rename_tac x xs q I J)(*strict*)
   apply(subgoal_tac "length xs = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) xs)")
    apply(rename_tac x xs q I J)(*strict*)
    prefer 2
    apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac x xs q I J)(*strict*)
         apply(force)
        apply(rename_tac x xs q I J)(*strict*)
        apply(force)
       apply(rename_tac x xs q I J)(*strict*)
       apply(force)
      apply(rename_tac x xs q I J)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac x xs q I J)(*strict*)
     apply(force)
    apply(rename_tac x xs q I J)(*strict*)
    apply(force)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(erule meta_impE)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(thin_tac "q = F_VALID_ITEM_SET_GOTO__descent__fp G' F k (F_VALID_ITEM_SET_GOTO__basis x (valid_item_set G' k xs))")
  apply(thin_tac "I \<in> q")
  apply(erule conjE)+
  apply(rule GOTO_preserves_SententialRM)
       apply(rename_tac x xs q I J)(*strict*)
       apply(force)
      apply(rename_tac x xs q I J)(*strict*)
      apply(force)
     apply(force)
    apply(rename_tac x xs q I J)(*strict*)
    prefer 3
    apply(force)
   apply(rename_tac x xs q I J)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(rule Fact6_12__2)
   apply(rename_tac x xs q I J)(*strict*)
   apply(force)
  apply(rename_tac x xs q I J)(*strict*)
  apply(force)
  done

lemma F_DFA_GOTO_SEQUENCE_append_valid_item_set: "
  valid_cfg G'
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> set (x # y) \<subseteq> two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')
  \<Longrightarrow> F_DFA_GOTO_SEQUENCE M (epda_initial M) (butlast (x # y)) @ [valid_item_set G' k (x # y)] = F_DFA_GOTO_SEQUENCE M (epda_initial M) (x # y)"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add:)
     apply(force)
    apply(simp add:)
   apply(simp add:)
  apply(rule_tac
      t="valid_item_set G' k (x#y)"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) (x#y))"
      in ssubst)
   apply(rule_tac
      w="x#y"
      and M="M"
      and G="G'"
      in F_LR_MACHINE_all_SOUND_NotNil)
          apply(force)
         apply(simp add:)
        apply(force)
       apply(force)
      apply(force)
     apply(rule two_elements_construct_domain_setA)
     apply(force)
    apply(rule two_elements_construct_domain_setB)
    apply(force)
   apply(force)
  apply(subgoal_tac "\<exists>y' x'. x#y=y'@[x']")
   prefer 2
   apply(rule NonEmptyListHasTailElem)
   apply(force)
  apply(erule exE)+
  apply(rename_tac y' x')(*strict*)
  apply(rule_tac
      t="butlast (x#y)"
      and s="y'"
      in ssubst)
   apply(rename_tac y' x')(*strict*)
   apply(force)
  apply(rename_tac y' x')(*strict*)
  apply(rule_tac
      t="x#y"
      and s="y'@[x']"
      in ssubst)
   apply(rename_tac y' x')(*strict*)
   apply(force)
  apply(rename_tac y' x')(*strict*)
  apply(rule F_DFA_GOTO_SEQUENCE_butlast_last)
      apply(rename_tac y' x')(*strict*)
      apply(force)
     apply(rename_tac y' x')(*strict*)
     apply(force)
    apply(rename_tac y' x')(*strict*)
    apply(force)
   apply(rename_tac y' x')(*strict*)
   apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
    apply(rename_tac y' x')(*strict*)
    apply(simp add:  F_LR_MACHINE_def)
   apply(rename_tac y' x')(*strict*)
   apply(force)
  apply(rename_tac y' x')(*strict*)
  apply(rule_tac
      t="epda_events M"
      and s="two_elements_construct_domain (cfg_nonterminals G') (cfg_events G')"
      in ssubst)
   apply(rename_tac y' x')(*strict*)
   apply(simp add:  F_LR_MACHINE_def)
  apply(rename_tac y' x')(*strict*)
  apply(force)
  done

lemma F_LR_MACHINE_DFAGTOTO_differs2_prime: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> x \<noteq> y
  \<Longrightarrow> \<exists>v. x @ v = [teB Do, teA (cfg_initial G), teB Do]
  \<Longrightarrow> \<exists>v. y @ v = [teB Do, teA (cfg_initial G), teB Do]
  \<Longrightarrow> x \<noteq> []
  \<Longrightarrow> y \<noteq> []
  \<Longrightarrow> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) y) \<noteq> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) x)"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add:)
     apply(force)
    apply(simp add:)
   apply(simp add:)
  apply(subgoal_tac "length x = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) x)")
   apply(subgoal_tac "length y = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) y)")
    apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) y)"
      and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) y)"
      in subst)
     defer
     apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) x)"
      and s="last ((epda_initial M)#F_DFA_GOTO_SEQUENCE M (epda_initial M) x)"
      in subst)
      defer
      apply(rule F_LR_MACHINE_DFAGTOTO_differs2)
                 apply(force)
                apply(force)
               apply(force)
              apply(force)
             apply(force)
            apply(force)
           apply(force)
          apply(force)
         apply(force)
        apply(force)
       apply(force)
      apply(force)
     apply(erule exE)+
     apply(rename_tac v va)(*strict*)
     apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
          apply(rename_tac v va)(*strict*)
          apply(force)
         apply(rename_tac v va)(*strict*)
         apply(force)
        apply(rename_tac v va)(*strict*)
        apply(force)
       apply(rename_tac v va)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac v va)(*strict*)
      apply(rule_tac
      B="set [teB Do, teA (cfg_initial G), teB Do]"
      in subset_trans)
       apply(rename_tac v va)(*strict*)
       apply(rule_tac
      t="[teB Do, teA (cfg_initial G), teB Do]"
      and s="y@va"
      in ssubst)
        apply(rename_tac v va)(*strict*)
        apply(force)
       apply(rename_tac v va)(*strict*)
       apply(rule set_append1)
      apply(rename_tac v va)(*strict*)
      apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def two_elements_construct_domain_def)
     apply(rename_tac v va)(*strict*)
     apply(clarsimp)
    apply(erule exE)+
    apply(rename_tac v va)(*strict*)
    apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(rename_tac v va)(*strict*)
         apply(force)
        apply(rename_tac v va)(*strict*)
        apply(force)
       apply(rename_tac v va)(*strict*)
       apply(force)
      apply(rename_tac v va)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac v va)(*strict*)
     apply(rule_tac
      B="set [teB Do, teA (cfg_initial G), teB Do]"
      in subset_trans)
      apply(rename_tac v va)(*strict*)
      apply(rule_tac
      t="[teB Do, teA (cfg_initial G), teB Do]"
      and s="x@v"
      in ssubst)
       apply(rename_tac v va)(*strict*)
       apply(force)
      apply(rename_tac v va)(*strict*)
      apply(rule set_append1)
     apply(rename_tac v va)(*strict*)
     apply(simp add: F_LR_MACHINE_def F_CFG_AUGMENT_def valid_cfg_def two_elements_construct_domain_def)
    apply(rename_tac v va)(*strict*)
    apply(clarsimp)
   apply(rule last_ConsR)
   apply(force)
  apply(rule last_ConsR)
  apply(force)
  done

lemma AF_LR_PARSER_final_sequence_contains_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_first_compatible F k
  \<Longrightarrow> Do = F_FRESH (cfg_events G)
  \<Longrightarrow> S' = F_FRESH (cfg_nonterminals G)
  \<Longrightarrow> G' = F_CFG_AUGMENT G S' Do
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> valid_dfa M
  \<Longrightarrow> some_step_from_every_configuration M
  \<Longrightarrow> M = F_LR_MACHINE G' F k
  \<Longrightarrow> teA (cfg_initial G) \<in> epda_events M
  \<Longrightarrow> set (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<subseteq> epda_states M - {epda_initial M, last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G), teB Do]), F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))}"
  apply(subgoal_tac "every_state_in_some_accessible_configuration M")
   prefer 2
   apply(rule F_LR_MACHINE_all_Connected)
      prefer 3
      apply(simp add:)
     apply(force)
    apply(simp add:)
   apply(simp add:)
  apply(rule_tac
      t="set (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="{last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]), last(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])}"
      in ssubst)
   apply(rule_tac
      t="set (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s=" {F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]!i| i. i<length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])} "
      in ssubst)
    apply(rule set_conv_nth)
   apply(rule_tac
      t="length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="length [teB Do, teA (cfg_initial G)]"
      in subst)
    apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rule set_take_head2)
      apply(simp add:  F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
     apply(simp (no_asm_use))
    apply(force)
   apply(subgoal_tac "{y. \<exists>i. y = F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! i \<and> i < length [teB Do, teA (cfg_initial G)]} = {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]), last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])}")
    apply(force)
   apply(rule order_antisym)
    apply(rule subsetI)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "\<exists>i. x=F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! i \<and> i < length [teB Do, teA (cfg_initial G)]")
     apply(rename_tac x)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(thin_tac "x \<in> {F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! i |i. i < length [teB Do, teA (cfg_initial G)]}")
    apply(rename_tac x)(*strict*)
    apply(erule exE)+
    apply(rename_tac x i)(*strict*)
    apply(erule conjE)+
    apply(rule_tac
      t="x"
      and s="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! i"
      in ssubst)
     apply(rename_tac x i)(*strict*)
     apply(force)
    apply(rename_tac x i)(*strict*)
    apply(case_tac i)
     apply(rename_tac x i)(*strict*)
     apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! i"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
      apply(rename_tac x i)(*strict*)
      apply(rule_tac
      t="[teB Do]"
      and s="take (Suc 0) [teB Do, teA (cfg_initial G)]"
      in subst)
       apply(rename_tac x i)(*strict*)
       apply(force)
      apply(rename_tac x i)(*strict*)
      apply(rule_tac
      t="i"
      and s="0"
      in ssubst)
       apply(rename_tac x i)(*strict*)
       apply(force)
      apply(rename_tac x i)(*strict*)
      apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE)
           apply(rename_tac x i)(*strict*)
           apply(force)
          apply(rename_tac x i)(*strict*)
          apply(force)
         apply(rename_tac x i)(*strict*)
         apply(force)
        apply(rename_tac x i)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac x i)(*strict*)
       apply(force)
      apply(rename_tac x i)(*strict*)
      apply(rule set_take_head2)
       apply(rename_tac x i)(*strict*)
       apply(simp add:  F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
      apply(rename_tac x i)(*strict*)
      apply(simp (no_asm_use))
     apply(rename_tac x i)(*strict*)
     apply(force)
    apply(rename_tac x i nat)(*strict*)
    apply(case_tac nat)
     apply(rename_tac x i nat)(*strict*)
     apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! i"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
      apply(rename_tac x i nat)(*strict*)
      apply(rule_tac
      t="i"
      and s="Suc 0"
      in ssubst)
       apply(rename_tac x i nat)(*strict*)
       apply(force)
      apply(rename_tac x i nat)(*strict*)
      apply(rule_tac
      P="\<lambda>qq. F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! Suc 0 = last (F_DFA_GOTO_SEQUENCE M (epda_initial M) qq)"
      and s="take (Suc (Suc 0)) [teB Do, teA (cfg_initial G)]"
      in ssubst)
       apply(rename_tac x i nat)(*strict*)
       apply(force)
      apply(rename_tac x i nat)(*strict*)
      apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE)
           apply(rename_tac x i nat)(*strict*)
           apply(force)
          apply(rename_tac x i nat)(*strict*)
          apply(force)
         apply(rename_tac x i nat)(*strict*)
         apply(force)
        apply(rename_tac x i nat)(*strict*)
        apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
       apply(rename_tac x i nat)(*strict*)
       apply(force)
      apply(rename_tac x i nat)(*strict*)
      apply(rule set_take_head2)
       apply(rename_tac x i nat)(*strict*)
       apply(simp add:  F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
      apply(rename_tac x i nat)(*strict*)
      apply(simp (no_asm_use))
     apply(rename_tac x i nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac x i nat nata)(*strict*)
    apply(force)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(case_tac "x=last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
    apply(rename_tac x)(*strict*)
    apply(thin_tac "x \<in> {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]), last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])}")
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      t="x"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "\<exists>i. last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) = F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! i \<and> i < length [teB Do, teA (cfg_initial G)]")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      x="Suc 0"
      in exI)
    apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! Suc 0"
      and s="last(F_DFA_GOTO_SEQUENCE M (epda_initial M) (take (Suc (Suc 0)) [teB Do, teA (cfg_initial G)]))"
      in ssubst)
     apply(rename_tac x)(*strict*)
     apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE)
          apply(rename_tac x)(*strict*)
          apply(force)
         apply(rename_tac x)(*strict*)
         apply(force)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(rename_tac x)(*strict*)
       apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
      apply(rename_tac x)(*strict*)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(rule set_take_head2)
      apply(rename_tac x)(*strict*)
      apply(simp add:  F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
     apply(rename_tac x)(*strict*)
     apply(simp (no_asm_use))
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "x=last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])")
    apply(rename_tac x)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(thin_tac "x \<noteq> last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
   apply(thin_tac "x \<in> {last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]), last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])}")
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "\<exists>i. x=F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! i \<and> i < length [teB Do, teA (cfg_initial G)]")
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      t="x"
      and s="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(force)
   apply(rename_tac x)(*strict*)
   apply(rule_tac
      x="0"
      in exI)
   apply(rule_tac
      t="F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)] ! 0"
      and s="last(F_DFA_GOTO_SEQUENCE M (epda_initial M) (take (Suc 0) [teB Do, teA (cfg_initial G)]))"
      in ssubst)
    apply(rename_tac x)(*strict*)
    apply(rule nth_last_commutes_over_F_DFA_GOTO_SEQUENCE)
         apply(rename_tac x)(*strict*)
         apply(force)
        apply(rename_tac x)(*strict*)
        apply(force)
       apply(rename_tac x)(*strict*)
       apply(force)
      apply(rename_tac x)(*strict*)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule set_take_head2)
     apply(rename_tac x)(*strict*)
     apply(simp add:  F_LR_MACHINE_def F_CFG_AUGMENT_def two_elements_construct_domain_def)
    apply(rename_tac x)(*strict*)
    apply(simp (no_asm_use))
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(subgoal_tac "length [] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [])")
   apply(subgoal_tac "length [teB Do, teA (cfg_initial G)] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])")
    apply(subgoal_tac "length [teB Do] = length (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])")
     apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) =last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]))")
      apply(subgoal_tac "last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) =last ((epda_initial M)#(F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]))")
       apply(simp (no_asm))
       apply(rule conjI)
        apply(rule_tac
      ?q0.0="epda_initial M"
      and w="[teB Do, teA (cfg_initial G)]"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
              apply(force)
             apply(force)
            apply(force)
           apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
          apply(rule set_take_head2)
           apply(simp add:  F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
          apply(force)
         apply(force)
        apply(force)
       apply(rule conjI)
        apply(rule_tac
      P="\<lambda>qq. last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) \<noteq> qq"
      and s="last(epda_initial M # (F_DFA_GOTO_SEQUENCE M (epda_initial M) []))"
      in subst)
         apply(rule last_ConsL)
         apply(force)
        apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
         apply(force)
        apply(rule_tac
      G="G"
      in F_LR_MACHINE_DFAGTOTO_differs2)
                   apply(simp add:)
                  apply(force)
                 apply(force)
                apply(force)
               apply(simp add:)
              apply(simp add:)
             apply(force)
            apply(simp add:)
           apply(force)
          apply(force)
         apply(force)
        apply(simp add:)
       apply(rule conjI)
        apply(rule_tac G="G" in F_LR_MACHINE_DFAGTOTO_differs2_prime)
                     apply(simp add:)
                    apply(force)
                   apply(force)
                  apply(force)
                 apply(simp add:)
                apply(simp add:)
               apply(force)
              apply(simp add:)
             apply(force)
            apply(simp add:)
           apply(simp add:)
          apply(force)
         apply(force)
        apply(force)
       apply(rule_tac
      t="F_DFA_GOTO M (epda_initial M) (teA (cfg_initial G))"
      and s="{}"
      in ssubst)
        apply(rule_tac
      G="G"
      in ReadInitialIsEmpty)
                 apply(simp add:)
                apply(force)
               apply(force)
              apply(force)
             apply(force)
            apply(simp add:)
           apply(simp add:)
          apply(simp add:)
         apply(simp add:)
        apply(simp add:)
       apply(rule conjI)
        apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])"
      in ssubst)
         apply(force)
        apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)])-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} \<noteq> {}")
         apply(force)
        apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do, teA (cfg_initial G)]) - {I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}"
      and s="{\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do, teA (cfg_initial G)], cfg_item_rhs2=[teB Do], cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
         apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_2)
                   apply(simp add:)
                  apply(simp add:)
                 apply(simp add:)
                apply(simp add:)
               apply(simp add:)
              apply(force)
             apply(simp add:)
            apply(simp add:)
           apply(simp add:)
          apply(simp add:)
         apply(simp add:)
        apply(force)
       apply(rule conjI)
        apply(rule_tac
      ?q0.0="epda_initial M"
      and w="[teB Do]"
      in DFA_F_DFA_GOTO_SEQUENCE_last_in_states)
              apply(force)
             apply(force)
            apply(force)
           apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
          apply(rule set_take_head2)
           apply(simp add:  F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
          apply(force)
         apply(force)
        apply(force)
       apply(rule conjI)
        apply(rule_tac
      P="\<lambda>qq. last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) \<noteq> qq"
      and s="last(epda_initial M # (F_DFA_GOTO_SEQUENCE M (epda_initial M) []))"
      in subst)
         apply(rule last_ConsL)
         apply(force)
        apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
         apply(force)
        apply(rule_tac
      G="G"
      in F_LR_MACHINE_DFAGTOTO_differs2)
                   apply(simp add:)
                  apply(force)
                 apply(force)
                apply(force)
               apply(simp add:)
              apply(simp add:)
             apply(force)
            apply(simp add:)
           apply(force)
          apply(force)
         apply(force)
        apply(simp add:)
       apply(rule conjI)
        apply(rule_tac G="G" in F_LR_MACHINE_DFAGTOTO_differs2_prime)
                     apply(simp add:)
                    apply(force)
                   apply(force)
                  apply(force)
                 apply(simp add:)
                apply(simp add:)
               apply(force)
              apply(simp add:)
             apply(force)
            apply(force)
           apply(simp add:)
          apply(simp add:)
         apply(force)
        apply(force)
       apply(rule_tac
      t="last (F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      and s="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])"
      in ssubst)
        apply(force)
       apply(subgoal_tac "last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do])-{I. (valid_item G' k I) \<and> (item_core I \<in> cfg_productions G)} \<noteq> {}")
        apply(force)
       apply(rule_tac
      t="last (epda_initial M # F_DFA_GOTO_SEQUENCE M (epda_initial M) [teB Do]) - {I. valid_item G' k I \<and> item_core I \<in> cfg_productions G}"
      and s="{\<lparr>cfg_item_lhs=S', cfg_item_rhs1=[teB Do], cfg_item_rhs2=[teA (cfg_initial G), teB Do], cfg_item_look_ahead=[]\<rparr>}"
      in ssubst)
        apply(rule_tac
      G="G"
      in F_LR_MACHINE_prefix_closureise_additionalItems_1)
                  apply(simp add:)
                 apply(simp add:)
                apply(simp add:)
               apply(simp add:)
              apply(simp add:)
             apply(simp add:)
            apply(force)
           apply(simp add:)
          apply(simp add:)
         apply(simp add:)
        apply(simp add:)
       apply(force)
      apply(rule sym)
      apply(rule last_ConsR)
      apply(force)
     apply(rule sym)
     apply(rule last_ConsR)
     apply(force)
    apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
         apply(force)
        apply(force)
       apply(force)
      apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
     apply(simp add:  F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(force)
   apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
        apply(force)
       apply(force)
      apply(force)
     apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
    apply(rule set_take_head2)
     apply(simp add:  F_LR_MACHINE_def two_elements_construct_domain_def F_CFG_AUGMENT_def)
    apply(force)
   apply(force)
  apply(rule_tac
      M="M"
      and q="epda_initial M"
      in F_DFA_GOTO_SEQUENCESound_main1)
       apply(force)
      apply(force)
     apply(force)
    apply(simp add: valid_dfa_def valid_dpda_def valid_pda_def valid_epda_def)
   apply(force)
  apply(force)
  done

end
