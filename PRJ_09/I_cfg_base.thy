section {*I\_cfg\_base*}
theory
  I_cfg_base

imports
  PRJ_09__PRE

begin

record ('nonterminal, 'event) cfg_step_label =
  prod_lhs :: "'nonterminal"
  prod_rhs :: "('nonterminal, 'event) DT_two_elements list"

record ('nonterminal, 'event) cfg =
  cfg_nonterminals :: "'nonterminal set"
  cfg_events :: "'event set"
  cfg_initial :: "'nonterminal"
  cfg_productions :: "('nonterminal, 'event) cfg_step_label set"

definition valid_cfg_step_label :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label
  \<Rightarrow> bool"
  where
    "valid_cfg_step_label G e \<equiv>
  prod_lhs e \<in> cfg_nonterminals G
  \<and> setA (prod_rhs e) \<subseteq> cfg_nonterminals G
  \<and> setB (prod_rhs e) \<subseteq> cfg_events G"
declare valid_cfg_step_label_def [simp add]

definition valid_cfg :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "valid_cfg G \<equiv>
  finite (cfg_events G)
  \<and> finite (cfg_nonterminals G)
  \<and> cfg_initial G \<in> cfg_nonterminals G
  \<and> finite (cfg_productions G)
  \<and> (\<forall>e \<in> cfg_productions G. valid_cfg_step_label G e)"

record ('nonterminal, 'event) cfg_configuration =
  cfg_conf :: "('nonterminal, 'event) DT_two_elements list"

definition cfg_configurations :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration set"
  where
    "cfg_configurations G \<equiv>
  {\<lparr>cfg_conf = c\<rparr> |c.
  setA c \<subseteq> cfg_nonterminals G
  \<and> setB c \<subseteq> cfg_events G}"

definition cfg_initial_configurations :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration set"
  where
    "cfg_initial_configurations G \<equiv>
  {\<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>}
  \<inter> cfg_configurations G"

definition cfg_marking_configuration :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_configuration set"
  where
    "cfg_marking_configuration G \<equiv>
  {c. setA (cfg_conf c) = {}}
  \<inter> cfg_configurations G"

definition cfg_marking_condition :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event)cfg_step_label, ('nonterminal, 'event)cfg_configuration)derivation
  \<Rightarrow> bool"
  where
    "cfg_marking_condition G d \<equiv>
  \<exists>i e c.
    d i = Some (pair e c)
    \<and> c \<in> cfg_marking_configuration G"

definition cfg_step_labels :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label set"
  where
    "cfg_step_labels G \<equiv>
  cfg_productions G"

definition cfg_effects :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'event list set" where
  "cfg_effects G \<equiv>
  {w. set w \<subseteq> cfg_events G}"

definition cfg_marked_effect :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event)cfg_step_label, ('nonterminal, 'event)cfg_configuration)derivation
  \<Rightarrow> 'event list set"
  where
    "cfg_marked_effect G d \<equiv>
  {w. \<exists>e c i.
      d i = Some (pair e c)
      \<and> setA (cfg_conf c) = {}
      \<and> liftB w = cfg_conf c}"

definition cfg_marked_effect_ALT :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event)cfg_step_label, ('nonterminal, 'event)cfg_configuration)derivation
  \<Rightarrow> 'event list set"
  where
    "cfg_marked_effect_ALT G d \<equiv>
  {w. \<exists>e c i.
      d i = Some (pair e c)
      \<and> liftB w = cfg_conf c}"

lemma cfg_marked_effect_ALT_vs_cfg_marked_effect: "
  cfg_marked_effect_ALT G d = cfg_marked_effect G d"
  apply(simp add: cfg_marked_effect_ALT_def cfg_marked_effect_def)
  apply(rule antisym)
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(rename_tac x e c i)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac x e c i)(*strict*)
   apply(force)
  apply(rename_tac x e c i)(*strict*)
  apply(case_tac c)
  apply(rename_tac x e c i cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x e i)(*strict*)
  apply (metis setA_liftB_empty)
  done

definition cfg_unmarked_effect :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event) cfg_step_label, ('nonterminal, 'event) cfg_configuration) derivation
  \<Rightarrow> 'event list set" where
  "cfg_unmarked_effect G d \<equiv>
  {w. \<exists>e c i.
      d i = Some (pair e c)
      \<and> (\<exists>z. liftB w @ z = cfg_conf c)}"

datatype ('nonterminal, 'event) cfg_destination =
  dest_nonterminal "'nonterminal"
  | dest_production "('nonterminal, 'event)cfg_step_label"

definition cfg_destination :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_destination set"
  where
    "cfg_destination G \<equiv>
  dest_nonterminal ` cfg_nonterminals G
  \<union> dest_production ` cfg_productions G"

definition cfg_get_destinations :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> (('nonterminal, 'event)cfg_step_label, ('nonterminal, 'event)cfg_configuration)derivation_configuration
  \<Rightarrow> ('nonterminal, 'event) cfg_destination set"
  where
    "cfg_get_destinations G der_conf \<equiv>
  case der_conf of pair e c \<Rightarrow>
    dest_nonterminal ` setA (cfg_conf c)
    \<union> (case e of None \<Rightarrow> {} | Some e' \<Rightarrow> {dest_production e'})"

definition valid_right_regular_grammar :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "valid_right_regular_grammar G \<equiv>
  valid_cfg G
  \<and> (\<forall>e \<in> cfg_productions G. \<exists>\<alpha> A.
      prod_rhs e = liftB \<alpha> @ [teA A]
      \<or> prod_rhs e = liftB \<alpha>)"

definition valid_left_regular_grammar :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "valid_left_regular_grammar G \<equiv>
  valid_cfg G
  \<and> (\<forall>e \<in> cfg_productions G. \<exists>\<alpha> A.
      prod_rhs e = [teA A] @ liftB \<alpha>
      \<or> prod_rhs e = liftB \<alpha>)"

definition cfg_marked_configuration_effect :: "
  ('nonterminal, 'event)cfg
  \<Rightarrow> ('nonterminal, 'event)cfg_configuration
  \<Rightarrow> 'event list set"
  where
    "cfg_marked_configuration_effect G c \<equiv>
  {w. cfg_conf c = liftB w}"

definition cfg_unmarked_configuration_effect :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event)cfg_configuration
  \<Rightarrow> 'event list set"
  where
    "cfg_unmarked_configuration_effect G c =
  {w. \<exists>w'. cfg_conf c = liftB w @ w'}"

definition cfg_get_history :: "
  ('nonterminal, 'event) cfg_configuration
  \<Rightarrow> 'event list"
  where
    "cfg_get_history c \<equiv>
  maxTermPrefix (cfg_conf c)"

lemma cfgBASE_inst_AX_initial_configuration_belongs: "
  (\<forall>X. cfg_initial_configurations X \<subseteq> cfg_configurations X)"
  apply(simp add: cfg_initial_configurations_def cfg_configurations_def)
  done

lemma cfgBASE_inst_AX_effect_inclusion1: "
  (\<forall>M f. cfg_marking_condition M f \<longrightarrow> cfg_marked_effect M f \<subseteq> cfg_unmarked_effect M f)"
  apply(rule allI)+
  apply(rename_tac M f)(*strict*)
  apply(simp add: cfg_marked_effect_def cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac M f x e c i)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(rule conjI)
   apply(rename_tac M f x e c i)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
  apply(rename_tac M f x e c i)(*strict*)
  apply(case_tac c)
  apply(rename_tac M f x e c i cfg_confa)(*strict*)
  apply(clarsimp)
  done

definition empty_cfg :: "
  'nonterminal
  \<Rightarrow> 'event set
  \<Rightarrow> ('nonterminal, 'event) cfg"
  where
    "empty_cfg S A \<equiv>
  \<lparr>cfg_nonterminals = {S},
    cfg_events = A,
    cfg_initial = S,
    cfg_productions = {}\<rparr>"

definition cfg_has_production :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "cfg_has_production G \<equiv>
  cfg_productions G \<noteq> {}"

definition cfg_every_nonterminal_on_some_left_hand_side :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "cfg_every_nonterminal_on_some_left_hand_side G \<equiv>
  \<forall>A \<in> cfg_nonterminals G.
  \<exists>e \<in> cfg_productions G.
  prod_lhs e = A"

definition cfg_sub :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "cfg_sub G1 G2 \<equiv>
  cfg_events G1 \<subseteq> cfg_events G2
  \<and> cfg_nonterminals G1 \<subseteq> cfg_nonterminals G2
  \<and> cfg_productions G1 \<subseteq> cfg_productions G2
  \<and> cfg_initial G1 = cfg_initial G2"

lemma cfg_initial_in_nonterms: "
  valid_cfg G
  \<Longrightarrow> cfg_initial G \<in> cfg_nonterminals G"
  apply(simp add: valid_cfg_def)
  done

lemma prod_rhs_in_nonterms: "
  valid_cfg G
  \<Longrightarrow> \<lparr>prod_lhs = a, prod_rhs = w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G"
  apply(simp add: valid_cfg_def)
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "\<lparr>prod_lhs = a, prod_rhs = w\<rparr>"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(auto)
  done

lemma prod_rhs_in_cfg_events: "
  valid_cfg G
  \<Longrightarrow> \<lparr>prod_lhs = a, prod_rhs = w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> setB w \<subseteq> cfg_events G"
  apply(simp add: valid_cfg_def)
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "\<lparr>prod_lhs = a, prod_rhs = w\<rparr>"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(auto)
  done

lemma prod_lhs_in_nonterms: "
  valid_cfg G
  \<Longrightarrow> \<lparr>prod_lhs = a, prod_rhs = w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> a \<in> cfg_nonterminals G"
  apply(simp add: valid_cfg_def)
  apply(auto)
  done

lemma cfg_sub_inherits_cfg_events: "
  cfg_sub G1 G2
  \<Longrightarrow> cfg_events G1 \<subseteq> cfg_events G2"
  apply(simp add: cfg_sub_def)
  done

lemma only_terminals_in_postfix_closure: "
  valid_cfg G
  \<Longrightarrow> e \<in> cfg_productions G
  \<Longrightarrow> teB b # w \<in> suffixes (prod_rhs e)
  \<Longrightarrow> b \<in> cfg_events G"
  apply(subgoal_tac "\<exists>x. x @ (Cons (teB b) w) = prod_rhs e")
   defer
   apply(rule suffixes_intro2_rev)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
      x = "e"
      in ballE)
   apply(rename_tac x)(*strict*)
   defer
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      A="setB (x @ teB b # w)"
      in set_mp)
   apply(rename_tac x)(*strict*)
   apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(rule setB_selects_sound1)
  done

lemma prod_rhs_in_cfg_events2: "
  valid_cfg G
  \<Longrightarrow> \<lparr>prod_lhs = a, prod_rhs = w\<rparr> \<in> cfg_productions G
  \<Longrightarrow> setB w \<subseteq> cfg_events G"
  apply(simp add: valid_cfg_def)
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x = "\<lparr>prod_lhs = a, prod_rhs = w\<rparr>"
      in ballE)
   apply(rename_tac x)(*strict*)
   apply(auto)
  done

lemma CFGprod_lhs_in_nonterms: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> x=prod_lhs p
  \<Longrightarrow> x\<in> cfg_nonterminals G"
  apply(simp add: valid_cfg_def)
  done

lemma cfg_insert_symbol: "
  valid_cfg G
  \<Longrightarrow> valid_cfg (G\<lparr>cfg_events:=cfg_events G \<union> {a}\<rparr>)"
  apply(simp add: valid_cfg_def)
  apply(auto)
  done

lemma prod_lhs_in_nonterms2: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_lhs p = x
  \<Longrightarrow> x \<in> cfg_nonterminals G"
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  done

lemma cfg_has_nonempty_two_elements_construct_domain: "
  valid_cfg G
  \<Longrightarrow> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) = {}
  \<Longrightarrow> P"
  apply(simp add: valid_cfg_def)
  apply(simp add: two_elements_construct_domain_def)
  done

lemma cfg_prod_in_two_elements_construct_domain_subset_trans: "
  valid_cfg G
  \<Longrightarrow> \<lparr>prod_lhs=x, prod_rhs=W\<rparr> \<in> cfg_productions G
  \<Longrightarrow> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<subseteq> A
  \<Longrightarrow> set W \<subseteq> A"
  apply(simp add: valid_cfg_def)
  apply(erule conjE)+
  apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
   apply(erule_tac
      x="\<lparr>prod_lhs = x, prod_rhs = W\<rparr>"
      in ballE)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfg_prod_in_two_elements_construct_domain_subset_trans2: "
  valid_cfg G
  \<Longrightarrow> \<lparr>prod_lhs=x, prod_rhs=W\<rparr> \<in> cfg_productions G
  \<Longrightarrow> two_elements_construct_domain (cfg_nonterminals G) (cfg_events G) \<subseteq> A
  \<Longrightarrow> teA x \<in> A"
  apply(subgoal_tac "set[teA x]\<subseteq> A")
   apply(force)
  apply(simp only: valid_cfg_def)
  apply(erule conjE)+
  apply(rule_tac
      B="two_elements_construct_domain (cfg_nonterminals G) (cfg_events G)"
      in subset_trans)
   apply(erule_tac
      x="\<lparr>prod_lhs = x, prod_rhs = W\<rparr>"
      in ballE)
    apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma cfg_unmarked_effect_one_position_derivation: "
  cfg_unmarked_effect M (\<lambda>n. if n = 0 then Some (pair None c) else None) = prefix_closure{maxTermPrefix (cfg_conf c)}"
  apply(rule order_antisym)
   apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(simp add: cfg_unmarked_effect_def prefix_closure_def prefix_def)
   apply(clarsimp)
   apply(rename_tac x e ca i z)(*strict*)
   apply(case_tac i)
    apply(rename_tac x e ca i z)(*strict*)
    apply(clarsimp)
    apply(rename_tac x z)(*strict*)
    prefer 2
    apply(rename_tac x e ca i z nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac x z)(*strict*)
   apply(rule_tac
      t="cfg_conf c"
      and s="liftB x @ z"
      in ssubst)
    apply(rename_tac x z)(*strict*)
    apply(force)
   apply(rename_tac x z)(*strict*)
   apply(rule_tac
      t="maxTermPrefix (liftB x @ z)"
      and s="x@maxTermPrefix z"
      in ssubst)
    apply(rename_tac x z)(*strict*)
    apply(rule maxTermPrefix_shift)
   apply(rename_tac x z)(*strict*)
   apply(force)
  apply(simp add: cfg_unmarked_effect_def prefix_closure_def prefix_def)
  apply(clarsimp)
  apply(rename_tac x ca)(*strict*)
  apply(case_tac c)
  apply(rename_tac x ca cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c cfg_conf)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. liftB w1 @ w2 = cfg_conf \<and> (case w2 of teB b#list \<Rightarrow> False | _ \<Rightarrow> True)")
   apply(rename_tac x c cfg_conf)(*strict*)
   prefer 2
   apply(rule maxSplit)
  apply(rename_tac x c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c w1 w2)(*strict*)
  apply(subgoal_tac "x@c=w1")
   apply(rename_tac x c w1 w2)(*strict*)
   prefer 2
   apply(rule_tac
      t="w1"
      and s="maxTermPrefix (liftB w1 @ w2)"
      in subst)
    apply(rename_tac x c w1 w2)(*strict*)
    apply(rule maxTermPrefix_on_maxSplit)
    apply(force)
   apply(rename_tac x c w1 w2)(*strict*)
   apply(force)
  apply(rename_tac x c w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x c w2)(*strict*)
  apply(rule_tac
      t="liftB (x @ c)"
      and s="liftB x@liftB c"
      in ssubst)
   apply(rename_tac x c w2)(*strict*)
   apply(rule liftB_commutes_over_concat)
  apply(rename_tac x c w2)(*strict*)
  apply(force)
  done

lemma cfgSTD_inst_AX_unmarked_effect_persists: "
  \<forall>M d n. cfg_unmarked_effect M (derivation_take d n) \<subseteq> cfg_unmarked_effect M d"
  apply(clarsimp)
  apply(rename_tac M d n x)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(rename_tac d n x)(*strict*)
  apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(rename_tac d n x e c i z)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac d n x e c i z)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac d n x e c i z)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(force)
   apply(rename_tac d n x e c i z)(*strict*)
   apply(force)
  apply(rename_tac d n x e c i z)(*strict*)
  apply(force)
  done

lemma cfgSTD_inst_AX_marking_can_not_be_disabled: "
  (\<forall>G d. (\<exists>n. cfg_marking_condition G (derivation_take d n)) \<longrightarrow> cfg_marking_condition G d)"
  apply(clarsimp)
  apply(rename_tac G d n)(*strict*)
  apply(simp add: cfg_marking_condition_def derivation_take_def)
  apply(clarsimp)
  apply(rename_tac G d n i e c)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac G d n i e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G d n i e c)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="i"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(force)
  done

lemma cfgSTD_inst_AX_marked_effect_persists: "
  \<forall>G d n. cfg_marked_effect G (derivation_take d n) \<subseteq> cfg_marked_effect G d"
  apply(clarsimp)
  apply(rename_tac G d n x)(*strict*)
  apply(simp add: cfg_marked_effect_def derivation_take_def)
  apply(rename_tac d n x)(*strict*)
  apply(clarsimp)
  apply(rename_tac d n x e c i)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(clarsimp)
  apply(case_tac "i\<le>n")
   apply(rename_tac d n x e c i)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d n x e c i)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      x="i"
      in exI)
  apply(force)
  done

lemma cfgLM_inst_AX_unmarked_effect_persists: "
  \<forall>M d n. cfg_unmarked_effect M (derivation_take d n) \<subseteq> cfg_unmarked_effect M d"
  apply(clarsimp)
  apply(rename_tac M d n x)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(rename_tac d n x)(*strict*)
  apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(rename_tac d n x e c i z)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac d n x e c i z)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac d n x e c i z)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(force)
   apply(rename_tac d n x e c i z)(*strict*)
   apply(force)
  apply(rename_tac d n x e c i z)(*strict*)
  apply(force)
  done

lemma cfgRM_inst_AX_unmarked_effect_persists: "
  \<forall>M d n. cfg_unmarked_effect M (derivation_take d n) \<subseteq> cfg_unmarked_effect M d"
  apply(clarsimp)
  apply(rename_tac M d n x)(*strict*)
  apply(simp add: cfg_unmarked_effect_def)
  apply(rename_tac d n x)(*strict*)
  apply(simp add: derivation_take_def)
  apply(clarsimp)
  apply(rename_tac d n x e c i z)(*strict*)
  apply(case_tac "i\<le>n")
   apply(rename_tac d n x e c i z)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="e"
      in exI)
   apply(rule_tac
      x="c"
      in exI)
   apply(rule conjI)
    apply(rename_tac d n x e c i z)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(force)
   apply(rename_tac d n x e c i z)(*strict*)
   apply(force)
  apply(rename_tac d n x e c i z)(*strict*)
  apply(force)
  done

lemma cfg_sub__trans: "
  cfg_sub G1 G2
  \<Longrightarrow> cfg_sub G2 G3
  \<Longrightarrow> cfg_sub G1 G3"
  apply(simp add: cfg_sub_def)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(force)
  apply(force)
  done

lemma CFG_prod_lhs_in_nonterms: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> prod_lhs p \<in> cfg_nonterminals G"
  apply(simp add: valid_cfg_def)
  done

lemma CFG_prod_rhs_in_two_elements_construct_domain: "
  valid_cfg G
  \<Longrightarrow> p \<in> cfg_productions G
  \<Longrightarrow> set (prod_rhs p)
          \<subseteq> two_elements_construct_domain
             (cfg_nonterminals
               G)
             (cfg_events G)"
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      A="set(prod_rhs p)"
      in set_mp)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(rule SetxBiElem_check_vs_set_two_elements_construct_domain_check)
   apply(rename_tac x)(*strict*)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(force)
  done

lemma cfg_sub_trans: "
  cfg_sub a b
  \<Longrightarrow> cfg_sub b c
  \<Longrightarrow> cfg_sub a c"
  apply(simp add: cfg_sub_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(force)
  apply(rule conjI)
   apply(force)
  apply(force)
  done

lemma cfg_sub_reflexive: "
  cfg_sub G G"
  apply(simp add: cfg_sub_def)
  done

lemma cfg_equal_by_mutual_cfg_sub: "
  cfg_sub G1 G2
  \<Longrightarrow> cfg_sub G2 G1
  \<Longrightarrow> G1 = G2"
  apply(simp add: cfg_sub_def)
  apply(force)
  done

lemma hlp3: "
  \<lparr>cfg_conf = liftB w\<rparr> \<in> cfg_configurations G
  \<Longrightarrow> i < length (liftB w)
  \<Longrightarrow> \<lparr>cfg_conf = [liftB w ! i]\<rparr> \<in> cfg_configurations G"
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(case_tac "liftB w ! i")
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      t="liftB w ! i"
      and s="teA SSa" for SSa
      in ssubst)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(clarsimp)
   apply(rule hlp2)
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(force)
  apply(rename_tac b)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      A="setB (liftB w)"
      in set_mp)
   apply(rename_tac b)(*strict*)
   apply(force)
  apply(rename_tac b)(*strict*)
  apply (metis liftB_reflects_length teB_in_setB_nth set_setBliftB)
  done

lemma cfg_initial_conf_is_conf: "
  valid_cfg G
  \<Longrightarrow> \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<in> cfg_configurations G"
  apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  done

lemma cfg_initial_conf_is_initial_conf: "
  valid_cfg G
  \<Longrightarrow> \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<in> cfg_initial_configurations G"
  apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  done

lemma cfg_sub_cfg_productions_set_mp: "
  p \<in> cfg_productions G
  \<Longrightarrow> cfg_sub G G'
  \<Longrightarrow> p \<in> cfg_productions G'"
  apply(simp add: cfg_sub_def)
  apply(force)
  done

lemma cfg_sub_cfg_configurations_set_mp: "
  c \<in> cfg_configurations G
  \<Longrightarrow> cfg_sub G G'
  \<Longrightarrow> c \<in> cfg_configurations G'"
  apply(simp add: cfg_sub_def)
  apply(clarsimp)
  apply(simp add: cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac c)(*strict*)
  apply(force)
  done

lemma foldl_hlp: "
  foldl (@) [] (map (cfg_conf \<circ> (\<lambda>x. \<lparr>cfg_conf = [x]\<rparr>)) w) = w"
  apply(induct w)
   apply(clarsimp)
  apply(rename_tac a w)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      t="foldl (@) [a] (map (\<lambda>a. [a]) w)"
      and s="[a]@foldl (@) [] (map (\<lambda>a. [a]) w)"
      in ssubst)
   apply(rename_tac a w)(*strict*)
   apply(rule foldl_first)
  apply(rename_tac a w)(*strict*)
  apply(force)
  done

definition LR1ProdFormSimp :: "('a,'b) cfg \<Rightarrow> bool" where
  "LR1ProdFormSimp G \<equiv> (\<forall>p\<in> cfg_productions G. \<exists>b A B C.
  prod_rhs p = []
  \<or> (p=\<lparr>prod_lhs=A,prod_rhs=[teB b,teA B]\<rparr>)
  \<or> (p=\<lparr>prod_lhs=A,prod_rhs=[teA B]\<rparr>)
  \<or> (p=\<lparr>prod_lhs=A,prod_rhs=[teA B,teA C]\<rparr>)
  )"

end
