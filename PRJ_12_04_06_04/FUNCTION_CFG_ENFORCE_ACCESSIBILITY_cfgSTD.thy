section {*FUNCTION\_CFG\_ENFORCE\_ACCESSIBILITY\_cfgSTD*}
theory
  FUNCTION_CFG_ENFORCE_ACCESSIBILITY_cfgSTD

imports
  FUNCTION_CFG_ENFORCE_ACCESSIBILITY_cfgLM

begin

definition cfgSTD_SPEC_CFGEA__Productions :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg"
  where
    "cfgSTD_SPEC_CFGEA__Productions G \<equiv>
  let
    N = cfgSTD_accessible_nonterminals G
  in
    \<lparr>cfg_nonterminals = N,
    cfg_events = cfg_events G,
    cfg_initial = cfg_initial G,
    cfg_productions = {p \<in> cfg_productions G. prod_lhs p \<in> N}\<rparr>"

definition F_CFG_EASTD__fp_valid_input :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EASTD__fp_valid_input G N \<equiv>
  valid_cfg G
  \<and> N \<subseteq> cfg_nonterminals G"

definition F_CFG_EASTD__fp_invariant_01 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EASTD__fp_invariant_01 G N \<equiv>
  \<forall>p \<in> cfg_productions G.
    prod_lhs p \<in> N
    \<longrightarrow> setA (prod_rhs p) \<subseteq> F_CFG_EASTD__fp_one G N"

definition F_CFG_EASTD__fp_invariant_02 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EASTD__fp_invariant_02 G N \<equiv>
  N \<subseteq> cfg_nonterminals G
  \<and> cfg_initial G \<in> N"

definition F_CFG_EASTD__fp_invariant_03 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EASTD__fp_invariant_03 G N \<equiv>
  N \<subseteq> cfgSTD_accessible_nonterminals G"

definition F_CFG_EASTD__fp_invariants :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EASTD__fp_invariants G N \<equiv>
  F_CFG_EASTD__fp_invariant_03 G N
  \<and> F_CFG_EASTD__fp_invariant_01 G N
  \<and> F_CFG_EASTD__fp_invariant_02 G N
  \<and> F_CFG_EASTD__fp_valid_input G N"

lemma F_CFG_EASTD__fp_invariants_AT_kleene_starT: "
  F_CFG_EASTD__fp_valid_input G {cfg_initial G}
  \<Longrightarrow> F_CFG_EASTD__fp_invariants G {cfg_initial G}"
  apply(simp add: F_CFG_EASTD__fp_invariants_def F_CFG_EASTD__fp_valid_input_def)
  apply(simp add: F_CFG_EASTD__fp_invariant_03_def F_CFG_EASTD__fp_invariant_01_def F_CFG_EASTD__fp_invariant_02_def )
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: cfgSTD_accessible_nonterminals_def)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(simp add: cfgSTD.derivation_initial_def)
    apply(rule conjI)
     apply(rule cfgSTD.der1_is_derivation)
    apply(simp add: der1_def)
    apply(simp add: cfg_initial_configurations_def)
    apply(simp add: cfg_configurations_def valid_cfg_def)
   apply(simp add: get_configuration_def der1_def)
  apply(clarsimp)
  apply(rename_tac p x)(*strict*)
  apply(simp add: F_CFG_EASTD__fp_one_def)
  apply(clarsimp)
  done

lemma F_CFG_EASTD_termLem1: "
  F_CFG_EASTD__fp_one G N \<noteq> N
  \<Longrightarrow> F_CFG_EASTD__fp_valid_input G N
  \<Longrightarrow> F_CFG_EASTD__fp_valid_input G (F_CFG_EASTD__fp_one G N)"
  apply(unfold F_CFG_EASTD__fp_valid_input_def F_CFG_EASTD__fp_one_def)
  apply(auto)
  apply(rename_tac x p xa pa)(*strict*)
  apply (metis valid_cfg_def valid_cfg_step_label_def subsetD)
  done

lemma F_CFG_EASTD__fp_one_preserves_F_CFG_EASTD__fp_valid_input: "
  F_CFG_EASTD__fp_valid_input G N
  \<Longrightarrow> F_CFG_EASTD__fp_valid_input G (F_CFG_EASTD__fp_one G N)"
  apply(case_tac "F_CFG_EASTD__fp_one G N = N")
   apply(clarsimp)
  apply(rule F_CFG_EASTD_termLem1)
   apply(auto)
  done

lemma F_CFG_EASTD_sumSmaller: "
  F_CFG_EASTD__fp_one G N \<noteq> N
  \<Longrightarrow> F_CFG_EASTD__fp_valid_input G N
  \<Longrightarrow> card (cfg_nonterminals G - F_CFG_EASTD__fp_one G N) < card (cfg_nonterminals G - N)"
  apply(auto)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_CFG_EASTD__fp_valid_input_def)
   apply(subgoal_tac "N=F_CFG_EASTD__fp_one G N")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule card_seteq)
     apply(rename_tac x)(*strict*)
     apply(rule_tac
      B="cfg_nonterminals G"
      in finite_subset)
      apply(rename_tac x)(*strict*)
      apply(simp add: F_CFG_EASTD__fp_one_def)
      apply(clarsimp)
      apply(rename_tac x xa p)(*strict*)
      apply(simp add: valid_cfg_def)
      apply (metis insert_absorb insert_subset)
     apply(rename_tac x)(*strict*)
     apply (metis valid_cfg_def)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_CFG_EASTD__fp_one_def)
   apply(rename_tac x)(*strict*)
   apply(auto)
   apply(subgoal_tac "card (cfg_nonterminals G - F_CFG_EASTD__fp_one G N) \<ge> card (cfg_nonterminals G - N)")
    apply(rename_tac x)(*strict*)
    apply(auto)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "card (cfg_nonterminals G - F_CFG_EASTD__fp_one G N) = card (cfg_nonterminals G) - card (F_CFG_EASTD__fp_one G N)")
    apply(rename_tac x)(*strict*)
    apply(auto)
    apply(subgoal_tac "card (cfg_nonterminals G - N) = card (cfg_nonterminals G) - card N")
     apply(rename_tac x)(*strict*)
     apply(auto)
     apply(subgoal_tac "card (cfg_nonterminals G) - card (F_CFG_EASTD__fp_one G N) \<ge> card (cfg_nonterminals G) - card N")
      apply(rename_tac x)(*strict*)
      apply(auto)
     apply(rename_tac x)(*strict*)
     apply(rule_tac
      a="card (cfg_nonterminals G)"
      in XXXsmaller)
       apply(rename_tac x)(*strict*)
       apply(rule_tac
      B="cfg_nonterminals G"
      in card_mono)
        apply(rename_tac x)(*strict*)
        apply(simp add: valid_cfg_def)
       apply(rename_tac x)(*strict*)
       apply(simp)
      apply(rename_tac x)(*strict*)
      apply(rule card_mono)
       apply(rename_tac x)(*strict*)
       apply(simp add: valid_cfg_def)
      apply(rename_tac x)(*strict*)
      apply(simp add: F_CFG_EASTD__fp_one_def)
      apply(clarsimp)
      apply(rename_tac x xa p)(*strict*)
      apply(simp add: valid_cfg_def)
      apply(clarsimp)
      apply(erule_tac
      x="p"
      in ballE)
       apply(rename_tac x xa p)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac x xa p)(*strict*)
      apply(clarsimp)
      apply(force)
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule card_Diff_subset)
     apply(rename_tac x)(*strict*)
     apply(rule_tac
      B="cfg_nonterminals G"
      in finite_subset)
      apply(rename_tac x)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac x)(*strict*)
     apply(simp add: valid_cfg_def)
    apply(rename_tac x)(*strict*)
    apply(simp)
   apply(rename_tac x)(*strict*)
   apply(rule card_Diff_subset)
    apply(rename_tac x)(*strict*)
    apply(rule_tac
      B="cfg_nonterminals G"
      in finite_subset)
     apply(rename_tac x)(*strict*)
     apply(simp add: F_CFG_EASTD__fp_one_def)
     apply(clarsimp)
     apply(rename_tac x xa p)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(clarsimp)
     apply(erule_tac
      x="p"
      in ballE)
      apply(rename_tac x xa p)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac x xa p)(*strict*)
     apply(clarsimp)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(simp add: valid_cfg_def)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_CFG_EASTD__fp_one_def)
   apply(clarsimp)
   apply(rename_tac x xa p)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="p"
      in ballE)
    apply(rename_tac x xa p)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x xa p)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_CFG_EASTD__fp_one_def)
  done

lemma F_CFG_EASTD__fp_one_TRANSFER_TRANSFERS_SOUND: "
  F_CFG_EASTD__fp_valid_input G (F_CFG_EASTD__fp_one G N)
  \<Longrightarrow> F_CFG_EASTD__fp_valid_input G N
  \<Longrightarrow> F_CFG_EASTD__fp_invariants G N
  \<Longrightarrow> F_CFG_EASTD__fp_invariant_03 G (F_CFG_EASTD__fp_one G N)"
  apply(subgoal_tac "F_CFG_EASTD__fp_invariant_03 G N")
   defer
   apply(simp add: F_CFG_EASTD__fp_invariants_def)
  apply(subgoal_tac "valid_cfg G")
   defer
   apply(simp add: F_CFG_EASTD__fp_invariants_def F_CFG_EASTD__fp_valid_input_def)
  apply(simp add: F_CFG_EASTD__fp_invariant_03_def)
  apply(simp add: F_CFG_EASTD__fp_one_def)
  apply(simp add: cfgSTD_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x p)(*strict*)
  apply(rule conjI)
   apply(rename_tac x p)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="p"
      in ballE)
    apply(rename_tac x p)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x p)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac x p)(*strict*)
  apply(subgoal_tac "prod_lhs p \<in> {A \<in> cfg_nonterminals G. \<exists>d. cfgSTD.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> A \<in> setA (cfg_conf c))}")
   apply(rename_tac x p)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x p)(*strict*)
  apply(thin_tac "N \<subseteq> {A \<in> cfg_nonterminals G. \<exists>d. cfgSTD.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> A \<in> setA (cfg_conf c))}")
  apply(rename_tac x p)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p d n c)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac x p d n c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac x p d n c a)(*strict*)
  apply(case_tac a)
  apply(rename_tac x p d n c a option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac x p d n c option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac x p d n c e)(*strict*)
  apply(case_tac c)
  apply(rename_tac x p d n c e cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p d n e cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x p d n e w)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1@[teA (prod_lhs p)]@w2=w")
   apply(rename_tac x p d n e w)(*strict*)
   prefer 2
   apply(rule setA_decomp)
   apply(force)
  apply(rename_tac x p d n e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p d n e w1 w2)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = w1 @ teA (prod_lhs p) # w2\<rparr> p \<lparr>cfg_conf = w1 @ (prod_rhs p) @ w2\<rparr>) n"
      in exI)
  apply(rule conjI)
   apply(rename_tac x p d n e w1 w2)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
     apply(rename_tac x p d n e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac x p d n e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac x p d n e w1 w2)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac x p d n e w1 w2)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
    apply(rename_tac x p d n e w1 w2)(*strict*)
    apply(rule cfgSTD.der2_is_derivation)
    apply(simp add: cfgSTD_step_relation_def)
    apply(force)
   apply(rename_tac x p d n e w1 w2)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac x p d n e w1 w2)(*strict*)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(simp add: der2_def derivation_append_def)
  apply(simp add: setAConcat)
  done

lemma F_CFG_EASTD__fp_one_TRANSFER_TRANSFERS_EXTRA_01: "
  F_CFG_EASTD__fp_valid_input G (F_CFG_EASTD__fp_one G N)
  \<Longrightarrow> F_CFG_EASTD__fp_valid_input G N
  \<Longrightarrow> F_CFG_EASTD__fp_invariants G N
  \<Longrightarrow> F_CFG_EASTD__fp_invariant_01 G (F_CFG_EASTD__fp_one G N)"
  apply(simp add: F_CFG_EASTD__fp_invariant_01_def)
  apply(auto)
  apply(rename_tac p x)(*strict*)
  apply(simp add: F_CFG_EASTD__fp_one_def)
  apply(auto)
  done

lemma F_CFG_EASTD__fp_one_TRANSFER_TRANSFERS_EXTRA_02: "
  F_CFG_EASTD__fp_valid_input G (F_CFG_EASTD__fp_one G N)
  \<Longrightarrow> F_CFG_EASTD__fp_valid_input G N
  \<Longrightarrow> F_CFG_EASTD__fp_invariants G N
  \<Longrightarrow> F_CFG_EASTD__fp_invariant_02 G (F_CFG_EASTD__fp_one G N)"
  apply(simp add: F_CFG_EASTD__fp_invariant_02_def F_CFG_EASTD__fp_invariants_def)
  apply(auto)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_CFG_EASTD__fp_one_def)
   apply(auto)
   apply(rename_tac x p)(*strict*)
   apply(simp add: F_CFG_EASTD__fp_valid_input_def valid_cfg_def)
   apply(force)
  apply(simp add: F_CFG_EASTD__fp_one_def)
  done

lemma F_CFG_EASTD__fp_one_TRANSFER_TRANSFERS_ALL: "
  F_CFG_EASTD__fp_valid_input G (F_CFG_EASTD__fp_one G N)
  \<Longrightarrow> F_CFG_EASTD__fp_valid_input G N
  \<Longrightarrow> F_CFG_EASTD__fp_invariants G N
  \<Longrightarrow> F_CFG_EASTD__fp_invariants G (F_CFG_EASTD__fp_one G N)"
  apply(simp (no_asm) add: F_CFG_EASTD__fp_invariants_def)
  apply(rule conjI)
   apply(rule F_CFG_EASTD__fp_one_TRANSFER_TRANSFERS_SOUND)
     apply(blast)+
  apply(rule conjI)
   apply(rule F_CFG_EASTD__fp_one_TRANSFER_TRANSFERS_EXTRA_01)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_EASTD__fp_one_TRANSFER_TRANSFERS_EXTRA_02)
     apply(blast+)
  done

lemma F_CFG_EASTD__fp_Meta_Lift: "
  F_CFG_EASTD__fp_valid_input G {cfg_initial G}
  \<Longrightarrow> (\<And>G N. F_CFG_EASTD__fp_valid_input G (F_CFG_EASTD__fp_one G N)\<Longrightarrow> F_CFG_EASTD__fp_valid_input G N\<Longrightarrow> F_CFG_EASTD__fp_invariants G N\<Longrightarrow> P (F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N)) G \<Longrightarrow> P (F_CFG_EASTD__fp G N) G)
  \<Longrightarrow> (\<And>G N. F_CFG_EASTD__fp_one G N = N\<Longrightarrow> F_CFG_EASTD__fp_valid_input G N\<Longrightarrow> F_CFG_EASTD__fp_invariants G N \<Longrightarrow> P (F_CFG_EASTD__fp G N) G)
  \<Longrightarrow> P (F_CFG_EASTD__fp G {cfg_initial G}) G"
  apply(subgoal_tac "(\<lambda>G N. F_CFG_EASTD__fp_invariants G N \<longrightarrow> (P (F_CFG_EASTD__fp G N) G)) G {cfg_initial G}")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_CFG_EASTD__fp_invariants_AT_kleene_starT)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G,N). F_CFG_EASTD__fp_invariants G N \<longrightarrow> (P (F_CFG_EASTD__fp G N) G)) (G,{cfg_initial G})")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,N). F_CFG_EASTD__fp_valid_input G N"
      and RECURSIVE_COND = "\<lambda>(G,N). F_CFG_EASTD__fp_one G N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,N). (G,F_CFG_EASTD__fp_one G N)"
      and MEASURE = "\<lambda>(G,N). card (cfg_nonterminals G - N)"
      and TERM_FUN = "(\<lambda>(G,N). F_CFG_EASTD__fp_invariants G N \<longrightarrow> (P (F_CFG_EASTD__fp G N) G))"
      and y = "(G,{cfg_initial G})"
      in partial_termination_wf)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a b)(*strict*)
      apply(thin_tac "F_CFG_EASTD__fp_valid_input G {cfg_initial G}")
      apply(rename_tac G N)
      apply(rename_tac G N)(*strict*)
      apply(rule F_CFG_EASTD__fp_one_preserves_F_CFG_EASTD__fp_valid_input)
      apply(blast)
     apply(thin_tac "F_CFG_EASTD__fp_valid_input G {cfg_initial G}")
     apply(clarsimp)
     apply(rename_tac a b)(*strict*)
     apply(rename_tac G N)
     apply(rename_tac G N)(*strict*)
     apply(rule F_CFG_EASTD_sumSmaller)
      apply(rename_tac G N)(*strict*)
      apply(force)
     apply(rename_tac G N)(*strict*)
     apply(force)
    apply(force)
   prefer 2
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(erule impE)
   apply(rename_tac a b)(*strict*)
   apply(rule F_CFG_EASTD__fp_one_TRANSFER_TRANSFERS_ALL)
     apply(rename_tac a b)(*strict*)
     apply(blast)+
  done

lemma F_CFG_EASTD__fp_termination: "
  F_CFG_EASTD__fp_valid_input G N
  \<Longrightarrow> F_CFG_EASTD__fp_dom (G,N)"
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,N). F_CFG_EASTD__fp_valid_input G N"
      and RECURSIVE_COND = "\<lambda>(G,N). F_CFG_EASTD__fp_one G N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,N). (G,F_CFG_EASTD__fp_one G N)"
      and MEASURE = "\<lambda>(G,f). card (cfg_nonterminals G - f)"
      in partial_termination_wf)
      apply(clarsimp)
      apply(rename_tac a b)(*strict*)
      apply(rule F_CFG_EASTD_termLem1)
       apply(rename_tac a b)(*strict*)
       apply(blast,blast)
     defer
     apply(clarsimp)
     apply(rename_tac a b)(*strict*)
     apply(rule F_CFG_EASTD__fp.domintros,blast,blast)
    apply(clarsimp)
    apply(rename_tac a b)(*strict*)
    apply(rule F_CFG_EASTD__fp.domintros,blast,blast)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(rule F_CFG_EASTD_sumSmaller)
   apply(rename_tac a b)(*strict*)
   apply(blast)
  apply(rename_tac a b)(*strict*)
  apply(blast)
  done

lemma F_CFG_EASTD_F_CFG_EASTD__fp_invariant_02_unfold: "
  F_CFG_EASTD__fp_valid_input G {cfg_initial G}
  \<Longrightarrow> F_CFG_EASTD__fp G {cfg_initial G} \<subseteq> cfg_nonterminals G \<and> cfg_initial G \<in> F_CFG_EASTD__fp G {cfg_initial G}"
  apply(rule F_CFG_EASTD__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga N)(*strict*)
   defer
   apply(thin_tac "F_CFG_EASTD__fp_valid_input G {cfg_initial G}")
   apply(rename_tac G N)(*strict*)
   apply(subgoal_tac "F_CFG_EASTD__fp G N=N")
    apply(rename_tac G N)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_EASTD__fp_invariants_def F_CFG_EASTD__fp_invariant_02_def)
   apply(rename_tac G N)(*strict*)
   apply(rule_tac
      s="(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      and t="F_CFG_EASTD__fp G N"
      in ssubst)
    apply(rename_tac G N)(*strict*)
    apply(rule F_CFG_EASTD__fp.psimps)
    apply(rule F_CFG_EASTD__fp_termination)
    apply(blast)
   apply(rename_tac G N)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga N)(*strict*)
  apply(thin_tac "F_CFG_EASTD__fp_valid_input G {cfg_initial G}")
  apply(rename_tac G N)(*strict*)
  apply(case_tac "F_CFG_EASTD__fp_one G N = N")
   apply(rename_tac G N)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N)(*strict*)
  apply(rule_tac
      t = "F_CFG_EASTD__fp G N"
      and s = "(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      in ssubst)
   apply(rename_tac G N)(*strict*)
   apply(rule F_CFG_EASTD__fp.psimps)
   apply(rule F_CFG_EASTD__fp_termination)
   apply(blast)
  apply(rename_tac G N)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_EASTD_F_CFG_EASTD__fp_invariant_01_unfold: "
  F_CFG_EASTD__fp_valid_input G {cfg_initial G}
  \<Longrightarrow> \<forall>p \<in> cfg_productions G. prod_lhs p \<in> F_CFG_EASTD__fp G {cfg_initial G} \<longrightarrow> setA (prod_rhs p) \<subseteq> F_CFG_EASTD__fp G {cfg_initial G}"
  apply(rule F_CFG_EASTD__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga N)(*strict*)
   defer
   apply(thin_tac "F_CFG_EASTD__fp_valid_input G {cfg_initial G}")
   apply(rename_tac G N)(*strict*)
   apply(rename_tac G N)
   apply(clarsimp)
   apply(rename_tac G N p x)(*strict*)
   apply(subgoal_tac "F_CFG_EASTD__fp G N=N")
    apply(rename_tac G N p x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_EASTD__fp_invariants_def F_CFG_EASTD__fp_invariant_01_def)
    apply(rule_tac
      s="(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      and t="F_CFG_EASTD__fp G N"
      in ssubst)
     apply(rename_tac G N p x)(*strict*)
     apply(rule F_CFG_EASTD__fp.psimps)
     apply(rule F_CFG_EASTD__fp_termination)
     apply(blast)
    apply(rename_tac G N p x)(*strict*)
    apply(clarsimp)
    apply(rename_tac G N p x)(*strict*)
    apply(force)
   apply(rename_tac G N p x)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x = N"
      and t = "F_CFG_EASTD__fp G N"
      and s = "(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      in ssubst)
    apply(rename_tac G N p x)(*strict*)
    apply(rule F_CFG_EASTD__fp.psimps)
    apply(rule F_CFG_EASTD__fp_termination)
    apply(blast)
   apply(rename_tac G N p x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga N)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga N p x)(*strict*)
  apply(thin_tac "F_CFG_EASTD__fp_valid_input G {cfg_initial G}")
  apply(rename_tac G N p x)(*strict*)
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac G N p x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G N p x)(*strict*)
  apply(erule impE)
   apply(rename_tac G N p x)(*strict*)
   apply(rule_tac
      t = "F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N)"
      and s = "F_CFG_EASTD__fp G N"
      in ssubst)
    apply(rename_tac G N p x)(*strict*)
    apply(rule sym)
    apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N)"
      and t = "F_CFG_EASTD__fp G N"
      and s = "(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      in ssubst)
     apply(rename_tac G N p x)(*strict*)
     apply(rule F_CFG_EASTD__fp.psimps)
     apply(rule F_CFG_EASTD__fp_termination)
     apply(blast)
    apply(rename_tac G N p x)(*strict*)
    apply(clarsimp)
    apply(rule sym)
    apply(rule_tac
      P = "\<lambda>x. x=N"
      and t = "F_CFG_EASTD__fp G N"
      and s = "(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      in ssubst)
     apply(rename_tac G N p x)(*strict*)
     apply(rule F_CFG_EASTD__fp.psimps)
     apply(rule F_CFG_EASTD__fp_termination)
     apply(blast)
    apply(rename_tac G N p x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N p x)(*strict*)
   apply(force)
  apply(rename_tac G N p x)(*strict*)
  apply(rule_tac
      A="setA (prod_rhs p)"
      in set_mp)
   apply(rename_tac G N p x)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G N p x)(*strict*)
  apply(rule_tac
      s = "F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N)"
      and t = "F_CFG_EASTD__fp G N"
      in ssubst)
   apply(rename_tac G N p x)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N)"
      and t = "F_CFG_EASTD__fp G N"
      and s = "(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      in ssubst)
    apply(rename_tac G N p x)(*strict*)
    apply(rule F_CFG_EASTD__fp.psimps)
    apply(rule F_CFG_EASTD__fp_termination)
    apply(blast)
   apply(rename_tac G N p x)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule_tac
      P = "\<lambda>x. x=N"
      and t = "F_CFG_EASTD__fp G N"
      and s = "(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      in ssubst)
    apply(rename_tac G N p x)(*strict*)
    apply(rule F_CFG_EASTD__fp.psimps)
    apply(rule F_CFG_EASTD__fp_termination)
    apply(blast)
   apply(rename_tac G N p x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N p x)(*strict*)
  apply(force)
  done

lemma F_CFG_EASTDSound0_1: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EASTD__fp G {cfg_initial G} = N
  \<Longrightarrow> cfgSTD.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> setA (cfg_conf c) \<subseteq> N"
  apply(induct n arbitrary: e c)
   apply(rename_tac e c)(*strict*)
   apply(clarsimp)
   apply(rename_tac e c x)(*strict*)
   apply(case_tac c)
   apply(rename_tac e c x cfg_confa)(*strict*)
   apply(rename_tac w)
   apply(rename_tac e c x w)(*strict*)
   apply(subgoal_tac "\<exists>w1 w2. w1@[teA x]@w2=w")
    apply(rename_tac e c x w)(*strict*)
    prefer 2
    apply(rule setA_decomp)
    apply(force)
   apply(rename_tac e c x w)(*strict*)
   apply(clarsimp)
   apply(rename_tac e x w1 w2)(*strict*)
   apply(thin_tac "x \<in> setA (w1 @ teA x # w2)")
   apply(simp add: cfgSTD.derivation_initial_def cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac x w1 w2)(*strict*)
   apply(case_tac w1)
    apply(rename_tac x w1 w2)(*strict*)
    prefer 2
    apply(rename_tac x w1 w2 a list)(*strict*)
    apply(force)
   apply(rename_tac x w1 w2)(*strict*)
   apply(case_tac w2)
    apply(rename_tac x w1 w2)(*strict*)
    prefer 2
    apply(rename_tac x w1 w2 a list)(*strict*)
    apply(force)
   apply(rename_tac x w1 w2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "F_CFG_EASTD__fp G {cfg_initial G} \<subseteq> cfg_nonterminals G \<and> cfg_initial G \<in> F_CFG_EASTD__fp G {cfg_initial G}")
    prefer 2
    apply(rule F_CFG_EASTD_F_CFG_EASTD__fp_invariant_02_unfold)
    apply(simp add: F_CFG_EASTD__fp_valid_input_def)
    apply(simp add: valid_cfg_def)
   apply(clarsimp)
  apply(rename_tac n e c)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation G c1 e2 c2")
   apply(rename_tac n e c)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc n"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac n e c)(*strict*)
     apply(rule cfgSTD.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e c)(*strict*)
    apply(force)
   apply(rename_tac n e c)(*strict*)
   apply(force)
  apply(rename_tac n e c)(*strict*)
  apply(clarsimp)
  apply(rename_tac n c x e1 e2 c1)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(erule_tac
      x="c1"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac n c x e1 e2 c1 cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac n c x e1 e2 c1 w)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1@[teA x]@w2=w")
   apply(rename_tac n c x e1 e2 c1 w)(*strict*)
   prefer 2
   apply(rule setA_decomp)
   apply(force)
  apply(rename_tac n c x e1 e2 c1 w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 e2 c1 w1 w2)(*strict*)
  apply(thin_tac "x \<in> setA (w1 @ teA x # w2)")
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n x e1 e2 c1 w1 w2 l r)(*strict*)
  apply(case_tac c1)
  apply(rename_tac n x e1 e2 c1 w1 w2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 e2 w1 w2 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac n x e1 e2 w1 w2 l r prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 w1 w2 l r prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
  apply(case_tac "x \<in> setA w")
   apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
   prefer 2
   apply(subgoal_tac "prefix w1 l \<or> prefix l w1")
    apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
    apply(erule disjE)
     apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac n x e1 w1 w2 r A w c)(*strict*)
     apply(case_tac c)
      apply(rename_tac n x e1 w1 w2 r A w c)(*strict*)
      apply(clarsimp)
      apply(rename_tac n x e1 w1 w2 r A w)(*strict*)
      apply(case_tac w)
       apply(rename_tac n x e1 w1 w2 r A w)(*strict*)
       apply(clarsimp)
       apply(rename_tac n x e1 w1 w2 A)(*strict*)
       apply(rule_tac
      A="setA (w1 @ teA A # teA x # w2)"
      in set_mp)
        apply(rename_tac n x e1 w1 w2 A)(*strict*)
        apply(force)
       apply(rename_tac n x e1 w1 w2 A)(*strict*)
       apply (metis ConsApp setAConcat UnCI elemInsetA)
      apply(rename_tac n x e1 w1 w2 r A w a list)(*strict*)
      apply(clarsimp)
     apply(rename_tac n x e1 w1 w2 r A w c a list)(*strict*)
     apply(clarsimp)
     apply(rename_tac n x e1 w1 r A w list)(*strict*)
     apply(rule_tac
      A="setA (w1 @ teA x # list @ teA A # r)"
      in set_mp)
      apply(rename_tac n x e1 w1 r A w list)(*strict*)
      apply(force)
     apply(rename_tac n x e1 w1 r A w list)(*strict*)
     apply (metis elemInsetA)
    apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
    apply(simp add: prefix_def)
    apply(clarsimp)
    apply(rename_tac n x e1 w2 l r A w c)(*strict*)
    apply(subgoal_tac "prefix c w \<or> prefix w c")
     apply(rename_tac n x e1 w2 l r A w c)(*strict*)
     apply(erule disjE)
      apply(rename_tac n x e1 w2 l r A w c)(*strict*)
      apply(simp add: prefix_def)
      apply(clarsimp)
      apply(rename_tac n x e1 w2 l r A c ca)(*strict*)
      apply(case_tac ca)
       apply(rename_tac n x e1 w2 l r A c ca)(*strict*)
       apply(clarsimp)
       apply(rename_tac n x e1 w2 l A c)(*strict*)
       apply(rule_tac
      A="setA (l @ teA A # teA x # w2)"
      in set_mp)
        apply(rename_tac n x e1 w2 l A c)(*strict*)
        apply(force)
       apply(rename_tac n x e1 w2 l A c)(*strict*)
       apply (metis ConsApp setAConcat UnCI elemInsetA)
      apply(rename_tac n x e1 w2 l r A c ca a list)(*strict*)
      apply(clarsimp)
      apply(rename_tac n x e1 l r A c list)(*strict*)
      apply (metis elemInsetA)
     apply(rename_tac n x e1 w2 l r A w c)(*strict*)
     apply(simp add: prefix_def)
     apply(clarsimp)
     apply(rename_tac n x e1 w2 l A w ca)(*strict*)
     apply(rule_tac
      A="setA (l @ teA A # ca @ teA x # w2)"
      in set_mp)
      apply(rename_tac n x e1 w2 l A w ca)(*strict*)
      apply(force)
     apply(rename_tac n x e1 w2 l A w ca)(*strict*)
     apply (metis ConsApp setAConcat UnCI elemInsetA)
    apply(rename_tac n x e1 w2 l r A w c)(*strict*)
    apply (metis mutual_prefix_prefix)
   apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
   apply (metis mutual_prefix_prefix)
  apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1@[teA x]@w2=w")
   apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
   prefer 2
   apply(rule setA_decomp)
   apply(force)
  apply(rename_tac n x e1 w1 w2 l r A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
  apply(thin_tac "x \<in> setA (w1a @ teA x # w2a)")
  apply(subgoal_tac "(\<forall>p\<in> cfg_productions G. (prod_lhs p \<in> F_CFG_EASTD__fp G {cfg_initial G}) \<longrightarrow> (setA(prod_rhs p)) \<subseteq> F_CFG_EASTD__fp G {cfg_initial G})")
   apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
   prefer 2
   apply(rule F_CFG_EASTD_F_CFG_EASTD__fp_invariant_01_unfold)
   apply(simp add: F_CFG_EASTD__fp_valid_input_def)
   apply(simp add: valid_cfg_def)
  apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
  apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w1a @ teA x # w2a\<rparr>"
      in ballE)
   apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
  apply(clarsimp)
  apply(erule impE)
   apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
   prefer 2
   apply(rule_tac
      A="setA (w1a @ teA x # w2a)"
      in set_mp)
    apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
    apply(force)
   apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
   apply (metis elemInsetA)
  apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
  apply(rule_tac
      A="setA (l @ teA A # r)"
      in set_mp)
   apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
   apply(force)
  apply(rename_tac n x e1 w1 w2 l r A w1a w2a)(*strict*)
  apply (metis elemInsetA)
  done

lemma F_CFG_EASTDSoundL1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_accessible_nonterminals G \<subseteq> F_CFG_EASTD__fp G {cfg_initial G}"
  apply(simp add: cfgSTD_accessible_nonterminals_def get_configuration_def)
  apply(auto)
  apply(rename_tac x d n c)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac x d n c)(*strict*)
   apply(force)
  apply(rename_tac x d n c a)(*strict*)
  apply(case_tac a)
  apply(rename_tac x d n c a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c option)(*strict*)
  apply(rule_tac
      A="setA (cfg_conf c)"
      in set_mp)
   apply(rename_tac x d n c option)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x d n c option)(*strict*)
  apply(rule F_CFG_EASTDSound0_1)
     apply(rename_tac x d n c option)(*strict*)
     apply(force)
    apply(rename_tac x d n c option)(*strict*)
    apply(force)
   apply(rename_tac x d n c option)(*strict*)
   apply(force)
  apply(rename_tac x d n c option)(*strict*)
  apply(force)
  done

lemma F_CFG_EASTD_F_CFG_EASTD__fp_invariant_03_unfold: "
  F_CFG_EASTD__fp_valid_input G {cfg_initial G}
  \<Longrightarrow> F_CFG_EASTD__fp G {cfg_initial G} \<subseteq> cfgSTD_accessible_nonterminals G"
  apply(rule F_CFG_EASTD__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga N)(*strict*)
   defer
   apply(thin_tac "F_CFG_EASTD__fp_valid_input G {cfg_initial G}")
   apply(rename_tac G N)(*strict*)
   apply(rename_tac G N)
   apply(clarsimp)
   apply(rename_tac G N x)(*strict*)
   apply(subgoal_tac "F_CFG_EASTD__fp G N=N")
    apply(rename_tac G N x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_EASTD__fp_invariants_def F_CFG_EASTD__fp_invariant_03_def)
    apply(rule_tac
      A="F_CFG_EASTD__fp G N"
      in set_mp)
     apply(rename_tac G N x)(*strict*)
     apply(force)
    apply(rename_tac G N x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N x)(*strict*)
   apply(rule_tac
      s="(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      and t="F_CFG_EASTD__fp G N"
      in ssubst)
    apply(rename_tac G N x)(*strict*)
    apply(rule F_CFG_EASTD__fp.psimps)
    apply(rule F_CFG_EASTD__fp_termination)
    apply(blast)
   apply(rename_tac G N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga N)(*strict*)
  apply(thin_tac "F_CFG_EASTD__fp_valid_input G {cfg_initial G}")
  apply(rename_tac G N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G N x)(*strict*)
  apply(case_tac "N = F_CFG_EASTD__fp_one G N")
   apply(rename_tac G N x)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac G N x)(*strict*)
  apply(rule_tac
      A = "F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N)"
      in set_mp)
   apply(rename_tac G N x)(*strict*)
   apply(blast)
  apply(rename_tac G N x)(*strict*)
  apply(rule_tac
      t = "F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N)"
      and s = "F_CFG_EASTD__fp G N"
      in ssubst)
   apply(rename_tac G N x)(*strict*)
   apply(rule sym)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N)"
      and t = "F_CFG_EASTD__fp G N"
      and s = "(if F_CFG_EASTD__fp_one G N = N then N else F_CFG_EASTD__fp G (F_CFG_EASTD__fp_one G N))"
      in ssubst)
    apply(rename_tac G N x)(*strict*)
    apply(rule F_CFG_EASTD__fp.psimps)
    apply(rule F_CFG_EASTD__fp_termination)
    apply(blast)
   apply(rename_tac G N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N x)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_EASTDSoundL2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_accessible_nonterminals G \<supseteq> F_CFG_EASTD__fp G {cfg_initial G}"
  apply(rule F_CFG_EASTD_F_CFG_EASTD__fp_invariant_03_unfold)
  apply(simp add: F_CFG_EASTD__fp_valid_input_def valid_cfg_def)
  done

lemma F_CFG_EASTDSoundL: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_accessible_nonterminals G = F_CFG_EASTD__fp G {cfg_initial G}"
  apply(rule order_antisym)
   apply(rule F_CFG_EASTDSoundL1)
   apply(blast)
  apply(rule F_CFG_EASTDSoundL2)
  apply(blast)
  done

theorem F_CFG_EASTD_vs_cfgSTD_SPEC_CFGEA__Productions: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EASTD G = cfgSTD_SPEC_CFGEA__Productions G"
  apply(subgoal_tac "cfgSTD_accessible_nonterminals G = F_CFG_EASTD__fp G {cfg_initial G}")
   apply(simp add: F_CFG_EASTD_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
  apply(rule F_CFG_EASTDSoundL)
  apply(force)
  done

theorem F_CFG_EASTD_preserves_CFG: "
  valid_cfg G
  \<Longrightarrow> valid_cfg (cfgSTD_SPEC_CFGEA__Productions G)"
  apply(simp (no_asm) add: valid_cfg_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
  apply(rule conjI)
   apply(simp add: valid_cfg_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
  apply(rule conjI)
   apply(simp add: valid_cfg_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
   apply(simp add: cfgSTD_accessible_nonterminals_def)
  apply(rule conjI)
   apply(simp add: cfgSTD_accessible_nonterminals_def)
   apply(simp add: valid_cfg_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(simp add: cfgSTD.derivation_initial_def)
    apply(rule conjI)
     apply(rule cfgSTD.der1_is_derivation)
    apply(simp add: der1_def)
    apply(simp add: cfg_initial_configurations_def)
    apply(simp add: cfg_configurations_def valid_cfg_def)
   apply(simp add: get_configuration_def der1_def)
  apply(rule conjI)
   apply(simp add: valid_cfg_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
  apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule conjI)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(simp add: valid_cfg_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
  apply(rename_tac e)(*strict*)
  apply(subgoal_tac "(\<forall>e\<in> cfg_productions G. prod_lhs e \<in> cfg_nonterminals G \<and> setA (prod_rhs e) \<subseteq> cfg_nonterminals G \<and> setB (prod_rhs e) \<subseteq> cfg_events G)")
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(simp add: valid_cfg_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
  apply(rename_tac e)(*strict*)
  apply(erule_tac
      x="e"
      in ballE)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac e)(*strict*)
  apply(simp add: cfgSTD_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac e x d n c)(*strict*)
  apply(rule conjI)
   apply(rename_tac e x d n c)(*strict*)
   apply(force)
  apply(rename_tac e x d n c)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac e x d n c)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac e x d n c a)(*strict*)
  apply(case_tac a)
  apply(rename_tac e x d n c a option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac e x d n c option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac ea x d n c e)(*strict*)
  apply(case_tac c)
  apply(rename_tac ea x d n c e cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea x d n e cfg_confa)(*strict*)
  apply(rename_tac w)
  apply(rename_tac ea x d n e w)(*strict*)
  apply(subgoal_tac "\<exists>w1 w2. w1@[teA (prod_lhs ea)]@w2=w")
   apply(rename_tac ea x d n e w)(*strict*)
   prefer 2
   apply(rule setA_decomp)
   apply(force)
  apply(rename_tac ea x d n e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac ea x d n e w1 w2)(*strict*)
  apply(rule_tac
      x="derivation_append d (der2 \<lparr>cfg_conf = w1 @ teA (prod_lhs ea) # w2\<rparr> ea \<lparr>cfg_conf = w1 @ (prod_rhs ea) @ w2\<rparr>) n"
      in exI)
  apply(rule conjI)
   apply(rename_tac ea x d n e w1 w2)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
     apply(rename_tac ea x d n e w1 w2)(*strict*)
     apply(force)
    apply(rename_tac ea x d n e w1 w2)(*strict*)
    apply(force)
   apply(rename_tac ea x d n e w1 w2)(*strict*)
   apply(rule cfgSTD.derivation_append_preserves_derivation)
     apply(rename_tac ea x d n e w1 w2)(*strict*)
     apply(simp add: cfgSTD.derivation_initial_def)
    apply(rename_tac ea x d n e w1 w2)(*strict*)
    apply(rule cfgSTD.der2_is_derivation)
    apply(simp add: cfgSTD_step_relation_def)
    apply(force)
   apply(rename_tac ea x d n e w1 w2)(*strict*)
   apply(clarsimp)
   apply(simp add: der2_def)
  apply(rename_tac ea x d n e w1 w2)(*strict*)
  apply(rule_tac
      x="Suc n"
      in exI)
  apply(simp add: der2_def derivation_append_def)
  apply(simp add: setAConcat)
  done

lemma cfgSTD_SPEC_CFGEA__Productions_makes_cfg_sub: "
  valid_cfg G
  \<Longrightarrow> cfg_sub (cfgSTD_SPEC_CFGEA__Productions G) G"
  apply(simp add: cfgSTD_SPEC_CFGEA__Productions_def cfg_sub_def Let_def)
  apply(rule conjI)
   apply(simp add: cfgSTD_accessible_nonterminals_def)
   apply(force)
  apply(force)
  done

lemma CFG_cfgSTD_SPEC_CFGEA__Productions_preserves_Nonblockingness_branching: "
  valid_cfg G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G
  \<Longrightarrow> cfgSTD.Nonblockingness_branching (cfgSTD_SPEC_CFGEA__Productions G)"
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(erule_tac
      x="dh"
      in allE)
  apply(subgoal_tac "cfgSTD.derivation_initial G dh")
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(rule cfg_sub_preserves_derivation_initial)
     apply(rename_tac dh n)(*strict*)
     apply(force)
    apply(rename_tac dh n)(*strict*)
    apply(force)
   apply(rename_tac dh n)(*strict*)
   apply(rule cfgSTD_SPEC_CFGEA__Productions_makes_cfg_sub)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rename_tac dh n dc x)(*strict*)
  apply(rule_tac
      x="dc"
      in exI)
  apply(clarsimp)
  apply(rule context_conjI)
   apply(rename_tac dh n dc x)(*strict*)
   apply(simp (no_asm) add: cfgSTD.derivation_def)
   apply(clarsimp)
   apply(rename_tac dh n dc x i)(*strict*)
   apply(case_tac i)
    apply(rename_tac dh n dc x i)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x)(*strict*)
    apply(simp add: cfgSTD.derivation_def derivation_append_fit_def maximum_of_domain_def)
    apply(case_tac "dc 0")
     apply(rename_tac dh n dc x)(*strict*)
     apply(clarsimp)
     apply(rename_tac dh n dc x y ya)(*strict*)
     apply(case_tac y)
     apply(rename_tac dh n dc x y ya option b)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dc x a)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x a y ya)(*strict*)
    apply(case_tac a)
    apply(rename_tac dh n dc x a y ya option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x y ya option b)(*strict*)
    apply(case_tac option)
     apply(rename_tac dh n dc x y ya option b)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dc x y ya option b a)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x y ya b a)(*strict*)
    apply(case_tac y)
    apply(rename_tac dh n dc x y ya b a option ba)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc x i nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x nat)(*strict*)
   apply(case_tac "dc (Suc nat)")
    apply(rename_tac dh n dc x nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc x nat a)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e1 e2 c1 c2. dc nat = Some (pair e1 c1) \<and> SSd (Suc SSn) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation SSG c1 e2 c2" for SSd SSn SSG)
    apply(rename_tac dh n dc x nat a)(*strict*)
    prefer 2
    apply(rule cfgSTD.step_detail_before_some_position)
      apply(rename_tac dh n dc x nat a)(*strict*)
      apply(simp add: cfgSTD.derivation_initial_def)
     apply(rename_tac dh n dc x nat a)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x nat a)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x nat a)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x nat e1 e2 c1 c2)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(simp add: cfgSTD_SPEC_CFGEA__Productions_def Let_def)
   apply(clarsimp)
   apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
   apply(simp add: cfgSTD_accessible_nonterminals_def)
   apply(rule conjI)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
    apply(simp add: valid_cfg_def)
   apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
   apply(rule_tac
      x="derivation_append dh dc n"
      in exI)
   apply(rule conjI)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
    apply(rule cfgSTD.derivation_append_preserves_derivation_initial)
      apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
      apply(force)
     apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
    apply(rule cfgSTD.derivation_append_preserves_derivation)
      apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
      apply(simp add: cfgSTD.derivation_initial_def)
     apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(case_tac "dh n")
     apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r option b)(*strict*)
    apply(case_tac "dc 0")
     apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r option b)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r option b a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r option b a optiona ba)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r option b optiona ba)(*strict*)
    apply(case_tac optiona)
     apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r option b optiona ba)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r option b optiona ba a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
   apply(rule_tac
      x="n+nat"
      in exI)
   apply(simp add: derivation_append_def get_configuration_def)
   apply(case_tac nat)
    apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x e1 e2 c1 c2 l r)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(case_tac "dh n")
     apply(rename_tac dh n dc x e1 e2 c1 c2 l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dc x e1 e2 c1 c2 l r a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac dh n dc x e1 e2 c1 c2 l r a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x e1 e2 c1 c2 l r option b)(*strict*)
    apply(case_tac "dc 0")
     apply(rename_tac dh n dc x e1 e2 c1 c2 l r option b)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dc x e1 e2 c1 c2 l r option b a)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x e1 e2 c1 c2 l r option b)(*strict*)
    apply(case_tac e1)
     apply(rename_tac dh n dc x e1 e2 c1 c2 l r option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac dh n dc x e2 c1 c2 l r option)(*strict*)
     apply (metis elemInsetA)
    apply(rename_tac dh n dc x e1 e2 c1 c2 l r option b a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc x nat e1 e2 c1 c2 l r nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x e1 e2 c1 c2 l r nata)(*strict*)
   apply (metis elemInsetA)
  apply(rename_tac dh n dc x)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac dh n dc x)(*strict*)
   apply(case_tac "dc 0")
    apply(rename_tac dh n dc x)(*strict*)
    apply(simp add: derivation_append_fit_def)
    apply(case_tac "dh n")
     apply(rename_tac dh n dc x)(*strict*)
     apply(clarsimp)
    apply(rename_tac dh n dc x a)(*strict*)
    apply(clarsimp)
    apply(case_tac a)
    apply(rename_tac dh n dc x a option b)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc x a)(*strict*)
   apply(case_tac "dc 0")
    apply(rename_tac dh n dc x a)(*strict*)
    apply(clarsimp)
   apply(rename_tac dh n dc x a aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x a)(*strict*)
   apply(case_tac a)
   apply(rename_tac dh n dc x a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x option b)(*strict*)
   apply(case_tac "option")
    apply(rename_tac dh n dc x option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac dh n dc x b)(*strict*)
    apply(rule cfgSTD.derivation_belongs)
       apply(rename_tac dh n dc x b)(*strict*)
       apply(rule F_CFG_EASTD_preserves_CFG)
       apply(force)
      apply(rename_tac dh n dc x b)(*strict*)
      apply(force)
     apply(rename_tac dh n dc x b)(*strict*)
     apply(simp add: derivation_append_fit_def)
     apply(case_tac "dh n")
      apply(rename_tac dh n dc x b)(*strict*)
      apply(clarsimp)
     apply(rename_tac dh n dc x b a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac dh n dc x b a option ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac dh n dc x b option)(*strict*)
     apply(case_tac "dc 0")
      apply(rename_tac dh n dc x b option)(*strict*)
      apply(clarsimp)
     apply(rename_tac dh n dc x b option a)(*strict*)
     apply(clarsimp)
     apply(rename_tac dh n dc x b option)(*strict*)
     apply(rule cfgSTD.derivation_initial_configurations)
       apply(rename_tac dh n dc x b option)(*strict*)
       apply(rule F_CFG_EASTD_preserves_CFG)
       apply(force)
      apply(rename_tac dh n dc x b option)(*strict*)
      apply(force)
     apply(rename_tac dh n dc x b option)(*strict*)
     apply(force)
    apply(rename_tac dh n dc x b)(*strict*)
    apply(force)
   apply(rename_tac dh n dc x option b a)(*strict*)
   apply(clarsimp)
   apply(rename_tac dh n dc x b a)(*strict*)
   apply(simp add: cfgSTD.derivation_def)
   apply(erule_tac
      x="0"
      in allE)+
   apply(clarsimp)
  apply(rename_tac dh n dc x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n dc x)(*strict*)
   apply(rule_tac
      x="x"
      in exI)
   apply(force)
  apply(rename_tac dh n dc x)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac dh n dc x i e c)(*strict*)
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
  apply(simp add: cfg_marking_configuration_def cfg_configurations_def cfgSTD_SPEC_CFGEA__Productions_def Let_def)
  apply(clarsimp)
  done

theorem F_CFG_EASTD_vs_F_CFG_EASTD_ALT: "
  F_CFG_EASTD__SpecInput G
  \<Longrightarrow> F_CFG_EASTD G = F_CFG_EASTD_ALT G"
  apply(rule_tac t="F_CFG_EASTD G" in ssubst)
   apply(rule F_CFG_EASTD_vs_cfgSTD_SPEC_CFGEA__Productions)
   apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule SOUND_FUN_CFGLMACX)
   apply(force)
  apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(clarsimp)
  apply(subgoal_tac "cfgSTD_accessible_nonterminals G =
    F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
   apply(simp add: F_CFG_EASTD_ALT_def Let_def cfgSTD_SPEC_CFGEA__Productions_def)
  apply(thin_tac "cfg_sub (F_CFG_EASTD_ALT G) G")
  apply(thin_tac "valid_cfg (F_CFG_EASTD_ALT G)")
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply(subgoal_tac "cfg_nonterminals (F_CFG_EASTD_ALT G) = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
   prefer 2
   apply(simp add: F_CFG_EASTD_ALT_def Let_def)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EASTD_ALT_idemp_cfgLM_accessible_nonterminals)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule cfgSTD_accessible_nonterminals_vs_cfgLM_accessible_nonterminals)
    apply(force)
   apply(force)
  apply(force)
  done

theorem SOUND_FUN_CFGLMACX_STD: "
  F_CFG_EASTD__SpecInput G
  \<Longrightarrow> F_CFG_EASTD__SpecOutput G (F_CFG_EASTD G)"
  apply(rule_tac t="F_CFG_EASTD G" in ssubst)
   apply(rule F_CFG_EASTD_vs_F_CFG_EASTD_ALT)
   apply(simp add: F_CFG_EASTD__SpecInput_def F_CFG_EASTD__SpecOutput_def)
  apply(metis SOUND_FUN_CFGLMACX)
  done

end

