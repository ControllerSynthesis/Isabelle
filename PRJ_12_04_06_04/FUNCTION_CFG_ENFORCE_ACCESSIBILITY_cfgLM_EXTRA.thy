section {*FUNCTION\_CFG\_ENFORCE\_ACCESSIBILITY\_cfgLM\_EXTRA*}
theory
  FUNCTION_CFG_ENFORCE_ACCESSIBILITY_cfgLM_EXTRA

imports
  PRJ_12_04_06_04__ENTRY

begin

definition cfgLM_SPEC_CFGEA__Productions :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg_step_label set"
  where
    "cfgLM_SPEC_CFGEA__Productions G \<equiv>
  {p \<in> cfg_productions G.
  prod_lhs p \<in> cfgLM_accessible_nonterminals G}"

definition F_CFG_APLM__fp_valid_input :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_APLM__fp_valid_input G E N \<equiv>
  valid_cfg G
  \<and> E = cfgSTD_Nonblockingness_nonterminals G
  \<and> N \<subseteq> cfg_nonterminals G"

definition F_CFG_APLM__fp_invariant_01 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_APLM__fp_invariant_01 G E N \<equiv>
  \<forall>p \<in> cfg_productions G.
    prod_lhs p \<in> N
    \<longrightarrow> (\<forall>w1 A w2.
        prod_rhs p = w1 @ teA A#w2
        \<longrightarrow> setA w1 \<subseteq> E
        \<longrightarrow> A \<in> F_CFG_APLM__fp_one G E N)"

definition F_CFG_APLM__fp_invariant_02 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_APLM__fp_invariant_02 G E N \<equiv>
  N \<subseteq> cfg_nonterminals G
  \<and> cfg_initial G \<in> N"

definition F_CFG_APLM__fp_invariant_03 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_APLM__fp_invariant_03 G E N \<equiv>
  N \<subseteq> cfgLM_accessible_nonterminals G"

definition F_CFG_APLM__fp_invariants :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_APLM__fp_invariants G E N \<equiv>
  F_CFG_APLM__fp_invariant_03 G E N
  \<and> F_CFG_APLM__fp_invariant_01 G E N
  \<and> F_CFG_APLM__fp_invariant_02 G E N
  \<and> F_CFG_APLM__fp_valid_input G E N"

lemma F_CFG_APLM__fp_invariants_AT_kleene_starT: "
  F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}
  \<Longrightarrow> F_CFG_APLM__fp_invariants G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
  apply(simp add: F_CFG_APLM__fp_invariants_def F_CFG_APLM__fp_valid_input_def)
  apply(simp add: F_CFG_APLM__fp_invariant_03_def F_CFG_APLM__fp_invariant_01_def F_CFG_APLM__fp_invariant_02_def )
  apply(clarsimp)
  apply(rule conjI)
   apply(simp add: cfgLM_accessible_nonterminals_def)
   apply(rule_tac
      x="der1 \<lparr>cfg_conf=[teA (cfg_initial G)]\<rparr>"
      in exI)
   apply(rule conjI)
    apply(simp add: cfgLM.derivation_initial_def)
    apply(rule conjI)
     apply(rule cfgLM.der1_is_derivation)
    apply(simp add: der1_def)
    apply(simp add: cfg_initial_configurations_def)
    apply(simp add: cfg_configurations_def valid_cfg_def)
   apply(simp add: get_configuration_def der1_def)
   apply(rule_tac
      x="[]"
      in exI)
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac p w1 A w2)(*strict*)
  apply(simp add: F_CFG_APLM__fp_one_def)
  apply(clarsimp)
  apply(force)
  done

lemma F_CFG_APLM_termLem1: "
  F_CFG_APLM__fp_one G E N \<noteq> N
  \<Longrightarrow> F_CFG_APLM__fp_valid_input G E N
  \<Longrightarrow> F_CFG_APLM__fp_valid_input G E (F_CFG_APLM__fp_one G E N)"
  apply(unfold F_CFG_APLM__fp_valid_input_def F_CFG_APLM__fp_one_def)
  apply(auto)
  apply(rename_tac x p w1 w2 xa pa w1a w2a)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac x p w1 w2 xa pa w1a w2a)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x p w1 w2 xa pa w1a w2a)(*strict*)
  apply(clarsimp)
  apply (metis elemInsetA nset_mp)
  done

lemma F_CFG_APLM__fp_one_preserves_F_CFG_APLM__fp_valid_input: "
  F_CFG_APLM__fp_valid_input G E N
  \<Longrightarrow> F_CFG_APLM__fp_valid_input G E (F_CFG_APLM__fp_one G E N)"
  apply(case_tac "F_CFG_APLM__fp_one G E N = N")
   apply(clarsimp)
  apply(rule F_CFG_APLM_termLem1)
   apply(auto)
  done

lemma F_CFG_APLM_sumSmaller: "
  F_CFG_APLM__fp_one G E N \<noteq> N
  \<Longrightarrow> F_CFG_APLM__fp_valid_input G E N
  \<Longrightarrow> card (cfg_nonterminals G - F_CFG_APLM__fp_one G E N) < card (cfg_nonterminals G - N)"
  apply(rule card_diff)
     apply(simp add: F_CFG_APLM__fp_one_def)
    apply(force)
   apply(simp add: F_CFG_APLM__fp_valid_input_def valid_cfg_def)
  apply(simp add: F_CFG_APLM__fp_valid_input_def F_CFG_APLM__fp_one_def)
  apply(clarsimp)
  apply(rename_tac x p w1 w2)(*strict*)
  apply(simp add: valid_cfg_def)
  apply(clarsimp)
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac x p w1 w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x p w1 w2)(*strict*)
  apply(clarsimp)
  apply (metis elemInsetA nset_mp)
  done

lemma F_CFG_APLM__fp_one_TRANSFER_TRANSFERS_SOUND: "
  F_CFG_APLM__fp_valid_input G E (F_CFG_APLM__fp_one G E N)
  \<Longrightarrow> F_CFG_APLM__fp_valid_input G E N
  \<Longrightarrow> F_CFG_APLM__fp_invariants G E N
  \<Longrightarrow> F_CFG_APLM__fp_invariant_03 G E (F_CFG_APLM__fp_one G E N)"
  apply(subgoal_tac "F_CFG_APLM__fp_invariant_03 G E N")
   defer
   apply(simp add: F_CFG_APLM__fp_invariants_def)
  apply(subgoal_tac "valid_cfg G")
   defer
   apply(simp add: F_CFG_APLM__fp_invariants_def F_CFG_APLM__fp_valid_input_def)
  apply(simp add: F_CFG_APLM__fp_invariant_03_def)
  apply(simp add: F_CFG_APLM__fp_one_def)
  apply(simp add: cfgLM_accessible_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x p w1 w2)(*strict*)
  apply(rule conjI)
   apply(rename_tac x p w1 w2)(*strict*)
   apply(simp add: valid_cfg_def)
   apply(clarsimp)
   apply(erule_tac
      x="p"
      in ballE)
    apply(rename_tac x p w1 w2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x p w1 w2)(*strict*)
   apply(clarsimp)
   apply (metis elemInsetA nset_mp)
  apply(rename_tac x p w1 w2)(*strict*)
  apply(subgoal_tac "prod_lhs p \<in> {A \<in> cfg_nonterminals G. \<exists>d. cfgLM.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2))}")
   apply(rename_tac x p w1 w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x p w1 w2)(*strict*)
  apply(thin_tac "N \<subseteq> {A \<in> cfg_nonterminals G. \<exists>d. cfgLM.derivation_initial G d \<and> (\<exists>n c. get_configuration (d n) = Some c \<and> (\<exists>w1 w2. cfg_conf c = liftB w1 @ teA A # w2))}")
  apply(rename_tac x p w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p w1 w2 d n c w1a w2a)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac x p w1 w2 d n c w1a w2a)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac x p w1 w2 d n c w1a w2a a)(*strict*)
  apply(case_tac a)
  apply(rename_tac x p w1 w2 d n c w1a w2a a option b)(*strict*)
  apply(simp add: get_configuration_def)
  apply(clarsimp)
  apply(rename_tac x p w1 w2 d n c w1a w2a option)(*strict*)
  apply(rename_tac e)
  apply(rename_tac x p w1 w2 d n c w1a w2a e)(*strict*)
  apply(case_tac c)
  apply(rename_tac x p w1 w2 d n c w1a w2a e cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p w1 w2 d n w1a w2a e)(*strict*)
  apply(simp add: F_CFG_APLM__fp_valid_input_def)
  apply(clarsimp)
  apply(thin_tac "{u.
        \<exists>p. p \<in> cfg_productions G \<and>
            prod_lhs p \<in> N \<and>
            (\<exists>w1. (\<exists>w2. prod_rhs p = w1 @ teA u # w2) \<and>
                  setA w1 \<subseteq> cfgSTD_Nonblockingness_nonterminals G)}
       \<subseteq> cfg_nonterminals G")
  apply(rename_tac x p w1 w2 d n w1a w2a e)(*strict*)
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
   apply(rename_tac x p w1 w2 d n w1a w2a e)(*strict*)
   prefer 2
   apply(rule canElimCombine)
    apply(rename_tac x p w1 w2 d n w1a w2a e)(*strict*)
    apply(force)
   apply(rename_tac x p w1 w2 d n w1a w2a e)(*strict*)
   apply(force)
  apply(rename_tac x p w1 w2 d n w1a w2a e)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w')(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
  apply(case_tac "da 0")
   apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
  apply(subgoal_tac "\<exists>d' e. cfgLM.derivation G d' \<and> maximum_of_domain d' na \<and> d' 0 = Some (pair None \<lparr>cfg_conf=w1\<rparr>) \<and> d' na = Some (pair e \<lparr>cfg_conf=w'\<rparr>)")
   apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
   prefer 2
   apply(rule cfg_derivation_can_be_translated_to_cfgLM_derivation)
        apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
        apply(force)
       apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
       apply(force)
      apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
     apply(force)
    apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
    apply(force)
   apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
   apply(force)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
  apply(rule_tac
      x="derivation_append (derivation_append d (der2 \<lparr>cfg_conf = liftB w1a @ teA (prod_lhs p) # w2a\<rparr> p \<lparr>cfg_conf = liftB w1a @ (prod_rhs p) @ w2a\<rparr>) n) (derivation_map d' (\<lambda>c. \<lparr>cfg_conf=liftB w1a@(cfg_conf c)@(teA x#w2)@w2a\<rparr>)) (Suc n)"
      in exI)
  apply(rule conjI)
   apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
     apply(force)
    apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation_initial)
      apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
      apply(force)
     apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
     apply(force)
    apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
      apply(rule cfgLM.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
     apply(rule cfgLM.der2_is_derivation)
     apply(simp add: cfgLM_step_relation_def)
     apply(rule_tac
      x="liftB w1a"
      in exI)
     apply(clarsimp)
     apply (metis setA_liftB)
    apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
    apply(clarsimp)
    apply(simp add: der2_def)
   apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
     apply(rule cfgLM.derivation_append_preserves_derivation)
       apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
       apply(rule cfgLM.derivation_initial_is_derivation)
       apply(force)
      apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
      apply(rule cfgLM.der2_is_derivation)
      apply(simp add: cfgLM_step_relation_def)
      apply(rule_tac
      x="liftB w1a"
      in exI)
      apply(clarsimp)
      apply (metis setA_liftB)
     apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
     apply(clarsimp)
     apply(simp add: der2_def)
    apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
    apply(rule cfgLM.derivation_map_preserves_derivation2)
     apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
     apply(force)
    apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
    apply(clarsimp)
    apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea a eb b)(*strict*)
    apply(simp add: cfgLM_step_relation_def)
    apply(clarsimp)
    apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea a eb b l r)(*strict*)
    apply(rule_tac
      x="liftB w1a@l"
      in exI)
    apply(clarsimp)
    apply(simp add: setAConcat)
    apply (metis setA_liftB)
   apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
   apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
  apply(rule_tac
      x="n+Suc 0+na"
      in exI)
  apply(clarsimp)
  apply(simp add: der2_def derivation_append_def derivation_map_def)
  apply(case_tac na)
   apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea)(*strict*)
   apply(clarsimp)
   apply(rename_tac x p w2 d n w1a w2a e da w' d')(*strict*)
   apply(rule_tac
      x="w1a@(filterB w')"
      in exI)
   apply(rule_tac
      x="w2@w2a"
      in exI)
   apply(clarsimp)
   apply (metis liftBDeConv2 liftB_commutes_over_concat)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w' na xa d' ea nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac x p w1 w2 d n w1a w2a e da w' xa d' ea nat)(*strict*)
  apply(rule_tac
      x="w1a@(filterB w')"
      in exI)
  apply(rule_tac
      x="w2@w2a"
      in exI)
  apply(clarsimp)
  apply (metis liftBDeConv2 liftB_commutes_over_concat)
  done

lemma F_CFG_APLM__fp_one_TRANSFER_TRANSFERS_EXTRA_01: "
  F_CFG_APLM__fp_valid_input G E (F_CFG_APLM__fp_one G E N)
  \<Longrightarrow> F_CFG_APLM__fp_valid_input G E N
  \<Longrightarrow> F_CFG_APLM__fp_invariants G E N
  \<Longrightarrow> F_CFG_APLM__fp_invariant_01 G E (F_CFG_APLM__fp_one G E N)"
  apply(simp add: F_CFG_APLM__fp_invariant_01_def)
  apply(clarsimp)
  apply(rename_tac p w1 A w2)(*strict*)
  apply(simp add: F_CFG_APLM__fp_one_def)
  apply(erule disjE)
   apply(rename_tac p w1 A w2)(*strict*)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(rule_tac
      x="p"
      in exI)
   apply(rename_tac p w1 A w2)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="w1"
      in exI)
   apply(clarsimp)
  apply(rename_tac p w1 A w2)(*strict*)
  apply(rule disjI2)
  apply(rule disjI2)
  apply(clarsimp)
  apply(rename_tac p w1 A w2 pa w1a w2a)(*strict*)
  apply(rule_tac
      x="p"
      in exI)
  apply(rename_tac p w1 A w2 pa w1a w2a)(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac p w1 A w2 pa w1a w2a)(*strict*)
   apply(rule disjI2)
   apply(rule_tac
      x="pa"
      in exI)
   apply(rename_tac p w1 A w2 pa w1a w2a)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      x="w1a"
      in exI)
   apply(clarsimp)
  apply(rename_tac p w1 A w2 pa w1a w2a)(*strict*)
  apply(force)
  done

lemma F_CFG_APLM__fp_one_TRANSFER_TRANSFERS_EXTRA_02: "
  F_CFG_APLM__fp_valid_input G E (F_CFG_APLM__fp_one G E N)
  \<Longrightarrow> F_CFG_APLM__fp_valid_input G E N
  \<Longrightarrow> F_CFG_APLM__fp_invariants G E N
  \<Longrightarrow> F_CFG_APLM__fp_invariant_02 G E (F_CFG_APLM__fp_one G E N)"
  apply(simp add: F_CFG_APLM__fp_invariant_02_def F_CFG_APLM__fp_invariants_def)
  apply(auto)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_CFG_APLM__fp_one_def)
   apply(auto)
   apply(rename_tac x p w1 w2)(*strict*)
   apply(simp add: F_CFG_APLM__fp_valid_input_def valid_cfg_def)
   apply (metis elemInsetA nset_mp)
  apply(simp add: F_CFG_APLM__fp_one_def)
  done

lemma F_CFG_APLM__fp_one_TRANSFER_TRANSFERS_ALL: "
  F_CFG_APLM__fp_valid_input G E (F_CFG_APLM__fp_one G E N)
  \<Longrightarrow> F_CFG_APLM__fp_valid_input G E N
  \<Longrightarrow> F_CFG_APLM__fp_invariants G E N
  \<Longrightarrow> F_CFG_APLM__fp_invariants G E (F_CFG_APLM__fp_one G E N)"
  apply(simp (no_asm) add: F_CFG_APLM__fp_invariants_def)
  apply(rule conjI)
   apply(rule F_CFG_APLM__fp_one_TRANSFER_TRANSFERS_SOUND)
     apply(blast)+
  apply(rule conjI)
   apply(rule F_CFG_APLM__fp_one_TRANSFER_TRANSFERS_EXTRA_01)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_APLM__fp_one_TRANSFER_TRANSFERS_EXTRA_02)
     apply(blast+)
  done

lemma F_CFG_APLM__fp_Meta_Lift: "
  F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}
  \<Longrightarrow> (\<And>G E N. F_CFG_APLM__fp_valid_input G E (F_CFG_APLM__fp_one G E N) \<Longrightarrow> F_CFG_APLM__fp_valid_input G E N \<Longrightarrow> F_CFG_APLM__fp_invariants G E N \<Longrightarrow> P (F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N)) E G  \<Longrightarrow> P (F_CFG_APLM__fp G E N) E G)
  \<Longrightarrow> (\<And>G E N. F_CFG_APLM__fp_one G E N = N \<Longrightarrow> F_CFG_APLM__fp_valid_input G E N \<Longrightarrow> F_CFG_APLM__fp_invariants G E N  \<Longrightarrow> P (F_CFG_APLM__fp G E N) E G)
  \<Longrightarrow> P (F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}) (cfgSTD_Nonblockingness_nonterminals G) G"
  apply(subgoal_tac "(\<lambda>G E N. F_CFG_APLM__fp_invariants G E N \<longrightarrow> (P (F_CFG_APLM__fp G E N) E G)) G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_CFG_APLM__fp_invariants_AT_kleene_starT)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G,E,N). F_CFG_APLM__fp_invariants G E N \<longrightarrow> (P (F_CFG_APLM__fp G E N) E G)) (G,(cfgSTD_Nonblockingness_nonterminals G),{cfg_initial G})")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,E,N). F_CFG_APLM__fp_valid_input G E N"
      and RECURSIVE_COND = "\<lambda>(G,E,N). F_CFG_APLM__fp_one G E N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,E,N). (G,E,F_CFG_APLM__fp_one G E N)"
      and MEASURE = "\<lambda>(G,E,N). card (cfg_nonterminals G - N)"
      and TERM_FUN = "(\<lambda>(G,E,N). F_CFG_APLM__fp_invariants G E N \<longrightarrow> (P (F_CFG_APLM__fp G E N) E G))"
      and y = "(G,(cfgSTD_Nonblockingness_nonterminals G),{cfg_initial G})"
      in partial_termination_wf)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a aa b)(*strict*)
      apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
      apply(rename_tac G E N)
      apply(rename_tac G E N)(*strict*)
      apply(rule F_CFG_APLM__fp_one_preserves_F_CFG_APLM__fp_valid_input)
      apply(blast)
     apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rename_tac G E N)
     apply(rename_tac G E N)(*strict*)
     apply(rule F_CFG_APLM_sumSmaller)
      apply(rename_tac G E N)(*strict*)
      apply(force)
     apply(rename_tac G E N)(*strict*)
     apply(force)
    apply(force)
   prefer 2
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(erule impE)
   apply(rename_tac a aa b)(*strict*)
   apply(rule F_CFG_APLM__fp_one_TRANSFER_TRANSFERS_ALL)
     apply(rename_tac a aa b)(*strict*)
     apply(blast)+
  done

lemma F_CFG_APLM__fp_termination: "
  F_CFG_APLM__fp_valid_input G E N
  \<Longrightarrow> F_CFG_APLM__fp_dom (G, E, N)"
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,E,N). F_CFG_APLM__fp_valid_input G E N"
      and RECURSIVE_COND = "\<lambda>(G,E,N). F_CFG_APLM__fp_one G E N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,E,N). (G,E,F_CFG_APLM__fp_one G E N)"
      and MEASURE = "\<lambda>(G,E,f). card (cfg_nonterminals G - f)"
      in partial_termination_wf)
      apply(clarsimp)
      apply(rename_tac a aa b)(*strict*)
      apply(rule F_CFG_APLM_termLem1)
       apply(rename_tac a aa b)(*strict*)
       apply(blast,blast)
     defer
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rule F_CFG_APLM__fp.domintros,blast,blast)
    apply(clarsimp)
    apply(rename_tac a aa b)(*strict*)
    apply(rule F_CFG_APLM__fp.domintros,blast,blast)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(rule F_CFG_APLM_sumSmaller)
   apply(rename_tac a aa b)(*strict*)
   apply(blast)
  apply(rename_tac a aa b)(*strict*)
  apply(blast)
  done

lemma F_CFG_APLM_F_CFG_APLM__fp_invariant_02_unfold: "
  F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}
  \<Longrightarrow> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G} \<subseteq> cfg_nonterminals G \<and> cfg_initial G \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
  apply(rule F_CFG_APLM__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga E N)(*strict*)
   defer
   apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
   apply(rename_tac G E N)(*strict*)
   apply(subgoal_tac "F_CFG_APLM__fp G E N=N")
    apply(rename_tac G E N)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_APLM__fp_invariants_def F_CFG_APLM__fp_invariant_02_def)
   apply(rename_tac G E N)(*strict*)
   apply(rule_tac
      s="(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      and t="F_CFG_APLM__fp G E N"
      in ssubst)
    apply(rename_tac G E N)(*strict*)
    apply(rule F_CFG_APLM__fp.psimps)
    apply(rule F_CFG_APLM__fp_termination)
    apply(blast)
   apply(rename_tac G E N)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga E N)(*strict*)
  apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(rename_tac G E N)(*strict*)
  apply(case_tac "F_CFG_APLM__fp_one G E N = N")
   apply(rename_tac G E N)(*strict*)
   apply(clarsimp)
  apply(rename_tac G E N)(*strict*)
  apply(rule_tac
      t = "F_CFG_APLM__fp G E N"
      and s = "(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      in ssubst)
   apply(rename_tac G E N)(*strict*)
   apply(rule F_CFG_APLM__fp.psimps)
   apply(rule F_CFG_APLM__fp_termination)
   apply(blast)
  apply(rename_tac G E N)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_APLM_F_CFG_APLM__fp_invariant_01_unfold: "
  F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}
  \<Longrightarrow> \<forall>p\<in> cfg_productions G. (prod_lhs p \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}) \<longrightarrow> (\<forall>w1 A w2. prod_rhs p = w1 @ teA A # w2 \<longrightarrow> setA w1 \<subseteq> (cfgSTD_Nonblockingness_nonterminals G) \<longrightarrow> A \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G})"
  apply(rule_tac
      P="\<lambda>S E G. \<forall>p\<in> cfg_productions G. prod_lhs p \<in> S \<longrightarrow> (\<forall>w1 A w2. prod_rhs p = w1 @ teA A # w2 \<longrightarrow> setA w1 \<subseteq> E \<longrightarrow> A \<in> S)"
      in F_CFG_APLM__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga E N)(*strict*)
   defer
   apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
   apply(rename_tac G E N)(*strict*)
   apply(rename_tac G E N)
   apply(clarsimp)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   apply(subgoal_tac "F_CFG_APLM__fp G E N=N")
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_APLM__fp_invariants_def F_CFG_APLM__fp_invariant_01_def)
    apply(rule_tac
      s="(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      and t="F_CFG_APLM__fp G E N"
      in ssubst)
     apply(rename_tac G E N p w1 A w2)(*strict*)
     apply(rule F_CFG_APLM__fp.psimps)
     apply(rule F_CFG_APLM__fp_termination)
     apply(blast)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(erule_tac
      x="p"
      in ballE)
     apply(rename_tac G E N p w1 A w2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(clarsimp)
    apply(erule_tac
      x="w1"
      in allE)
    apply(clarsimp)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x = N"
      and t = "F_CFG_APLM__fp G E N"
      and s = "(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      in ssubst)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(rule F_CFG_APLM__fp.psimps)
    apply(rule F_CFG_APLM__fp_termination)
    apply(blast)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga E N)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga E N p w1 A w2)(*strict*)
  apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(rename_tac G E N p w1 A w2)(*strict*)
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac G E N p w1 A w2)(*strict*)
  apply(erule impE)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   apply(rule_tac
      t = "F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N)"
      and s = "F_CFG_APLM__fp G E N"
      in ssubst)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(rule sym)
    apply(rule_tac
      P = "\<lambda>x. x = F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N)"
      and t = "F_CFG_APLM__fp G E N"
      and s = "(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      in ssubst)
     apply(rename_tac G E N p w1 A w2)(*strict*)
     apply(rule F_CFG_APLM__fp.psimps)
     apply(rule F_CFG_APLM__fp_termination)
     apply(blast)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(clarsimp)
    apply(rule sym)
    apply(rule_tac
      P = "\<lambda>x. x=N"
      and t = "F_CFG_APLM__fp G E N"
      and s = "(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      in ssubst)
     apply(rename_tac G E N p w1 A w2)(*strict*)
     apply(rule F_CFG_APLM__fp.psimps)
     apply(rule F_CFG_APLM__fp_termination)
     apply(blast)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(clarsimp)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   apply(force)
  apply(rename_tac G E N p w1 A w2)(*strict*)
  apply(erule_tac
      x="w1"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      s = "F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N)"
      and t = "F_CFG_APLM__fp G E N"
      in ssubst)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_APLM__fp G E(F_CFG_APLM__fp_one G E N)"
      and t = "F_CFG_APLM__fp G E N"
      and s = "(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      in ssubst)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(rule F_CFG_APLM__fp.psimps)
    apply(rule F_CFG_APLM__fp_termination)
    apply(blast)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   apply(clarsimp)
   apply(rule sym)
   apply(rule_tac
      P = "\<lambda>x. x=N"
      and t = "F_CFG_APLM__fp G E N"
      and s = "(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      in ssubst)
    apply(rename_tac G E N p w1 A w2)(*strict*)
    apply(rule F_CFG_APLM__fp.psimps)
    apply(rule F_CFG_APLM__fp_termination)
    apply(blast)
   apply(rename_tac G E N p w1 A w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac G E N p w1 A w2)(*strict*)
  apply(force)
  done

lemma F_CFG_APLM_apply_outside: "
  F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}
  \<Longrightarrow> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G} = F_CFG_APLM__fp_one G (cfgSTD_Nonblockingness_nonterminals G) (F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G})"
  apply(rule F_CFG_APLM__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga E N)(*strict*)
   defer
   apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
   apply(rename_tac G E N)(*strict*)
   apply(subgoal_tac "F_CFG_APLM__fp G E N=N")
    apply(rename_tac G E N)(*strict*)
    apply(clarsimp)
   apply(rename_tac G E N)(*strict*)
   apply(simp add: F_CFG_APLM__fp_invariants_def F_CFG_APLM__fp_invariant_02_def)
   apply(rule_tac
      s="(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      and t="F_CFG_APLM__fp G E N"
      in ssubst)
    apply(rename_tac G E N)(*strict*)
    apply(rule F_CFG_APLM__fp.psimps)
    apply(rule F_CFG_APLM__fp_termination)
    apply(blast)
   apply(rename_tac G E N)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga E N)(*strict*)
  apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(rename_tac G E N)(*strict*)
  apply(case_tac "F_CFG_APLM__fp_one G E N = N")
   apply(rename_tac G E N)(*strict*)
   apply(clarsimp)
  apply(rename_tac G E N)(*strict*)
  apply(rule_tac
      t = "F_CFG_APLM__fp G E N"
      and s = "(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      in ssubst)
   apply(rename_tac G E N)(*strict*)
   apply(rule F_CFG_APLM__fp.psimps)
   apply(rule F_CFG_APLM__fp_termination)
   apply(blast)
  apply(rename_tac G E N)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_APLMSound0_1: "
  valid_cfg G
  \<Longrightarrow> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G} = N
  \<Longrightarrow> cfgLM.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e c)
  \<Longrightarrow> cfg_conf c = liftB w1 @ teA x # w2
  \<Longrightarrow> x \<in> N"
  apply(induct n arbitrary: e c w1 x w2 rule: less_induct)
  apply(rename_tac x e c w1 xa w2)(*strict*)
  apply(subgoal_tac "\<exists>m\<le>x. \<exists>w1. cfg_conf(the(get_configuration(d m))) = w1 @ [teA xa] @ w2 \<and> (\<forall>k<m. \<not> (\<exists>w1. cfg_conf(the(get_configuration(d k))) = w1 @ [teA xa] @ w2))")
   apply(rename_tac x e c w1 xa w2)(*strict*)
   prefer 2
   apply(rule earlist_occurence_of_nonterminal)
      apply(rename_tac x e c w1 xa w2)(*strict*)
      apply(force)
     apply(rename_tac x e c w1 xa w2)(*strict*)
     apply(force)
    apply(rename_tac x e c w1 xa w2)(*strict*)
    apply(force)
   apply(rename_tac x e c w1 xa w2)(*strict*)
   apply(simp add: get_configuration_def)
  apply(rename_tac x e c w1 xa w2)(*strict*)
  apply(case_tac x)
   apply(rename_tac x e c w1 xa w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac e c w1 xa w2 w1a)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac w1 xa w2 w1a)(*strict*)
   apply(case_tac w1)
    apply(rename_tac w1 xa w2 w1a)(*strict*)
    apply(clarsimp)
    apply(rename_tac w1a)(*strict*)
    apply(subgoal_tac "F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G} \<subseteq> cfg_nonterminals G \<and> cfg_initial G \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
     apply(rename_tac w1a)(*strict*)
     prefer 2
     apply(rule F_CFG_APLM_F_CFG_APLM__fp_invariant_02_unfold)
     apply(simp add: F_CFG_APLM__fp_valid_input_def)
     apply(simp add: valid_cfg_def)
    apply(rename_tac w1a)(*strict*)
    apply(force)
   apply(rename_tac w1 xa w2 w1a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac x e c w1 xa w2 nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac x e c w1 xa w2 n)(*strict*)
  apply(clarsimp)
  apply(rename_tac e c w1 xa w2 n m w1a)(*strict*)
  apply(case_tac m)
   apply(rename_tac e c w1 xa w2 n m w1a)(*strict*)
   apply(clarsimp)
   apply(rename_tac e c w1 xa w2 n w1a)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def)
   apply(clarsimp)
   apply(simp add: get_configuration_def)
   apply(case_tac "d 0")
    apply(rename_tac e c w1 xa w2 n w1a)(*strict*)
    apply(clarsimp)
   apply(rename_tac e c w1 xa w2 n w1a a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac e c w1 xa w2 n w1a a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac e c w1 xa w2 n w1a b)(*strict*)
   apply(case_tac c)
   apply(rename_tac e c w1 xa w2 n w1a b cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac e w1 xa w2 n w1a b)(*strict*)
   apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac e w1 xa w2 n w1a)(*strict*)
   apply(case_tac w1a)
    apply(rename_tac e w1 xa w2 n w1a)(*strict*)
    apply(clarsimp)
    apply(rename_tac e w1 n)(*strict*)
    apply(subgoal_tac "F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G} \<subseteq> cfg_nonterminals G \<and> cfg_initial G \<in> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
     apply(rename_tac e w1 n)(*strict*)
     prefer 2
     apply(rule F_CFG_APLM_F_CFG_APLM__fp_invariant_02_unfold)
     apply(simp add: F_CFG_APLM__fp_valid_input_def)
     apply(simp add: valid_cfg_def)
    apply(rename_tac e w1 n)(*strict*)
    apply(force)
   apply(rename_tac e w1 xa w2 n w1a a list)(*strict*)
   apply(clarsimp)
  apply(rename_tac e c w1 xa w2 n m w1a nat)(*strict*)
  apply(rename_tac n)
  apply(rename_tac e c w1 xa w2 na m w1a n)(*strict*)
  apply(case_tac c)
  apply(rename_tac e c w1 xa w2 na m w1a n cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 xa w2 na w1a n)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d n = Some (pair e1 c1) \<and> d (Suc n) = Some (pair (Some e2) c2) \<and> cfgLM_step_relation G c1 e2 c2")
   apply(rename_tac e w1 xa w2 na w1a n)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc na"
      in cfgLM.step_detail_before_some_position)
     apply(rename_tac e w1 xa w2 na w1a n)(*strict*)
     apply(rule cfgLM.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac e w1 xa w2 na w1a n)(*strict*)
    apply(force)
   apply(rename_tac e w1 xa w2 na w1a n)(*strict*)
   apply(force)
  apply(rename_tac e w1 xa w2 na w1a n)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 xa w2 na w1a n e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgLM_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e w1 xa w2 na w1a n e1 e2 c1 c2 l r)(*strict*)
  apply(case_tac c2)
  apply(rename_tac e w1 xa w2 na w1a n e1 e2 c1 c2 l r cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 xa w2 na w1a n e1 e2 c1 l r)(*strict*)
  apply(case_tac e2)
  apply(rename_tac e w1 xa w2 na w1a n e1 e2 c1 l r prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac e w1 xa w2 na w1a n e1 e2 c1 l r A w)(*strict*)
  apply(simp add: get_configuration_def)
  apply(case_tac c1)
  apply(rename_tac e w1 xa w2 na w1a n e1 e2 c1 l r A w cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
  apply(erule_tac
      x="n"
      in allE)
  apply(clarsimp)
  apply(rule_tac
      t="F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
      and s="F_CFG_APLM__fp_one G (cfgSTD_Nonblockingness_nonterminals G) (F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G})"
      in ssubst)
   apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
   apply(rule F_CFG_APLM_apply_outside)
   apply(simp add: F_CFG_APLM__fp_valid_input_def)
   apply(simp add: valid_cfg_def)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
  apply(simp add: F_CFG_APLM__fp_one_def)
  apply(rule disjI2)
  apply(rule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w\<rparr>"
      in exI)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
  apply(clarsimp)
  apply(erule_tac
      x="n"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="\<lparr>cfg_conf = l @ teA A # r\<rparr>"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="filterB l"
      in meta_allE)
  apply(erule_tac
      x="A"
      in meta_allE)
  apply(erule_tac
      x="r"
      in meta_allE)
  apply(clarsimp)
  apply(erule meta_impE)
   apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
   apply (metis liftBDeConv2)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
  apply(rule conjI)
   apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
   apply(force)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
  apply(subgoal_tac "prefix (l@w) w1a \<or> prefix w1a (l@w)")
   apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
  apply(case_tac "prefix (l@w) w1a")
   apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(force)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w c)(*strict*)
  apply(case_tac c)
   apply(rename_tac e w1 xa w2 na w1a n e1 l r A w c)(*strict*)
   apply(force)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w c a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w a list)(*strict*)
  apply(thin_tac "\<forall>c. l @ w @ c \<noteq> w1a")
  apply(subgoal_tac "prefix w1a l \<or> prefix l w1a")
   apply(rename_tac e w1 xa w2 na w1a n e1 l r A w a list)(*strict*)
   prefer 2
   apply(rule mutual_prefix_prefix)
   apply(force)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w a list)(*strict*)
  apply(case_tac "prefix w1a l")
   apply(rename_tac e w1 xa w2 na w1a n e1 l r A w a list)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(rename_tac e w1 xa w2 na w1a n e1 r A w a list c)(*strict*)
   apply(case_tac c)
    apply(rename_tac e w1 xa w2 na w1a n e1 r A w a list c)(*strict*)
    apply(clarsimp)
    apply(rename_tac e w1 xa na w1a n e1 r A list)(*strict*)
    apply(rule_tac
      x="[]"
      in exI)
    apply(clarsimp)
   apply(rename_tac e w1 xa w2 na w1a n e1 r A w a list c aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac e w1 xa na w1a n e1 r A w lista)(*strict*)
   apply (metis elemInsetA emptyE)
  apply(rename_tac e w1 xa w2 na w1a n e1 l r A w a list)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac e w1 xa na n e1 l r A list c)(*strict*)
  apply(rule_tac
      x="c"
      in exI)
  apply(clarsimp)
  apply(rename_tac e w1 xa na n e1 l r A list c x)(*strict*)
  apply(thin_tac "\<forall>w1. l @ [teA A] \<noteq> w1 @ teA xa # list")
  apply(thin_tac "d n = Some (pair e1 \<lparr>cfg_conf = l @ teA A # r\<rparr>)")
  apply(subgoal_tac "\<exists>x. n+x=na")
   apply(rename_tac e w1 xa na n e1 l r A list c x)(*strict*)
   prefer 2
   apply(rule_tac
      x="na-n"
      in exI)
   apply(force)
  apply(rename_tac e w1 xa na n e1 l r A list c x)(*strict*)
  apply(clarsimp)
  apply(rename_tac e w1 xa n l r A list c x xb)(*strict*)
  apply(rule_tac
      A="setA (l@c)"
      in set_mp)
   apply(rename_tac e w1 xa n l r A list c x xb)(*strict*)
   apply(rule_tac
      e="(Some \<lparr>prod_lhs = A, prod_rhs = c @ teA xa # list\<rparr>)"
      and n="Suc n"
      and m="xb"
      in nonterminals_are_eliminable_in_untouchable_context)
      apply(rename_tac e w1 xa n l r A list c x xb)(*strict*)
      apply(force)
     apply(rename_tac e w1 xa n l r A list c x xb)(*strict*)
     apply(force)
    apply(rename_tac e w1 xa n l r A list c x xb)(*strict*)
    apply(force)
   apply(rename_tac e w1 xa n l r A list c x xb)(*strict*)
   apply(force)
  apply(rename_tac e w1 xa n l r A list c x xb)(*strict*)
  apply(simp add: setAConcat)
  done

lemma F_CFG_APLMSoundL1: "
  valid_cfg G
  \<Longrightarrow> cfgLM_accessible_nonterminals G \<subseteq> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
  apply(simp add: cfgLM_accessible_nonterminals_def get_configuration_def)
  apply(auto)
  apply(rename_tac x d n c w1 w2)(*strict*)
  apply(case_tac "d n")
   apply(rename_tac x d n c w1 w2)(*strict*)
   apply(force)
  apply(rename_tac x d n c w1 w2 a)(*strict*)
  apply(case_tac a)
  apply(rename_tac x d n c w1 w2 a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d n c w1 w2 option)(*strict*)
  apply(rule F_CFG_APLMSound0_1)
      apply(rename_tac x d n c w1 w2 option)(*strict*)
      apply(force)
     apply(rename_tac x d n c w1 w2 option)(*strict*)
     apply(force)
    apply(rename_tac x d n c w1 w2 option)(*strict*)
    apply(force)
   apply(rename_tac x d n c w1 w2 option)(*strict*)
   apply(force)
  apply(rename_tac x d n c w1 w2 option)(*strict*)
  apply(force)
  done

lemma F_CFG_APLM_F_CFG_APLM__fp_invariant_03_unfold: "
  F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}
  \<Longrightarrow> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G} \<subseteq> cfgLM_accessible_nonterminals G"
  apply(rule F_CFG_APLM__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga E N)(*strict*)
   defer
   apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
   apply(rename_tac G E N)(*strict*)
   apply(rename_tac G E N)
   apply(clarsimp)
   apply(rename_tac G E N x)(*strict*)
   apply(subgoal_tac "F_CFG_APLM__fp G E N=N")
    apply(rename_tac G E N x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_APLM__fp_invariants_def F_CFG_APLM__fp_invariant_03_def)
    apply(rule_tac
      A="F_CFG_APLM__fp G E N"
      in set_mp)
     apply(rename_tac G E N x)(*strict*)
     apply(force)
    apply(rename_tac G E N x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G E N x)(*strict*)
   apply(rule_tac
      s="(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      and t="F_CFG_APLM__fp G E N"
      in ssubst)
    apply(rename_tac G E N x)(*strict*)
    apply(rule F_CFG_APLM__fp.psimps)
    apply(rule F_CFG_APLM__fp_termination)
    apply(blast)
   apply(rename_tac G E N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga E N)(*strict*)
  apply(thin_tac "F_CFG_APLM__fp_valid_input G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}")
  apply(rename_tac G E N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G E N x)(*strict*)
  apply(case_tac "N = F_CFG_APLM__fp_one G E N")
   apply(rename_tac G E N x)(*strict*)
   apply(clarsimp)
   apply(force)
  apply(rename_tac G E N x)(*strict*)
  apply(rule_tac
      A = "F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N)"
      in set_mp)
   apply(rename_tac G E N x)(*strict*)
   apply(blast)
  apply(rename_tac G E N x)(*strict*)
  apply(rule_tac
      t = "F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N)"
      and s = "F_CFG_APLM__fp G E N"
      in ssubst)
   apply(rename_tac G E N x)(*strict*)
   apply(rule sym)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N)"
      and t = "F_CFG_APLM__fp G E N"
      and s = "(if F_CFG_APLM__fp_one G E N = N then N else F_CFG_APLM__fp G E (F_CFG_APLM__fp_one G E N))"
      in ssubst)
    apply(rename_tac G E N x)(*strict*)
    apply(rule F_CFG_APLM__fp.psimps)
    apply(rule F_CFG_APLM__fp_termination)
    apply(blast)
   apply(rename_tac G E N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G E N x)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_APLMSoundL2: "
  valid_cfg G
  \<Longrightarrow> cfgLM_accessible_nonterminals G \<supseteq> F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
  apply(rule F_CFG_APLM_F_CFG_APLM__fp_invariant_03_unfold)
  apply(simp add: F_CFG_APLM__fp_valid_input_def valid_cfg_def)
  done

lemma F_CFG_APLMSoundL: "
  valid_cfg G
  \<Longrightarrow> cfgLM_accessible_nonterminals G = F_CFG_APLM__fp G (cfgSTD_Nonblockingness_nonterminals G) {cfg_initial G}"
  apply(rule order_antisym)
   apply(rule F_CFG_APLMSoundL1)
   apply(blast)
  apply(rule F_CFG_APLMSoundL2)
  apply(blast)
  done

theorem F_CFG_APLM_vs_cfgLM_SPEC_CFGEA__Productions: "
  valid_cfg G
  \<Longrightarrow> F_CFG_APLM G = cfgLM_SPEC_CFGEA__Productions G"
  apply(subgoal_tac "cfgLM_accessible_nonterminals G = F_CFG_APLM__fp G (F_CFG_EB__fp G {}) {cfg_initial G}")
   apply(simp add: F_CFG_APLM_def cfgLM_SPEC_CFGEA__Productions_def Let_def)
  apply(rule_tac t="F_CFG_EB__fp G {}" in ssubst)
   prefer 2
   apply(rule F_CFG_APLMSoundL)
   apply(force)
  apply (metis F_CFG_EBSoundL)
  done

end
