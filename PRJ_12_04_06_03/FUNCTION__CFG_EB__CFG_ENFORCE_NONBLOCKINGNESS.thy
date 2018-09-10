section {*FUNCTION\_\_CFG\_EB\_\_CFG\_ENFORCE\_NONBLOCKINGNESS*}
theory
  FUNCTION__CFG_EB__CFG_ENFORCE_NONBLOCKINGNESS

imports
  PRJ_12_04_06_03__ENTRY

begin

definition F_CFG_EB__fp_valid_input :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EB__fp_valid_input G N \<equiv>
  valid_cfg G
  \<and> N \<subseteq> cfg_nonterminals G"

definition F_CFG_EB__fp_invariant_01 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EB__fp_invariant_01 G N \<equiv>
   \<forall>p \<in> cfg_productions G.
   setA (prod_rhs p) \<subseteq> N
   \<longrightarrow> prod_lhs p \<in> F_CFG_EB__fp_one G N"

definition F_CFG_EB__fp_invariant_02 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EB__fp_invariant_02 G N \<equiv>
  N \<subseteq> cfg_nonterminals G"

definition F_CFG_EB__fp_invariant_03 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EB__fp_invariant_03 G N \<equiv>
  \<forall>A \<in> N. \<exists>e. e \<in> cfg_productions G
  \<and> prod_lhs e \<in> N
  \<and> setA (prod_rhs e) \<subseteq> N
  \<and> prod_lhs e = A"

definition F_CFG_EB__fp_invariant_04 :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EB__fp_invariant_04 G N \<equiv>
  N \<subseteq> cfgSTD_Nonblockingness_nonterminals G"

definition F_CFG_EB__fp_invariants :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> 'nonterminal set
  \<Rightarrow> bool"
  where
    "F_CFG_EB__fp_invariants G N \<equiv>
  F_CFG_EB__fp_invariant_04 G N
  \<and> F_CFG_EB__fp_invariant_01 G N
  \<and> F_CFG_EB__fp_invariant_02 G N
  \<and> F_CFG_EB__fp_invariant_03 G N
  \<and> F_CFG_EB__fp_valid_input G N"

lemma F_CFG_EB__fp_invariants_AT_kleene_starT: "
  F_CFG_EB__fp_valid_input G {}
  \<Longrightarrow> F_CFG_EB__fp_invariants G {}"
  apply(simp add: F_CFG_EB__fp_invariants_def)
  apply(simp add: F_CFG_EB__fp_invariant_04_def F_CFG_EB__fp_invariant_01_def F_CFG_EB__fp_invariant_02_def F_CFG_EB__fp_invariant_03_def )
  apply(auto)
  apply(rename_tac p)(*strict*)
  apply(simp add: F_CFG_EB__fp_one_def)
  apply(auto)
  done

lemma F_CFG_EB_termLem1: "
  F_CFG_EB__fp_one G N \<noteq> N
  \<Longrightarrow> F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> F_CFG_EB__fp_valid_input G (F_CFG_EB__fp_one G N)"
  apply(unfold F_CFG_EB__fp_valid_input_def F_CFG_EB__fp_one_def)
  apply(auto)
  apply(rename_tac p pa)(*strict*)
  apply(case_tac pa)
  apply(rename_tac p pa prod_lhsa prod_rhsa)(*strict*)
  apply(auto)
  apply(rename_tac p prod_lhsa prod_rhsa)(*strict*)
  apply(simp add: valid_cfg_def)
  done

lemma F_CFG_EB__fp_one_preserves_F_CFG_EB__fp_valid_input: "
  F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> F_CFG_EB__fp_valid_input G (F_CFG_EB__fp_one G N)"
  apply(case_tac "F_CFG_EB__fp_one G N = N")
   apply(clarsimp)
  apply(rule F_CFG_EB_termLem1)
   apply(auto)
  done

lemma F_CFG_EB_sumSmaller: "
  F_CFG_EB__fp_one G N \<noteq> N
  \<Longrightarrow> F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> card (cfg_nonterminals G - F_CFG_EB__fp_one G N) < card (cfg_nonterminals G - N)"
  apply(auto)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_CFG_EB__fp_valid_input_def)
   apply(subgoal_tac "N=F_CFG_EB__fp_one G N")
    apply(rename_tac x)(*strict*)
    apply(clarsimp)
   apply(rename_tac x)(*strict*)
   apply(rule card_seteq)
     apply(rename_tac x)(*strict*)
     apply(rule_tac
      B="cfg_nonterminals G"
      in finite_subset)
      apply(rename_tac x)(*strict*)
      apply(simp add: F_CFG_EB__fp_one_def)
      apply(clarsimp)
      apply(rename_tac x p)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac x)(*strict*)
     apply(simp add: valid_cfg_def)
    apply(rename_tac x)(*strict*)
    apply(simp add: F_CFG_EB__fp_one_def)
   apply(rename_tac x)(*strict*)
   apply(auto)
   apply(subgoal_tac "card (cfg_nonterminals G - F_CFG_EB__fp_one G N) \<ge> card (cfg_nonterminals G - N)")
    apply(rename_tac x)(*strict*)
    apply(auto)
   apply(rename_tac x)(*strict*)
   apply(subgoal_tac "card (cfg_nonterminals G - F_CFG_EB__fp_one G N) = card (cfg_nonterminals G) - card (F_CFG_EB__fp_one G N)")
    apply(rename_tac x)(*strict*)
    apply(auto)
    apply(subgoal_tac "card (cfg_nonterminals G - N) = card (cfg_nonterminals G) - card N")
     apply(rename_tac x)(*strict*)
     apply(auto)
     apply(subgoal_tac "card (cfg_nonterminals G) - card (F_CFG_EB__fp_one G N) \<ge> card (cfg_nonterminals G) - card N")
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
      apply(simp add: F_CFG_EB__fp_one_def)
      apply(clarsimp)
      apply(rename_tac x p)(*strict*)
      apply(simp add: valid_cfg_def)
     apply(rename_tac x)(*strict*)
     apply(clarsimp)
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
     apply(simp add: F_CFG_EB__fp_one_def)
     apply(clarsimp)
     apply(rename_tac x p)(*strict*)
     apply(simp add: valid_cfg_def)
    apply(rename_tac x)(*strict*)
    apply(simp add: valid_cfg_def)
   apply(rename_tac x)(*strict*)
   apply(simp add: F_CFG_EB__fp_one_def)
   apply(clarsimp)
   apply(rename_tac x p)(*strict*)
   apply(simp add: valid_cfg_def)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_CFG_EB__fp_one_def)
  done

lemma F_CFG_EB__fp_one_TRANSFER_TRANSFERS_SOUND: "
  F_CFG_EB__fp_valid_input G (F_CFG_EB__fp_one G N)
  \<Longrightarrow> F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> F_CFG_EB__fp_invariants G N
  \<Longrightarrow> F_CFG_EB__fp_invariant_04 G (F_CFG_EB__fp_one G N)"
  apply(subgoal_tac "F_CFG_EB__fp_invariant_04 G N")
   defer
   apply(simp add: F_CFG_EB__fp_invariants_def)
  apply(subgoal_tac "valid_cfg G")
   defer
   apply(simp add: F_CFG_EB__fp_invariants_def F_CFG_EB__fp_valid_input_def)
  apply(simp add: F_CFG_EB__fp_invariant_04_def)
  apply(simp add: F_CFG_EB__fp_one_def)
  apply(auto)
  apply(rename_tac p)(*strict*)
  apply(subgoal_tac "setA (prod_rhs p) \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
   apply(rename_tac p)(*strict*)
   defer
   apply(rule_tac
      B="N"
      in subset_trans)
    apply(rename_tac p)(*strict*)
    apply(clarsimp)
   apply(rename_tac p)(*strict*)
   apply(clarsimp)
  apply(rename_tac p)(*strict*)
  apply(thin_tac "F_CFG_EB__fp_valid_input G (N \<union> X)" for X)
  apply(thin_tac "F_CFG_EB__fp_valid_input G N")
  apply(thin_tac "F_CFG_EB__fp_invariants G N")
  apply(thin_tac "N \<subseteq> cfgSTD_Nonblockingness_nonterminals G")
  apply(thin_tac "setA (prod_rhs p) \<subseteq> N")
  apply(case_tac p)
  apply(rename_tac p prod_lhsa prod_rhsa)(*strict*)
  apply(clarsimp)
  apply(rename_tac prod_lhs prod_rhs)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac A w)(*strict*)
  apply(subgoal_tac "(\<exists>d w'. (cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>}) \<and> (setA w'={}))")
   apply(rename_tac A w)(*strict*)
   apply(auto)
   apply(rename_tac A w d w')(*strict*)
   apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
    apply(rename_tac A w d w')(*strict*)
    apply(auto)
    apply(rename_tac A w d w' n)(*strict*)
    apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
    apply(auto)
     apply(rename_tac A w d w' n)(*strict*)
     apply(simp add: valid_cfg_def)
     apply(auto)
    apply(rename_tac A w d w' n)(*strict*)
    apply(rule_tac
      x = "derivation_append (der2 \<lparr>cfg_conf = [teA A]\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = w\<rparr>) d (Suc 0)"
      in exI)
    apply(rule_tac
      x="w'"
      in exI)
    apply(rule conjI)
     apply(rename_tac A w d w' n)(*strict*)
     apply(rule_tac
      dJ = "\<lparr>cfg_conf=w\<rparr>"
      in cfgSTD.concatIsFromTo)
        apply(rename_tac A w d w' n)(*strict*)
        apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
        apply(rule conjI)
         apply(rename_tac A w d w' n)(*strict*)
         apply(rule cfgSTD.der2_is_derivation)
         apply(simp add: cfgSTD_step_relation_def)
         apply(force)
        apply(rename_tac A w d w' n)(*strict*)
        apply(rule conjI)
         apply(rename_tac A w d w' n)(*strict*)
         apply(simp add: der2_def)
        apply(rename_tac A w d w' n)(*strict*)
        apply(rule conjI)
         apply(rename_tac A w d w' n)(*strict*)
         apply(rule cfgSTD.der2_is_derivation)
         apply(simp add: cfgSTD_step_relation_def)
         apply(force)
        apply(rename_tac A w d w' n)(*strict*)
        apply(rule_tac
      x="Suc 0"
      in exI)
        apply(rule conjI)
         apply(rename_tac A w d w' n)(*strict*)
         apply(simp add: der2_def)
        apply(rename_tac A w d w' n)(*strict*)
        apply(clarsimp)
        apply(rename_tac A w d w' n na x)(*strict*)
        apply(rule_tac
      x="pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) \<lparr>cfg_conf = w\<rparr>"
      in exI)
        apply(clarsimp)
        apply(simp add: der2_def)
       apply(rename_tac A w d w' n)(*strict*)
       apply(force)
      apply(rename_tac A w d w' n)(*strict*)
      apply(rule der2_maximum_of_domain)
     apply(rename_tac A w d w' n)(*strict*)
     apply(force)
    apply(rename_tac A w d w' n)(*strict*)
    apply(force)
   apply(rename_tac A w d w')(*strict*)
   apply(simp add: cfgSTD.derivation_to_def cfgSTD.derivation_from_to_def)
   apply(clarsimp)
   apply(rename_tac A w d w' n x)(*strict*)
   apply(rule_tac
      x="n"
      in exI)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac A w)(*strict*)
  apply(thin_tac "\<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<in> cfg_productions G")
  apply(auto)
  apply(rename_tac w)(*strict*)
  apply(rule canElimCombine)
   apply(rename_tac w)(*strict*)
   apply(blast)+
  done

lemma F_CFG_EB__fp_one_TRANSFER_TRANSFERS_EXTRA_01: "
  F_CFG_EB__fp_valid_input G (F_CFG_EB__fp_one G N)
  \<Longrightarrow> F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> F_CFG_EB__fp_invariants G N
  \<Longrightarrow> F_CFG_EB__fp_invariant_01 G (F_CFG_EB__fp_one G N)"
  apply(simp add: F_CFG_EB__fp_invariant_01_def)
  apply(auto)
  apply(rename_tac p)(*strict*)
  apply(simp add: F_CFG_EB__fp_one_def)
  apply(auto)
  done

lemma F_CFG_EB__fp_one_TRANSFER_TRANSFERS_EXTRA_02: "
  F_CFG_EB__fp_valid_input G (F_CFG_EB__fp_one G N)
  \<Longrightarrow> F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> F_CFG_EB__fp_invariants G N
  \<Longrightarrow> F_CFG_EB__fp_invariant_02 G (F_CFG_EB__fp_one G N)"
  apply(simp add: F_CFG_EB__fp_invariant_02_def F_CFG_EB__fp_invariants_def)
  apply(auto)
  apply(rename_tac x)(*strict*)
  apply(simp add: F_CFG_EB__fp_one_def)
  apply(auto)
  apply(rename_tac p)(*strict*)
  apply(simp add: F_CFG_EB__fp_valid_input_def valid_cfg_def)
  done

lemma F_CFG_EB__fp_one_TRANSFER_TRANSFERS_EXTRA_03: "
  F_CFG_EB__fp_valid_input G (F_CFG_EB__fp_one G N)
  \<Longrightarrow> F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> F_CFG_EB__fp_invariants G N
  \<Longrightarrow> F_CFG_EB__fp_invariant_03 G (F_CFG_EB__fp_one G N)"
  apply(simp add: F_CFG_EB__fp_invariant_03_def F_CFG_EB__fp_invariants_def)
  apply(auto)
  apply(rename_tac A)(*strict*)
  apply(simp add: F_CFG_EB__fp_one_def)
  apply(auto)
  apply(erule_tac
      x="A"
      in ballE)
   apply(rename_tac A)(*strict*)
   apply(clarsimp)
   apply(rename_tac e)(*strict*)
   prefer 2
   apply(rename_tac A)(*strict*)
   apply(clarsimp)
  apply(rename_tac e)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(clarsimp)
  apply(rename_tac e x)(*strict*)
  apply(subgoal_tac "x\<in> N")
   apply(rename_tac e x)(*strict*)
   apply(clarsimp)
  apply(rename_tac e x)(*strict*)
  apply(force)
  done

lemma F_CFG_EB__fp_one_TRANSFER_TRANSFERS_ALL: "
  F_CFG_EB__fp_valid_input G (F_CFG_EB__fp_one G N)
  \<Longrightarrow> F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> F_CFG_EB__fp_invariants G N
  \<Longrightarrow> F_CFG_EB__fp_invariants G (F_CFG_EB__fp_one G N)"
  apply(simp (no_asm) add: F_CFG_EB__fp_invariants_def)
  apply(rule conjI)
   apply(rule F_CFG_EB__fp_one_TRANSFER_TRANSFERS_SOUND)
     apply(blast)+
  apply(rule conjI)
   apply(rule F_CFG_EB__fp_one_TRANSFER_TRANSFERS_EXTRA_01)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_EB__fp_one_TRANSFER_TRANSFERS_EXTRA_02)
     apply(blast+)
  apply(rule conjI)
   apply(rule F_CFG_EB__fp_one_TRANSFER_TRANSFERS_EXTRA_03)
     apply(blast+)
  done

lemma F_CFG_EB__fp_Meta_Lift: "
  F_CFG_EB__fp_valid_input G {}
  \<Longrightarrow> (\<And>G N. F_CFG_EB__fp_valid_input G (F_CFG_EB__fp_one G N) \<Longrightarrow> F_CFG_EB__fp_valid_input G N \<Longrightarrow> F_CFG_EB__fp_invariants G N \<Longrightarrow> P (F_CFG_EB__fp G (F_CFG_EB__fp_one G N)) G \<Longrightarrow> P (F_CFG_EB__fp G N) G)
  \<Longrightarrow> (\<And>G N. F_CFG_EB__fp_one G N = N \<Longrightarrow> F_CFG_EB__fp_valid_input G N \<Longrightarrow> F_CFG_EB__fp_invariants G N  \<Longrightarrow> P (F_CFG_EB__fp G N) G)
  \<Longrightarrow> P (F_CFG_EB__fp G {}) G"
  apply(subgoal_tac "(\<lambda>G N. F_CFG_EB__fp_invariants G N \<longrightarrow> (P (F_CFG_EB__fp G N) G)) G {}")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_CFG_EB__fp_invariants_AT_kleene_starT)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G,N). F_CFG_EB__fp_invariants G N \<longrightarrow> (P (F_CFG_EB__fp G N) G)) (G,{})")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,N). F_CFG_EB__fp_valid_input G N"
      and RECURSIVE_COND = "\<lambda>(G,N). F_CFG_EB__fp_one G N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,N). (G,F_CFG_EB__fp_one G N)"
      and MEASURE = "\<lambda>(G,N). card (cfg_nonterminals G - N)"
      and TERM_FUN = "(\<lambda>(G,N). F_CFG_EB__fp_invariants G N \<longrightarrow> (P (F_CFG_EB__fp G N) G))"
      and y = "(G,{})"
      in partial_termination_wf)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a b)(*strict*)
      apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
      apply(rename_tac G N)
      apply(rename_tac G N)(*strict*)
      apply(rule F_CFG_EB__fp_one_preserves_F_CFG_EB__fp_valid_input)
      apply(blast)
     apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
     apply(clarsimp)
     apply(rename_tac a b)(*strict*)
     apply(rename_tac G N)
     apply(rename_tac G N)(*strict*)
     apply(rule F_CFG_EB_sumSmaller)
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
   apply(rule F_CFG_EB__fp_one_TRANSFER_TRANSFERS_ALL)
     apply(rename_tac a b)(*strict*)
     apply(blast)+
  done

lemma F_CFG_EB__fp_termination: "
  F_CFG_EB__fp_valid_input G N
  \<Longrightarrow> F_CFG_EB__fp_dom (G, N)"
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,N). F_CFG_EB__fp_valid_input G N"
      and RECURSIVE_COND = "\<lambda>(G,N). F_CFG_EB__fp_one G N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,N). (G,F_CFG_EB__fp_one G N)"
      and MEASURE = "\<lambda>(G,f). card (cfg_nonterminals G - f)"
      in partial_termination_wf)
      apply(clarsimp)
      apply(rename_tac a b)(*strict*)
      apply(rule F_CFG_EB_termLem1)
       apply(rename_tac a b)(*strict*)
       apply(blast,blast)
     defer
     apply(clarsimp)
     apply(rename_tac a b)(*strict*)
     apply(rule F_CFG_EB__fp.domintros,blast,blast)
    apply(clarsimp)
    apply(rename_tac a b)(*strict*)
    apply(rule F_CFG_EB__fp.domintros,blast,blast)
   apply(blast)
  apply(clarsimp)
  apply(rename_tac a b)(*strict*)
  apply(rule F_CFG_EB_sumSmaller)
   apply(rename_tac a b)(*strict*)
   apply(blast)
  apply(rename_tac a b)(*strict*)
  apply(blast)
  done

lemma F_CFG_EB_F_CFG_EB__fp_invariant_01_unfold: "
  F_CFG_EB__fp_valid_input G {}
  \<Longrightarrow> \<forall>p \<in> cfg_productions G. setA (prod_rhs p) \<subseteq> F_CFG_EB__fp G {} \<longrightarrow> prod_lhs p \<in> F_CFG_EB__fp G {}"
  apply(rule F_CFG_EB__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga N)(*strict*)
   defer
   apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
   apply(rename_tac G N)(*strict*)
   apply(rename_tac G N)
   apply(clarsimp)
   apply(rename_tac G N p)(*strict*)
   apply(subgoal_tac "F_CFG_EB__fp G N=N")
    apply(rename_tac G N p)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_EB__fp_invariants_def F_CFG_EB__fp_invariant_01_def)
   apply(rename_tac G N p)(*strict*)
   apply(rule_tac
      s="(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      and t="F_CFG_EB__fp G N"
      in ssubst)
    apply(rename_tac G N p)(*strict*)
    apply(rule F_CFG_EB__fp.psimps)
    apply(rule F_CFG_EB__fp_termination)
    apply(blast)
   apply(rename_tac G N p)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga N)(*strict*)
  apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
  apply(rename_tac G N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G N p)(*strict*)
  apply(erule_tac
      x="p"
      in ballE)
   apply(rename_tac G N p)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac G N p)(*strict*)
  apply(erule impE)
   apply(rename_tac G N p)(*strict*)
   apply(rule_tac
      t = "F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and s = "F_CFG_EB__fp G N"
      in ssubst)
    apply(rename_tac G N p)(*strict*)
    apply(case_tac "N = F_CFG_EB__fp_one G N")
     apply(rename_tac G N p)(*strict*)
     apply(clarsimp)
    apply(rename_tac G N p)(*strict*)
    apply(rule sym)
    apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      and s = "(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      in ssubst)
     apply(rename_tac G N p)(*strict*)
     apply(rule F_CFG_EB__fp.psimps)
     apply(rule F_CFG_EB__fp_termination)
     apply(blast)
    apply(rename_tac G N p)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N p)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N p)(*strict*)
  apply(rule_tac
      s = "F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      in ssubst)
   apply(rename_tac G N p)(*strict*)
   apply(case_tac "N = F_CFG_EB__fp_one G N")
    apply(rename_tac G N p)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N p)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      and s = "(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      in ssubst)
    apply(rename_tac G N p)(*strict*)
    apply(rule F_CFG_EB__fp.psimps)
    apply(rule F_CFG_EB__fp_termination)
    apply(blast)
   apply(rename_tac G N p)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N p)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_EBSound0_1: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB__fp G {} = N
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>}
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> setA w1 \<subseteq> N"
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   apply(clarsimp del: subsetI)
   apply(rename_tac n)(*strict*)
   apply(subgoal_tac "\<forall>n. \<forall>d w1 w2. maximum_of_domain d n \<and> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>} \<and> setA w2 = {} \<longrightarrow> setA w1 \<subseteq> F_CFG_EB__fp G {}")
    apply(rename_tac n)(*strict*)
    apply(erule_tac
      x="n"
      in allE)
    apply(erule_tac
      x="d"
      in allE)
    apply(erule_tac
      x="w1"
      in allE)
    apply(erule_tac
      x="w2"
      in allE)
    apply(clarsimp)
   apply(rename_tac n)(*strict*)
   apply(rule allI)
   apply(rename_tac n na)(*strict*)
   apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>}")
   apply(thin_tac "setA w2 = {}")
   apply(thin_tac "maximum_of_domain d n")
   apply(induct_tac na)
    apply(rename_tac n na)(*strict*)
    apply(clarsimp del: subsetI)
    apply(rename_tac d w1 w2)(*strict*)
    apply(subgoal_tac "w1=w2")
     apply(rename_tac d w1 w2)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w1 w2)(*strict*)
    defer
    apply(rename_tac n na nb)(*strict*)
    apply(clarsimp del: subsetI)
    apply(rename_tac nb d w1 w2)(*strict*)
    apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1\<rparr>}. d 0 = Some x")
     apply(rename_tac nb d w1 w2)(*strict*)
     prefer 2
     apply(rule cfgSTD.derivation_from_starts_from)
     apply(rule cfgSTD.from_to_is_from)
     apply(blast)
    apply(rename_tac nb d w1 w2)(*strict*)
    apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
     apply(rename_tac nb d w1 w2)(*strict*)
     prefer 2
     apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
       apply(rename_tac nb d w1 w2)(*strict*)
       apply(rule cfgSTD.from_to_is_der)
       apply(blast)
      apply(rename_tac nb d w1 w2)(*strict*)
      apply(blast)
     apply(rename_tac nb d w1 w2)(*strict*)
     apply(arith)
    apply(rename_tac nb d w1 w2)(*strict*)
    apply(subgoal_tac "\<exists>e. d (Suc nb) = Some (pair e \<lparr>cfg_conf=w2\<rparr>)")
     apply(rename_tac nb d w1 w2)(*strict*)
     prefer 2
     apply(rule cfgSTD.reachesToAtMaxDom)
      apply(rename_tac nb d w1 w2)(*strict*)
      apply(rule cfgSTD.from_to_is_to)
      apply(blast)
     apply(rename_tac nb d w1 w2)(*strict*)
     apply(clarsimp)
    apply(rename_tac nb d w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac nb d w1 w2 x e ea c)(*strict*)
    apply(case_tac c)
    apply(rename_tac nb d w1 w2 x e ea c cfg_conf)(*strict*)
    apply(clarsimp)
    apply(rename_tac nb d w1 w2 x e ea cfg_conf)(*strict*)
    apply(rename_tac w1')
    apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
    apply(erule_tac
      x="derivation_drop d (Suc 0)"
      in allE)
    apply(erule_tac
      x="w1'"
      in allE)
    apply(erule_tac impE)
     apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
     apply(rule conjI)
      apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
      apply(rule derivation_drop_preserves_generates_maximum_of_domain)
      apply(blast)
     apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
     apply(rule_tac
      x="w2"
      in exI)
     apply(clarsimp)
     defer
     apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = w1'\<rparr>")
      apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
      apply(simp add: cfgSTD_step_relation_def)
      apply(clarsimp)
      apply(rename_tac nb d w2 x e ea l r)(*strict*)
      apply(case_tac e)
      apply(rename_tac nb d w2 x e ea l r prod_lhsa prod_rhsa)(*strict*)
      apply(clarsimp)
      apply(rename_tac nb d w2 x ea l r prod_lhs prod_rhs)(*strict*)
      apply(rename_tac A w)
      apply(rename_tac nb d w2 x ea l r A w)(*strict*)
      apply(subgoal_tac "setA (l @ [teA A] @ r) \<subseteq> F_CFG_EB__fp G {}")
       apply(rename_tac nb d w2 x ea l r A w)(*strict*)
       apply(force)
      apply(rename_tac nb d w2 x ea l r A w)(*strict*)
      apply(simp (no_asm) only: setAConcat concat_asso)
      apply(clarsimp)
      apply(rule conjI)
       apply(rename_tac nb d w2 x ea l r A w)(*strict*)
       defer
       apply(simp only: setAConcat concat_asso)
       apply(clarsimp)
      apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
      apply(rule cfgSTD.stepOnlyDueToStepRelation)
         apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
         apply(blast)
        apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
        apply(rule cfgSTD.from_to_is_der)
        apply(blast)
       apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
       apply(blast)
      apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
      apply(blast)
     apply(rule cfgSTD.to_has_maximum_of_domain)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac d w1 w2)(*strict*)
    apply(rule ZeroLengthDeriStartIsEnd)
      apply(rename_tac d w1 w2)(*strict*)
      apply(blast)
     apply(rename_tac d w1 w2)(*strict*)
     apply(blast)
    apply(rename_tac d w1 w2)(*strict*)
    apply(blast)
   apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
   apply(rule_tac
      m = "nb"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
      apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
      apply(blast)
     apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
     apply(rule_tac
      s = "Suc nb"
      in ssubst)
      apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
      apply(arith)
     apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
     apply(blast)
    apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
    apply(blast)
   apply(rename_tac nb d w1 w2 x e ea w1')(*strict*)
   apply(clarsimp)
  apply(rename_tac nb d w2 x ea l r A w)(*strict*)
  apply(subgoal_tac "\<forall>p\<in> cfg_productions G. setA (prod_rhs p) \<subseteq> F_CFG_EB__fp G {} \<longrightarrow> prod_lhs p \<in> F_CFG_EB__fp G {}")
   apply(rename_tac nb d w2 x ea l r A w)(*strict*)
   defer
   apply(rule F_CFG_EB_F_CFG_EB__fp_invariant_01_unfold)
   apply(simp add: F_CFG_EB__fp_valid_input_def)
  apply(rename_tac nb d w2 x ea l r A w)(*strict*)
  apply(erule_tac
      x="\<lparr>prod_lhs = A, prod_rhs = w\<rparr>"
      in ballE)
   apply(rename_tac nb d w2 x ea l r A w)(*strict*)
   apply(erule impE)
    apply(rename_tac nb d w2 x ea l r A w)(*strict*)
    apply(clarsimp del: subsetI)
    apply(simp only: setAConcat concat_asso)
    apply(clarsimp)
   apply(rename_tac nb d w2 x ea l r A w)(*strict*)
   apply(clarsimp)
  apply(rename_tac nb d w2 x ea l r A w)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_EBSoundL1: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G \<subseteq> F_CFG_EB__fp G {}"
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(auto)
  apply(rename_tac x d w')(*strict*)
  apply(subgoal_tac "setA [teA x] \<subseteq> F_CFG_EB__fp G {}")
   apply(rename_tac x d w')(*strict*)
   apply(clarsimp)
  apply(rename_tac x d w')(*strict*)
  apply(rule F_CFG_EBSound0_1)
     apply(rename_tac x d w')(*strict*)
     apply(blast)+
  done

lemma F_CFG_EB_F_CFG_EB__fp_invariant_04_unfold: "
  F_CFG_EB__fp_valid_input G {}
  \<Longrightarrow> F_CFG_EB__fp G {} \<subseteq> cfgSTD_Nonblockingness_nonterminals G"
  apply(rule F_CFG_EB__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga N)(*strict*)
   defer
   apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
   apply(rename_tac G N)(*strict*)
   apply(rename_tac G N)
   apply(clarsimp)
   apply(rename_tac G N x)(*strict*)
   apply(subgoal_tac "F_CFG_EB__fp G N=N")
    apply(rename_tac G N x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_EB__fp_invariants_def F_CFG_EB__fp_invariant_04_def)
    apply(rule_tac
      A="F_CFG_EB__fp G N"
      in set_mp)
     apply(rename_tac G N x)(*strict*)
     apply(force)
    apply(rename_tac G N x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N x)(*strict*)
   apply(rule_tac
      s="(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      and t="F_CFG_EB__fp G N"
      in ssubst)
    apply(rename_tac G N x)(*strict*)
    apply(rule F_CFG_EB__fp.psimps)
    apply(rule F_CFG_EB__fp_termination)
    apply(blast)
   apply(rename_tac G N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga N)(*strict*)
  apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
  apply(rename_tac G N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G N x)(*strict*)
  apply(rule_tac
      A = "F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      in set_mp)
   apply(rename_tac G N x)(*strict*)
   apply(blast)
  apply(rename_tac G N x)(*strict*)
  apply(rule_tac
      t = "F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and s = "F_CFG_EB__fp G N"
      in ssubst)
   apply(rename_tac G N x)(*strict*)
   apply(case_tac "N = F_CFG_EB__fp_one G N")
    apply(rename_tac G N x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N x)(*strict*)
   apply(rule sym)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      and s = "(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      in ssubst)
    apply(rename_tac G N x)(*strict*)
    apply(rule F_CFG_EB__fp.psimps)
    apply(rule F_CFG_EB__fp_termination)
    apply(blast)
   apply(rename_tac G N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N x)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_EBSoundL2: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G \<supseteq> F_CFG_EB__fp G {}"
  apply(rule F_CFG_EB_F_CFG_EB__fp_invariant_04_unfold)
  apply(simp add: F_CFG_EB__fp_valid_input_def)
  done

lemma F_CFG_EBSoundL: "
  valid_cfg G
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G = F_CFG_EB__fp G {}"
  apply(rule order_antisym)
   apply(rule F_CFG_EBSoundL1)
   apply(blast)
  apply(rule F_CFG_EBSoundL2)
  apply(blast)
  done

lemma canNotElimWordWithNotEliminableNonterminal: "
  valid_cfg G
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> A \<in> setA w
  \<Longrightarrow> F_CFG_EB (G\<lparr>cfg_initial := A\<rparr>) = None
  \<Longrightarrow> {} = cfgSTD_first_symbol_of_derivable_marked_effect G w"
  apply(subgoal_tac "A\<notin>cfgSTD_Nonblockingness_nonterminals G")
   apply(thin_tac "F_CFG_EB (G\<lparr>cfg_initial := A\<rparr>) = None")
   apply(subgoal_tac "\<exists>w1 w2. w1 @ [teA A] @ w2 = w")
    apply(erule exE)+
    apply(rename_tac w1 w2)(*strict*)
    apply(simp add: cfgSTD_first_symbol_of_derivable_marked_effect_def)
    apply(clarsimp)
    apply(auto)
     apply(rename_tac w1 w2 v d w')(*strict*)
     apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = teA A#w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = teB v # w' ")
      apply(rename_tac w1 w2 v d w')(*strict*)
      prefer 2
      apply(rule derivationCanBeDecomposed)
      apply(blast)
     apply(rename_tac w1 w2 v d w')(*strict*)
     apply(clarsimp)
     apply(rename_tac w1 w2 v d w' d1 d2 w1' w2')(*strict*)
     apply(rename_tac w2'')
     apply(rename_tac w1 w2 v d w' d1 d2 w1' w2'')(*strict*)
     apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = w2''")
      apply(rename_tac w1 w2 v d w' d1 d2 w1' w2'')(*strict*)
      prefer 2
      apply(rule derivationCanBeDecomposed)
      apply(clarsimp)
      apply(blast)
     apply(rename_tac w1 w2 v d w' d1 d2 w1' w2'')(*strict*)
     apply(clarsimp)
     apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
     apply(case_tac "setA w1'nonterminal = {}")
      apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
      apply(subgoal_tac "A \<in> cfgSTD_Nonblockingness_nonterminals G")
       apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
       apply(force)
      apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
      apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
      apply(rule conjI)
       apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
       apply(force)
      apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
      apply(force)
     apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
     apply(subgoal_tac "setA w1'nonterminal = {}")
      apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
      apply(force)
     apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
     apply(rule order_antisym)
      apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
      apply(rule_tac
      B="setA (w1' @ w1'nonterminal @ w2')"
      in subset_trans)
       apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
       apply(simp (no_asm) only: setAConcat concat_asso)
       apply(blast)
      apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
      apply(rule_tac
      t="w1' @ w1'nonterminal @ w2'"
      and s="teB v # w'"
      in ssubst)
       apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
       apply(force)
      apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
      apply(clarsimp)
     apply(rename_tac w1 w2 v d w' d1 d2 w1' d1a d2a w1'nonterminal w2')(*strict*)
     apply(force)
    apply(rename_tac w1 w2 d)(*strict*)
    prefer 2
    apply(rule_tac
      t="\<exists>w1 w2. w1 @ teA A # w2=w"
      and s="\<exists>w1 w2. w1 @ [teA A] @ w2=w"
      in ssubst)
     apply(force)
    apply(rule setA_decomp)
    apply(blast)
   apply(rename_tac w1 w2 d)(*strict*)
   prefer 2
   apply(subgoal_tac "A \<notin> cfgSTD_Nonblockingness_nonterminals G")
    apply(force)
   apply(rule_tac
      t="cfgSTD_Nonblockingness_nonterminals G"
      and s="cfgSTD_Nonblockingness_nonterminals (G\<lparr>cfg_initial := A\<rparr>)"
      in ssubst)
    prefer 2
    apply(simp add: F_CFG_EB_def)
    apply(clarsimp)
    apply(case_tac "A \<in> F_CFG_EB__fp (G\<lparr>cfg_initial := A\<rparr>) {}")
     apply(clarsimp)
    apply(clarsimp)
    apply(subgoal_tac "cfgSTD_Nonblockingness_nonterminals (G\<lparr>cfg_initial := A\<rparr>) = F_CFG_EB__fp (G\<lparr>cfg_initial := A\<rparr>) {}")
     apply(force)
    apply(rule F_CFG_EBSoundL)
    apply(simp add: valid_cfg_def)
    apply(clarsimp)
    apply(force)
   apply(subgoal_tac "\<forall>d FS TS. cfgSTD.derivation_from_to G d FS TS \<longleftrightarrow> cfgSTD.derivation_from_to (G\<lparr>cfg_initial := A\<rparr>) d FS TS")
    prefer 2
    apply(rule allI)+
    apply(rename_tac d FS TS)(*strict*)
    apply(rule From_To_Derivation_Set_independent_from_Initial)
       apply(rename_tac d FS TS)(*strict*)
       apply(blast)
      apply(rename_tac d FS TS)(*strict*)
      apply(blast)
     apply(rename_tac d FS TS)(*strict*)
     apply(blast)
    apply(rename_tac d FS TS)(*strict*)
    apply(blast)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(rename_tac w1 w2 d)(*strict*)
  apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = teA A#w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = [] ")
   apply(rename_tac w1 w2 d)(*strict*)
   prefer 2
   apply(rule derivationCanBeDecomposed)
   apply(blast)
  apply(rename_tac w1 w2 d)(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 d d1 d2)(*strict*)
  apply(rename_tac w2'')
  apply(rename_tac w1 w2 d d1 w2'')(*strict*)
  apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = [teA A]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = []")
   apply(rename_tac w1 w2 d d1 w2'')(*strict*)
   prefer 2
   apply(rule derivationCanBeDecomposed)
   apply(clarsimp)
   apply(blast)
  apply(rename_tac w1 w2 d d1 w2'')(*strict*)
  apply(clarsimp)
  apply(rename_tac w1 w2 d d1 w2'' d1a d2)(*strict*)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(force)
  done

lemma F_CFG_EB_F_CFG_EB__fp_invariant_03_unfold: "
  F_CFG_EB__fp_valid_input G {}
  \<Longrightarrow> \<forall>A \<in> F_CFG_EB__fp G {}. \<exists>e. e \<in> cfg_productions G \<and> prod_lhs e \<in> F_CFG_EB__fp G {} \<and> setA (prod_rhs e) \<subseteq> F_CFG_EB__fp G {} \<and> prod_lhs e = A"
  apply(rule F_CFG_EB__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga N)(*strict*)
   defer
   apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
   apply(rename_tac G N)(*strict*)
   apply(rename_tac G N)
   apply(clarsimp)
   apply(rename_tac G N A)(*strict*)
   apply(subgoal_tac "F_CFG_EB__fp G N=N")
    apply(rename_tac G N A)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_EB__fp_invariants_def F_CFG_EB__fp_invariant_03_def)
   apply(rename_tac G N A)(*strict*)
   apply(rule_tac
      s="(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      and t="F_CFG_EB__fp G N"
      in ssubst)
    apply(rename_tac G N A)(*strict*)
    apply(rule F_CFG_EB__fp.psimps)
    apply(rule F_CFG_EB__fp_termination)
    apply(blast)
   apply(rename_tac G N A)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga N)(*strict*)
  apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
  apply(rename_tac G N)(*strict*)
  apply(clarsimp)
  apply(rename_tac G N A)(*strict*)
  apply(erule_tac
      x="A"
      in ballE)
   apply(rename_tac G N A)(*strict*)
   prefer 2
   apply(subgoal_tac "F_CFG_EB__fp G N = F_CFG_EB__fp G (F_CFG_EB__fp_one G N)")
    apply(rename_tac G N A)(*strict*)
    apply(force)
   apply(rename_tac G N A)(*strict*)
   apply(rule_tac
      t = "F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and s = "F_CFG_EB__fp G N"
      in ssubst)
    apply(rename_tac G N A)(*strict*)
    apply(case_tac "N = F_CFG_EB__fp_one G N")
     apply(rename_tac G N A)(*strict*)
     apply(clarsimp)
    apply(rename_tac G N A)(*strict*)
    apply(rule sym)
    apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      and s = "(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      in ssubst)
     apply(rename_tac G N A)(*strict*)
     apply(rule F_CFG_EB__fp.psimps)
     apply(rule F_CFG_EB__fp_termination)
     apply(blast)
    apply(rename_tac G N A)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N A)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N A)(*strict*)
  apply(clarsimp)
  apply(rename_tac G N e)(*strict*)
  apply(rule_tac
      x="e"
      in exI)
  apply(clarsimp)
  apply(rename_tac G N e x)(*strict*)
  apply(rule_tac
      s = "F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      in ssubst)
   apply(rename_tac G N e x)(*strict*)
   apply(case_tac "N = F_CFG_EB__fp_one G N")
    apply(rename_tac G N e x)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N e x)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      and s = "(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      in ssubst)
    apply(rename_tac G N e x)(*strict*)
    apply(rule F_CFG_EB__fp.psimps)
    apply(rule F_CFG_EB__fp_termination)
    apply(blast)
   apply(rename_tac G N e x)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N e x)(*strict*)
  apply(force)
  done

lemma F_CFG_EBMakescfg_every_nonterminal_on_some_left_hand_side: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfg_every_nonterminal_on_some_left_hand_side G'"
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   apply(clarsimp)
   defer
   apply(clarsimp)
  apply(simp add: cfg_every_nonterminal_on_some_left_hand_side_def)
  apply(clarsimp)
  apply(rename_tac A)(*strict*)
  apply(subgoal_tac "\<forall>A\<in> (F_CFG_EB__fp G {}). \<exists>e. e \<in> cfg_productions G \<and> prod_lhs e \<in> (F_CFG_EB__fp G {}) \<and> setA (prod_rhs e) \<subseteq> (F_CFG_EB__fp G {}) \<and> prod_lhs e = A")
   apply(rename_tac A)(*strict*)
   apply(force)
  apply(rename_tac A)(*strict*)
  apply(rule F_CFG_EB_F_CFG_EB__fp_invariant_03_unfold)
  apply(simp add: F_CFG_EB__fp_valid_input_def)
  done

lemma F_CFG_EBSound4: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfg_events G = cfg_events G'"
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   apply(auto)
  done

lemma F_CFG_EB__fp_in_cfg_nonterminals: "
  F_CFG_EB__fp_valid_input G {}
  \<Longrightarrow> F_CFG_EB__fp G {} \<subseteq> cfg_nonterminals G"
  apply(rule_tac
      B="cfgSTD_Nonblockingness_nonterminals G"
      in subset_trans)
   apply(rule F_CFG_EB_F_CFG_EB__fp_invariant_04_unfold)
   apply(blast)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  done

lemma F_CFG_EBSound3_tmp: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB__fp G {} \<subseteq> cfg_nonterminals G"
  apply(rule F_CFG_EB__fp_in_cfg_nonterminals)
  apply(simp add: F_CFG_EB__fp_valid_input_def)
  done

lemma F_CFG_EB_makes_cfg_sub: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfg_sub G' G"
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   apply(clarsimp)
   apply(simp add: cfg_sub_def)
   apply(rule conjI)
    apply(rule F_CFG_EBSound3_tmp)
    apply(blast)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma F_CFG_EBSoundA: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G = cfg_nonterminals G'"
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   defer
   apply(clarsimp)
  apply(clarsimp)
  apply(rule F_CFG_EBSoundL)
  apply(blast)
  done

lemma F_CFG_EBSound0: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G'
  \<Longrightarrow> setB w \<subseteq> cfg_events G
  \<Longrightarrow> cfgSTD_first_symbol_of_derivable_marked_effect G w = cfgSTD_first_symbol_of_derivable_marked_effect G' w"
  apply(subgoal_tac "cfg_nonterminals G' \<subseteq> cfg_nonterminals G")
   prefer 2
   apply(simp add: F_CFG_EB_def)
   apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
    apply(clarsimp)
    apply(rename_tac x)(*strict*)
    apply(subgoal_tac "F_CFG_EB__fp G {} \<subseteq> cfg_nonterminals G")
     apply(rename_tac x)(*strict*)
     apply(force)
    apply(rename_tac x)(*strict*)
    apply(rule F_CFG_EBSound3_tmp)
    apply(force)
   apply(force)
  apply(rule order_antisym)
   apply(rule subsetI)
   apply(rename_tac x)(*strict*)
   apply(case_tac x)
    apply(rename_tac x)(*strict*)
    apply(simp add: cfgSTD_first_symbol_of_derivable_marked_effect_def)
    apply(clarsimp)
    apply(rename_tac d)(*strict*)
    apply(subgoal_tac "\<forall>i. case d i of None \<Rightarrow> True | Some (pair e c) \<Rightarrow> setA (cfg_conf c) \<subseteq> cfg_nonterminals G'")
     apply(rename_tac d)(*strict*)
     apply(rule_tac
      x="d"
      in exI)
     apply(simp add: cfgSTD.derivation_def cfgSTD.derivation_from_def cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def)
     apply(clarsimp)
     apply(rename_tac d i n x)(*strict*)
     apply(erule_tac
      x="i"
      and P="\<lambda>i. case i of 0 \<Rightarrow> case_option False (case_derivation_configuration (\<lambda>a c. case a of None \<Rightarrow> True | Some e \<Rightarrow> False)) (d 0) | Suc i' \<Rightarrow> case_option True (case_derivation_configuration (\<lambda>i1 i2. case_option False (case_derivation_configuration (\<lambda>i'1 i'2. case i1 of None \<Rightarrow> False | Some i1v \<Rightarrow> cfgSTD_step_relation G i'2 i1v i2)) (d i'))) (d i)"
      in allE)
     apply(rename_tac d i n x)(*strict*)
     apply(case_tac i)
      apply(rename_tac d i n x)(*strict*)
      apply(clarsimp)
     apply(rename_tac d i n x nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n x nat)(*strict*)
     apply(case_tac "d (Suc nat)")
      apply(rename_tac d n x nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac d n x nat a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac d n x nat a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n x nat option b)(*strict*)
     apply(case_tac "d nat")
      apply(rename_tac d n x nat option b)(*strict*)
      apply(clarsimp)
     apply(rename_tac d n x nat option b a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac d n x nat option b a optiona ba)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n x nat option b optiona ba)(*strict*)
     apply(case_tac option)
      apply(rename_tac d n x nat option b optiona ba)(*strict*)
      apply(clarsimp)
     apply(rename_tac d n x nat option b optiona ba a)(*strict*)
     apply(clarsimp)
     apply(rename_tac d n x nat b optiona ba a)(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac d n x nat b optiona ba a l r)(*strict*)
     apply(simp add: F_CFG_EB_def)
     apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
      apply(rename_tac d n x nat b optiona ba a l r)(*strict*)
      apply(clarsimp)
      apply(rule conjI)
       apply(rename_tac d n x nat b optiona ba a l r)(*strict*)
       apply(erule_tac
      x="nat"
      in allE)
       apply(clarsimp)
       apply(subgoal_tac "prod_lhs a \<in> setA (l @ teA (prod_lhs a) # r)")
        apply(rename_tac d n x nat b optiona ba a l r)(*strict*)
        apply(force)
       apply(rename_tac d n x nat b optiona ba a l r)(*strict*)
       apply(rule elemInsetA)
      apply(rename_tac d n x nat b optiona ba a l r)(*strict*)
      apply(erule_tac
      x="Suc nat"
      in allE)
      apply(clarsimp)
      apply(rename_tac d n x nat b optiona ba a l r xa)(*strict*)
      apply(rule_tac
      A="setA (l @ prod_rhs a @ r)"
      in set_mp)
       apply(rename_tac d n x nat b optiona ba a l r xa)(*strict*)
       apply(force)
      apply(rename_tac d n x nat b optiona ba a l r xa)(*strict*)
      apply(simp only: concat_asso setAConcat)
      apply(force)
     apply(rename_tac d n x nat b optiona ba a l r)(*strict*)
     apply(clarsimp)
    apply(rename_tac d)(*strict*)
    apply(rule_tac
      t="cfg_nonterminals G'"
      and s="cfgSTD_Nonblockingness_nonterminals G"
      in subst)
     apply(rename_tac d)(*strict*)
     apply(rule F_CFG_EBSoundA)
      apply(rename_tac d)(*strict*)
      apply(force)
     apply(rename_tac d)(*strict*)
     apply(force)
    apply(rename_tac d)(*strict*)
    apply(clarsimp)
    apply(rename_tac d i)(*strict*)
    apply(case_tac i)
     apply(rename_tac d i)(*strict*)
     apply(clarsimp)
     apply(rename_tac d)(*strict*)
     apply(case_tac "d 0")
      apply(rename_tac d)(*strict*)
      apply(clarsimp)
     apply(rename_tac d a)(*strict*)
     apply(clarsimp)
     apply(case_tac a)
     apply(rename_tac d a option b)(*strict*)
     apply(clarsimp)
     apply(rename_tac d option b x)(*strict*)
     apply(case_tac b)
     apply(rename_tac d option b x cfg_confa)(*strict*)
     apply(rename_tac w')
     apply(rename_tac d option b x w')(*strict*)
     apply(subgoal_tac "w=w'")
      apply(rename_tac d option b x w')(*strict*)
      prefer 2
      apply(simp add: cfgSTD.derivation_def cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def)
     apply(rename_tac d option b x w')(*strict*)
     apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
     apply(rule conjI)
      apply(rename_tac d option b x w')(*strict*)
      apply(clarsimp)
      apply(rename_tac d option x)(*strict*)
      apply(force)
     apply(rename_tac d option b x w')(*strict*)
     apply(clarsimp)
     apply(rename_tac d option x)(*strict*)
     apply(subgoal_tac "\<exists>w1 w2. w1@[teA x]@w2=w")
      apply(rename_tac d option x)(*strict*)
      apply(clarsimp)
      apply(rename_tac d option x w1 w2)(*strict*)
      apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = teA x#w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = [] ")
       apply(rename_tac d option x w1 w2)(*strict*)
       prefer 2
       apply(rule derivationCanBeDecomposed)
       apply(blast)
      apply(rename_tac d option x w1 w2)(*strict*)
      apply(clarsimp)
      apply(rename_tac d option x w1 w2 d1 d2)(*strict*)
      apply(rename_tac w2'')
      apply(rename_tac d option x w1 w2 d1 w2'')(*strict*)
      apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = [teA x]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = []")
       apply(rename_tac d option x w1 w2 d1 w2'')(*strict*)
       prefer 2
       apply(rule derivationCanBeDecomposed)
       apply(clarsimp)
       apply(blast)
      apply(rename_tac d option x w1 w2 d1 w2'')(*strict*)
      apply(clarsimp)
      apply(rename_tac d option x w1 w2 d1 w2'' d1a d2)(*strict*)
      apply(rule_tac
      x="d1a"
      in exI)
      apply(rule_tac
      x="[]"
      in exI)
      apply(clarsimp)
     apply(rename_tac d option x)(*strict*)
     apply(rule setA_decomp)
     apply(force)
    apply(rename_tac d i nat)(*strict*)
    apply(case_tac "d i")
     apply(rename_tac d i nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac d i nat a)(*strict*)
    apply(case_tac a)
    apply(rename_tac d i nat a option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac d nat option b x)(*strict*)
    apply(case_tac b)
    apply(rename_tac d nat option b x cfg_confa)(*strict*)
    apply(clarsimp)
    apply(rename_tac d nat option x cfg_conf)(*strict*)
    apply(rename_tac v)
    apply(rename_tac d nat option x v)(*strict*)
    apply(subgoal_tac "\<exists>w1 w2. w1@[teA x]@w2=v")
     apply(rename_tac d nat option x v)(*strict*)
     prefer 2
     apply(rule setA_decomp)
     apply(force)
    apply(rename_tac d nat option x v)(*strict*)
    apply(clarsimp)
    apply(rename_tac d nat option x w1 w2)(*strict*)
    apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_drop d (Suc nat)) {pair None \<lparr>cfg_conf = w1 @ teA x # w2\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = []\<rparr>}")
     apply(rename_tac d nat option x w1 w2)(*strict*)
     apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = teA x#w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = [] ")
      apply(rename_tac d nat option x w1 w2)(*strict*)
      prefer 2
      apply(rule derivationCanBeDecomposed)
      apply(blast)
     apply(rename_tac d nat option x w1 w2)(*strict*)
     apply(clarsimp)
     apply(rename_tac d nat option x w1 w2 d1 d2)(*strict*)
     apply(rename_tac w2'')
     apply(rename_tac d nat option x w1 w2 d1 w2'')(*strict*)
     apply(subgoal_tac " \<exists>d1 d2 w1' w2'. cfgSTD.derivation_from_to G d1 {pair None \<lparr>cfg_conf = [teA x]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w1'\<rparr>} \<and> cfgSTD.derivation_from_to G d2 {pair None \<lparr>cfg_conf = w2\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2'\<rparr>} \<and> w1' @ w2' = []")
      apply(rename_tac d nat option x w1 w2 d1 w2'')(*strict*)
      prefer 2
      apply(rule derivationCanBeDecomposed)
      apply(clarsimp)
      apply(blast)
     apply(rename_tac d nat option x w1 w2 d1 w2'')(*strict*)
     apply(clarsimp)
     apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
     apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
     apply(rule conjI)
      apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
      apply(rule_tac
      A="setA (w1@teA x#w2)"
      in set_mp)
       apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
       apply(rule_tac
      w="w"
      and d="d"
      and i="0"
      and j="Suc nat"
      in staysInNonterms2)
            apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
            apply(force)
           apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
           apply(force)
          apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
          apply(force)
         apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
         apply(rule cfgSTD.from_to_is_der)
         apply(force)
        apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
        apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def)
        apply(clarsimp)
        apply(case_tac "d 0")
         apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
         apply(force)
        apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2 a)(*strict*)
        apply(force)
       apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
       apply(force)
      apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
      apply(force)
     apply(rename_tac d nat option x w1 w2 d1 w2'' d1a d2)(*strict*)
     apply(rule_tac
      x="d1a"
      in exI)
     apply(rule_tac
      x="[]"
      in exI)
     apply(clarsimp)
    apply(rename_tac d nat option x w1 w2)(*strict*)
    apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
     apply(rename_tac d nat option x w1 w2)(*strict*)
     prefer 2
     apply(simp add: cfgSTD.derivation_def cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def)
     apply(erule conjE)+
     apply(erule exE)+
     apply(rename_tac d nat option x w1 w2 n)(*strict*)
     apply(rule_tac
      x="n"
      in exI)
     apply(simp add: maximum_of_domain_def)
     apply(clarsimp)
    apply(rename_tac d nat option x w1 w2)(*strict*)
    apply(clarsimp)
    apply(rename_tac d nat option x w1 w2 n)(*strict*)
    apply(subgoal_tac "n\<ge>Suc nat")
     apply(rename_tac d nat option x w1 w2 n)(*strict*)
     prefer 2
     apply(case_tac "Suc nat > n")
      apply(rename_tac d nat option x w1 w2 n)(*strict*)
      apply(subgoal_tac "\<forall>m>n. d m = None")
       apply(rename_tac d nat option x w1 w2 n)(*strict*)
       prefer 2
       apply(rule cfgSTD.noSomeAfterMaxDom)
        apply(rename_tac d nat option x w1 w2 n)(*strict*)
        apply(rule cfgSTD.from_to_is_der)
        apply(blast)
       apply(rename_tac d nat option x w1 w2 n)(*strict*)
       apply(blast)
      apply(rename_tac d nat option x w1 w2 n)(*strict*)
      apply(force)
     apply(rename_tac d nat option x w1 w2 n)(*strict*)
     apply(force)
    apply(rename_tac d nat option x w1 w2 n)(*strict*)
    apply(rule_tac
      m="n-(Suc nat)"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
       apply(rename_tac d nat option x w1 w2 n)(*strict*)
       apply(force)
      apply(rename_tac d nat option x w1 w2 n)(*strict*)
      apply(force)
     apply(rename_tac d nat option x w1 w2 n)(*strict*)
     apply(force)
    apply(rename_tac d nat option x w1 w2 n)(*strict*)
    apply(clarsimp)
    apply(rename_tac d nat option x w1 w2)(*strict*)
    apply(subgoal_tac "w1@teA x#w2=[]")
     apply(rename_tac d nat option x w1 w2)(*strict*)
     apply(force)
    apply(rename_tac d nat option x w1 w2)(*strict*)
    apply(subgoal_tac "cfgSTD.derivation_to G d {y. \<exists>x. y = pair x \<lparr>cfg_conf = []\<rparr>}")
     apply(rename_tac d nat option x w1 w2)(*strict*)
     prefer 2
     apply(simp add: cfgSTD.derivation_def cfgSTD.derivation_from_to_def cfgSTD.derivation_to_def)
    apply(rename_tac d nat option x w1 w2)(*strict*)
    apply(simp add: cfgSTD.derivation_to_def)
    apply(clarsimp)
    apply(rename_tac d nat option x w1 w2 n xa)(*strict*)
    apply(subgoal_tac "n=Suc nat")
     apply(rename_tac d nat option x w1 w2 n xa)(*strict*)
     prefer 2
     apply(rule cfgSTD.maximum_of_domainUnique)
       apply(rename_tac d nat option x w1 w2 n xa)(*strict*)
       apply(force)
      apply(rename_tac d nat option x w1 w2 n xa)(*strict*)
      apply(force)
     apply(rename_tac d nat option x w1 w2 n xa)(*strict*)
     apply(simp add: maximum_of_domain_def)
    apply(rename_tac d nat option x w1 w2 n xa)(*strict*)
    apply(force)
   apply(rename_tac x a)(*strict*)
   prefer 2
   apply(simp add: cfgSTD_first_symbol_of_derivable_marked_effect_def)
   apply(rule conjI)
    apply(clarsimp)
    apply(rename_tac v d w')(*strict*)
    apply(rule conjI)
     apply(rename_tac v d w')(*strict*)
     apply(rule_tac
      A="cfg_events G'"
      in set_mp)
      apply(rename_tac v d w')(*strict*)
      apply(rule cfg_sub_inherits_cfg_events)
      apply(rule F_CFG_EB_makes_cfg_sub)
       apply(rename_tac v d w')(*strict*)
       apply(blast)
      apply(rename_tac v d w')(*strict*)
      apply(blast)
     apply(rename_tac v d w')(*strict*)
     apply(blast)
    apply(rename_tac v d w')(*strict*)
    apply(rule_tac
      x="d"
      in exI)
    apply(rule_tac
      x="w'"
      in exI)
    apply(rule conjI)
     apply(rename_tac v d w')(*strict*)
     apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
      apply(rename_tac v d w')(*strict*)
      apply(erule exE)+
      apply(rename_tac v d w' n)(*strict*)
      apply(rule_tac
      ?G1.0="G'"
      in cfg_subInheritsDerivation)
        apply(rename_tac v d w' n)(*strict*)
        apply(rule F_CFG_EB_makes_cfg_sub)
         apply(rename_tac v d w' n)(*strict*)
         apply(blast)
        apply(rename_tac v d w' n)(*strict*)
        apply(blast)
       apply(rename_tac v d w' n)(*strict*)
       apply(blast)
      apply(rename_tac v d w' n)(*strict*)
      apply(blast)
     apply(rename_tac v d w')(*strict*)
     apply(rule cfgSTD.to_has_maximum_of_domain)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac v d w')(*strict*)
    apply(blast)
   apply(clarsimp)
   apply(rename_tac d)(*strict*)
   apply(erule_tac
      x="d"
      in allE)
   apply(subgoal_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = []\<rparr>}")
    apply(rename_tac d)(*strict*)
    apply(force)
   apply(rename_tac d)(*strict*)
   apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
    apply(rename_tac d)(*strict*)
    apply(erule exE)+
    apply(rename_tac d n)(*strict*)
    apply(rule_tac
      ?G1.0="G'"
      in cfg_subInheritsDerivation)
      apply(rename_tac d n)(*strict*)
      apply(rule F_CFG_EB_makes_cfg_sub)
       apply(rename_tac d n)(*strict*)
       apply(blast)
      apply(rename_tac d n)(*strict*)
      apply(blast)
     apply(rename_tac d n)(*strict*)
     apply(blast)
    apply(rename_tac d n)(*strict*)
    apply(blast)
   apply(rename_tac d)(*strict*)
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac x a)(*strict*)
  apply(simp add: cfgSTD_first_symbol_of_derivable_marked_effect_def)
  apply(clarsimp)
  apply(rename_tac a d w')(*strict*)
  apply(rule conjI)
   apply(rename_tac a d w')(*strict*)
   apply(subgoal_tac "a\<in> cfg_events G'")
    apply(rename_tac a d w')(*strict*)
    apply(force)
   apply(rename_tac a d w')(*strict*)
   apply(rule_tac
      t="cfg_events G'"
      and s="cfg_events G"
      in ssubst)
    apply(rename_tac a d w')(*strict*)
    apply(rule sym)
    apply(rule F_CFG_EBSound4)
     apply(rename_tac a d w')(*strict*)
     apply(blast)
    apply(rename_tac a d w')(*strict*)
    apply(blast)
   apply(rename_tac a d w')(*strict*)
   apply(blast)
  apply(rename_tac a d w')(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule_tac
      x="w'"
      in exI)
  apply(auto)
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   apply(rename_tac a d w')(*strict*)
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(blast)
  apply(rename_tac a d w')(*strict*)
  apply(erule exE)+
  apply(rename_tac a d w' n)(*strict*)
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2. maximum_of_domain d n \<and> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>} \<and> setA w2 = {} \<and> setB w1 \<subseteq> cfg_events G \<and> setA w1 \<subseteq> F_CFG_EB__fp G {} \<longrightarrow> cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>}")
   apply(rename_tac a d w' n)(*strict*)
   apply(erule_tac
      x="n"
      in allE)
   apply(erule_tac
      x="d"
      in allE)
   apply(erule_tac
      x="w"
      in allE)
   apply(erule_tac
      x="teB a#w'"
      in allE)
   apply(erule impE)
    apply(rename_tac a d w' n)(*strict*)
    apply(rule conjI)
     apply(rename_tac a d w' n)(*strict*)
     apply(force)
    apply(rename_tac a d w' n)(*strict*)
    apply(rule conjI)
     apply(rename_tac a d w' n)(*strict*)
     apply(force)
    apply(rename_tac a d w' n)(*strict*)
    apply(rule conjI)
     apply(rename_tac a d w' n)(*strict*)
     apply(force)
    apply(rename_tac a d w' n)(*strict*)
    apply(rule conjI)
     apply(rename_tac a d w' n)(*strict*)
     apply(force)
    apply(rename_tac a d w' n)(*strict*)
    apply(rule_tac
      s="cfg_nonterminals G'"
      and t="F_CFG_EB__fp G {}"
      in ssubst)
     apply(rename_tac a d w' n)(*strict*)
     apply(simp add: F_CFG_EB_def)
     apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
      apply(rename_tac a d w' n)(*strict*)
      apply(force)
     apply(rename_tac a d w' n)(*strict*)
     apply(force)
    apply(rename_tac a d w' n)(*strict*)
    apply(force)
   apply(rename_tac a d w' n)(*strict*)
   apply(force)
  apply(rename_tac a d w' n)(*strict*)
  apply(rule allI)
  apply(rename_tac a d w' n na)(*strict*)
  apply(rule nat.induct)
   apply(rename_tac a d w' n na)(*strict*)
   apply(clarsimp)
   apply(rename_tac a d w' n da w1 w2)(*strict*)
   apply(subgoal_tac "da 0 = Some (pair None \<lparr>cfg_conf = w1\<rparr>)")
    apply(rename_tac a d w' n da w1 w2)(*strict*)
    apply(subgoal_tac "\<forall>n. n>0 \<longrightarrow> da n = None")
     apply(rename_tac a d w' n da w1 w2)(*strict*)
     apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
     apply(clarsimp)
     apply(rename_tac a d w' n da w1 w2 i na xa nb x)(*strict*)
     apply(case_tac i)
      apply(rename_tac a d w' n da w1 w2 i na xa nb x)(*strict*)
      apply(clarsimp)
     apply(rename_tac a d w' n da w1 w2 i na xa nb x nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac a d w' n da w1 w2)(*strict*)
    apply(rule cfgSTD.noSomeAfterMaxDom)
     apply(rename_tac a d w' n da w1 w2)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac a d w' n da w1 w2)(*strict*)
    apply(blast)
   apply(rename_tac a d w' n da w1 w2)(*strict*)
   apply(rule cfgSTD.derivation_from_starts_from2)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac a d w' n na nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac a d w' n nat da w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1\<rparr>}. da 0 = Some x")
   apply(rename_tac a d w' n nat da w1 w2)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac a d w' n nat da w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>e c. da (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac a d w' n nat da w1 w2)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac a d w' n nat da w1 w2)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac a d w' n nat da w1 w2)(*strict*)
    apply(blast)
   apply(rename_tac a d w' n nat da w1 w2)(*strict*)
   apply(arith)
  apply(rename_tac a d w' n nat da w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac a d w' n nat da w1 w2 e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac a d w' n nat da w1 w2 e c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac a d w' n nat da w1 w2 e cfg_conf)(*strict*)
  apply(rename_tac w1')
  apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
  apply(erule_tac
      x="derivation_drop da (Suc 0)"
      in allE)
  apply(erule_tac
      x="w1'"
      in allE)
  apply(erule_tac
      x="w2"
      in allE)
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = teB a # w'\<rparr>}")
  apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
  apply(thin_tac "a \<in> cfg_events G")
  apply(thin_tac "setA w \<subseteq> cfg_nonterminals G'")
  apply(thin_tac "setB w \<subseteq> cfg_events G")
  apply(thin_tac "maximum_of_domain d n")
  apply(subgoal_tac "maximum_of_domain (derivation_drop da (Suc 0)) nat")
   apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
   apply(subgoal_tac "cfgSTD.derivation_from_to G (derivation_drop da (Suc 0)) {pair None \<lparr>cfg_conf = w1'\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>}")
    apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
    apply(subgoal_tac "setA w2 = {}")
     apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
     apply(subgoal_tac "setB w1' \<subseteq> cfg_events G")
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      apply(subgoal_tac "setA w1' \<subseteq> F_CFG_EB__fp G {}")
       apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
       apply(erule impE)
    (*
  G:da:Suc nat:w1 \<rightarrow> w1' \<longrightarrow>* w2
  setB w1 \<subseteq> cfg_events G
  setA w1 \<subseteq> F_CFG_EB__fp G {}
  setA w' = {}
  setA w2 = {}
*)
        apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
        apply(force)
       apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
       prefer 6
       apply(rule derivation_drop_preserves_generates_maximum_of_domain)
       apply(blast)
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      prefer 5
      apply(rule_tac
      m = "nat"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
         apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
         apply(blast)
        apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
        apply(rule_tac
      s = "Suc nat"
      in ssubst)
         apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
         apply(arith)
        apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
        apply(blast)
       apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
       apply(blast)
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      apply(rule impI)
      apply(subgoal_tac "\<exists>e. da (Suc 0) = Some (pair e \<lparr>cfg_conf = w2\<rparr>)")
       apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
       apply(clarsimp)
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      apply(rule cfgSTD.reachesToAtMaxDom)
       apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
       apply(rule cfgSTD.from_to_is_to)
       apply(blast)
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      apply(blast)
     apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
     prefer 4
     apply(clarsimp)
    apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
    prefer 3
    apply(rule_tac
      e="e"
      and w="w1"
      in staysInSigma)
       apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
       apply(blast)
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      apply(blast)
     apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
     apply(rule cfgSTD.position_change_due_to_step_relation)
       apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
       apply(rule cfgSTD.from_to_is_der)
       apply(blast)
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      apply(blast)
     apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
     apply(blast)
    apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
    apply(rule inProdsFromcfgSTD_step_relation)
    apply(rule cfgSTD.position_change_due_to_step_relation)
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
     apply(blast)
    apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
    apply(blast)
    (*
  G:da:Suc nat:w1 \<rightarrow> w1' \<longrightarrow>* w2
  setB w1 \<subseteq> cfg_events G
  setA w1 \<subseteq> F_CFG_EB__fp G {}
  setA w' = {}
  setA w2 = {}
*)
   apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
   prefer 2
   apply(rule F_CFG_EBSound0_1)
      apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
      apply(blast)
     apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
     apply(blast)
    apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
    apply(blast)
   apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
   apply(blast)
    (*
  G:da:Suc nat:w1 \<rightarrow> w1' \<longrightarrow>* w2
  setB w1 \<subseteq> cfg_events G
  setA w1 \<subseteq> F_CFG_EB__fp G {}
  setA w' = {}
  setA w2 = {}
  setB w1' \<subseteq> cfg_events G
  setA w1' \<subseteq> F_CFG_EB__fp G {}
  G':da[skip1]:w1'\<longrightarrow>*w2
  \<Longrightarrow> G':da:w1\<longrightarrow>*w2
*)
  apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
  apply(subgoal_tac "\<forall>n. n>(Suc nat) \<longrightarrow> da n = None")
   apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
   prefer 2
   apply(rule cfgSTD.noSomeAfterMaxDom)
    apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
    apply(rule cfgSTD.from_to_is_der)
    apply(blast)
   apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
   apply(blast)
  apply(rename_tac a d w' n nat da w1 w2 e w1')(*strict*)
  apply(simp (no_asm) add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
  apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
  apply(clarsimp)
  apply(rule conjI)
   apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' i)(*strict*)
   apply(case_tac i)
    apply(rename_tac w' nat da w1 w2 e w1' i)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' i nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' nata)(*strict*)
   apply(case_tac "da (Suc nata)")
    apply(rename_tac w' nat da w1 w2 e w1' nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' nata a)(*strict*)
   apply(clarsimp)
   apply(case_tac a)
   apply(rename_tac w' nat da w1 w2 e w1' nata a option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' nata option b)(*strict*)
   apply(case_tac nata)
    apply(rename_tac w' nat da w1 w2 e w1' nata option b)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
    apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = w1'\<rparr>")
     apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
     apply(simp add: cfgSTD_step_relation_def)
     apply(clarsimp)
     apply(rename_tac w' nat da w2 e l r)(*strict*)
     apply(simp add: F_CFG_EB_def)
     apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
      apply(rename_tac w' nat da w2 e l r)(*strict*)
      apply(clarsimp)
      prefer 2
      apply(clarsimp)
     apply(rename_tac w' nat da w2 e l r)(*strict*)
     apply(simp only: setAConcat concat_asso)
     apply(clarsimp)
    apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
    apply(rule cfgSTD.position_change_due_to_step_relation)
      apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
     apply(blast)
    apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
    apply(blast)
   apply(rename_tac w' nat da w1 w2 e w1' nata option b natb)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
   apply(subgoal_tac "\<exists>e c. da (Suc natb) = Some (pair (Some e) c)")
    apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
    prefer 2
    apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
      apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
     apply(blast)
    apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
    apply(rule_tac
      j="Suc (Suc natb)"
      in le_trans)
     apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
     apply(arith)
    apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
    apply(rule cfgSTD.allPreMaxDomSome_prime)
      apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
     apply(blast)
    apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
    apply(blast)
   apply(rename_tac w' nat da w1 w2 e w1' option b natb)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' option b natb ea c)(*strict*)
   apply(case_tac option)
    apply(rename_tac w' nat da w1 w2 e w1' option b natb ea c)(*strict*)
    apply(clarsimp)
    apply(rename_tac w' nat da w1 w2 e w1' b natb ea c)(*strict*)
    apply(rule cfgSTD.derivation_Always_PreEdge_prime)
     apply(rename_tac w' nat da w1 w2 e w1' b natb ea c)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac w' nat da w1 w2 e w1' b natb ea c)(*strict*)
    apply(blast)
   apply(rename_tac w' nat da w1 w2 e w1' option b natb ea c a)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' b natb ea c a)(*strict*)
   apply(case_tac c)
   apply(rename_tac w' nat da w1 w2 e w1' b natb ea c a cfg_conf)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' b natb ea a cfg_conf)(*strict*)
   apply(case_tac b)
   apply(rename_tac w' nat da w1 w2 e w1' b natb ea a cfg_conf cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' natb ea a cfg_conf cfg_confa)(*strict*)
   apply(case_tac a)
   apply(rename_tac w' nat da w1 w2 e w1' natb ea a cfg_conf cfg_confa prod_lhs prod_rhs)(*strict*)
   apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' natb ea cfg_conf cfg_confa prod_lhs prod_rhs)(*strict*)
   apply(rename_tac v1 v2 A w)
   apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
   apply(subgoal_tac "setA v1 \<subseteq> F_CFG_EB__fp G {}")
    apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
    apply(subgoal_tac "setA v2 \<subseteq> F_CFG_EB__fp G {}")
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = v1\<rparr> \<lparr>prod_lhs = A, prod_rhs = w\<rparr> \<lparr>cfg_conf = v2\<rparr>")
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(simp add: cfgSTD_step_relation_def)
      apply(clarsimp)
      apply(rename_tac w' nat da w1 w2 e w1' natb ea A w l r)(*strict*)
      apply(simp add: F_CFG_EB_def)
      apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
       apply(rename_tac w' nat da w1 w2 e w1' natb ea A w l r)(*strict*)
       apply(clarsimp)
       prefer 2
       apply(clarsimp)
      apply(rename_tac w' nat da w1 w2 e w1' natb ea A w l r)(*strict*)
      apply(simp only: setAConcat concat_asso)
      apply(clarsimp)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(rule cfgSTD.position_change_due_to_step_relation)
       apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
       apply(rule cfgSTD.from_to_is_der)
       apply(blast)
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(blast)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(blast)
    apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
    apply(rule_tac
      d="derivation_drop da (Suc (Suc natb))"
      in F_CFG_EBSound0_1)
       apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
       apply(blast)
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(blast)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(subgoal_tac "\<exists>x. x+Suc(Suc natb)=Suc nat")
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(erule exE)
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
      apply(rule_tac
      m = "x"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
         apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
         apply(blast)
        apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
        apply(rule_tac
      s = "Suc nat"
      in ssubst)
         apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
         apply(arith)
        apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
        apply(blast)
       apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
       apply(blast)
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
      apply(clarsimp)
      apply(rename_tac w' da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(subgoal_tac "\<exists>e. da (Suc (Suc natb)) = Some (pair e \<lparr>cfg_conf = w2\<rparr>)")
       apply(rename_tac w' da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
       apply(erule exE)
       apply(rename_tac w' da w1 w2 e w1' natb ea v1 v2 A w eb)(*strict*)
       apply(clarsimp)
      apply(rename_tac w' da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(rule cfgSTD.reachesToAtMaxDom)
       apply(rename_tac w' da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
       apply(rule cfgSTD.from_to_is_to)
       apply(blast)
      apply(rename_tac w' da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(clarsimp)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(subgoal_tac "Suc (Suc natb) \<le> Suc nat")
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply (metis add_Suc less_iff_Suc_add add.commute not_less_eq_eq trivNat)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(case_tac "Suc (Suc natb) \<le> Suc nat")
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(clarsimp)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
    apply(blast)
   apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
   apply(rule_tac
      d="derivation_drop da (Suc natb)"
      in F_CFG_EBSound0_1)
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
      apply(blast)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(blast)
    apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
    apply(subgoal_tac "\<exists>x. x+Suc natb=Suc nat")
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(erule exE)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
     apply(rule_tac
      m = "x"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
        apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
        apply(blast)
       apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
       apply(rule_tac
      s = "Suc nat"
      in ssubst)
        apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
        apply(arith)
       apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
       apply(blast)
      apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
      apply(blast)
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w x)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
    apply(subgoal_tac "Suc natb \<le> Suc nat")
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply (metis add_Suc_right less_eq_Suc_le_raw less_iff_Suc_add add.commute)
    apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
    apply(case_tac "Suc natb \<le> Suc nat")
     apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
     apply(clarsimp)
    apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
    apply(clarsimp)
   apply(rename_tac w' nat da w1 w2 e w1' natb ea v1 v2 A w)(*strict*)
   apply(blast)
  apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
  apply(rule_tac
      x="Suc nat"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e. da (Suc nat) = Some (pair e \<lparr>cfg_conf = w2\<rparr>)")
   apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
   apply(erule exE)
   apply(rename_tac w' nat da w1 w2 e w1' ea)(*strict*)
   prefer 2
   apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac w' nat da w1 w2 e w1')(*strict*)
   apply(clarsimp)
  apply(rename_tac w' nat da w1 w2 e w1' ea)(*strict*)
  apply(force)
  done

lemma F_CFG_EB_F_CFG_EB__fp_invariant_02_unfold: "
  F_CFG_EB__fp_valid_input G {}
  \<Longrightarrow> F_CFG_EB__fp G {} \<subseteq> cfg_nonterminals G"
  apply(rule F_CFG_EB__fp_Meta_Lift)
    apply(blast)
   apply(rename_tac Ga N)(*strict*)
   defer
   apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
   apply(rename_tac G N)(*strict*)
   apply(rename_tac G N)
   apply(clarsimp)
   apply(rename_tac G N x)(*strict*)
   apply(subgoal_tac "F_CFG_EB__fp G N=N")
    apply(rename_tac G N x)(*strict*)
    apply(clarsimp)
    apply(simp add: F_CFG_EB__fp_invariants_def F_CFG_EB__fp_invariant_02_def)
    apply(force)
   apply(rename_tac G N x)(*strict*)
   apply(rule_tac
      s="(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      and t="F_CFG_EB__fp G N"
      in ssubst)
    apply(rename_tac G N x)(*strict*)
    apply(rule F_CFG_EB__fp.psimps)
    apply(rule F_CFG_EB__fp_termination)
    apply(blast)
   apply(rename_tac G N x)(*strict*)
   apply(clarsimp)
  apply(rename_tac Ga N)(*strict*)
  apply(thin_tac "F_CFG_EB__fp_valid_input G {}")
  apply(rename_tac G N)(*strict*)
  apply(rule_tac
      s = "F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      in ssubst)
   apply(rename_tac G N)(*strict*)
   apply(case_tac "N = F_CFG_EB__fp_one G N")
    apply(rename_tac G N)(*strict*)
    apply(clarsimp)
   apply(rename_tac G N)(*strict*)
   apply(rule_tac
      P = "\<lambda>x. x = F_CFG_EB__fp G (F_CFG_EB__fp_one G N)"
      and t = "F_CFG_EB__fp G N"
      and s = "(if F_CFG_EB__fp_one G N = N then N else F_CFG_EB__fp G (F_CFG_EB__fp_one G N))"
      in ssubst)
    apply(rename_tac G N)(*strict*)
    apply(rule F_CFG_EB__fp.psimps)
    apply(rule F_CFG_EB__fp_termination)
    apply(blast)
   apply(rename_tac G N)(*strict*)
   apply(clarsimp)
  apply(rename_tac G N)(*strict*)
  apply(clarsimp)
  done

lemma F_CFG_EBSound3: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> valid_cfg G'"
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   apply(auto)
  apply(simp (no_asm) add: valid_cfg_def)
  apply(auto)
     apply(simp add: valid_cfg_def)
    apply(rule_tac
      B="cfg_nonterminals G"
      in finite_subset)
     apply(rule F_CFG_EB_F_CFG_EB__fp_invariant_02_unfold)
     apply(simp add: F_CFG_EB__fp_valid_input_def)
    apply(simp add: valid_cfg_def)+
  apply(rename_tac e x)(*strict*)
  apply(auto)
  done

lemma F_CFG_EBSound5: "
  valid_cfg G
  \<Longrightarrow> A \<in> F_CFG_EB__fp G {}
  \<Longrightarrow> \<exists>x. prod_lhs x = A \<and> x \<in> cfg_productions G \<and> setA (prod_rhs x) \<subseteq> F_CFG_EB__fp G {}"
  apply(subgoal_tac "\<forall>A\<in> (F_CFG_EB__fp G {}). \<exists>e. e \<in> cfg_productions G \<and> prod_lhs e \<in> (F_CFG_EB__fp G {}) \<and> setA (prod_rhs e) \<subseteq> (F_CFG_EB__fp G {}) \<and> prod_lhs e = A")
   prefer 2
   apply(rule F_CFG_EB_F_CFG_EB__fp_invariant_03_unfold)
   apply(simp add: F_CFG_EB__fp_valid_input_def)
  apply(blast)
  done

lemma everyConfHasOnlyFromRNPPGrammar: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> setA w1 \<subseteq> cfg_nonterminals G'
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w2\<rparr>}
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> maximum_of_domain d n
  \<Longrightarrow> d i = Some (pair e \<lparr>cfg_conf = w\<rparr>)
  \<Longrightarrow> setA w \<subseteq> cfg_nonterminals G'"
  apply(rule_tac
      d="derivation_drop d i"
      in F_CFG_EBSound0_1)
     apply(blast)
    apply(simp add: F_CFG_EB_def)
    apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
     apply(clarsimp)
    apply(clarsimp)
   prefer 2
   apply(blast)
  apply(rule_tac
      m = "n-i"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
     apply(blast)
    apply(rule_tac
      s = "n"
      in ssubst)
     apply(subgoal_tac "n\<ge>i")
      apply(arith)
     apply(case_tac "i\<le>n")
      apply(clarsimp)
     apply(clarsimp)
     apply(subgoal_tac "\<forall>m>n. d m = None")
      apply(clarsimp)
     apply(rule cfgSTD.noSomeAfterMaxDom)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(blast)
    apply(blast)
   apply(blast)
  apply(clarsimp)
  apply(subgoal_tac "n=i")
   apply(clarsimp)
   apply(subgoal_tac "\<exists>e. d i = Some (pair e \<lparr>cfg_conf = w2\<rparr>)")
    apply(erule exE)
    apply(rename_tac ea)(*strict*)
    apply(clarsimp)
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(clarsimp)
  apply(case_tac "n=i")
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "\<forall>m>n. d m = None")
   apply(clarsimp)
  apply(rule cfgSTD.noSomeAfterMaxDom)
   apply(rule cfgSTD.from_to_is_der)
   apply(blast)
  apply(blast)
  done

lemma canMimik: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> setA w1 \<subseteq> cfg_nonterminals G'
  \<Longrightarrow> setB w1 \<subseteq> cfg_events G'
  \<Longrightarrow> setA w2 = {}
  \<Longrightarrow> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w2\<rparr>}
  \<Longrightarrow> cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>}"
  apply(subgoal_tac "\<exists>n. maximum_of_domain d n")
   prefer 2
   apply(rule cfgSTD.to_has_maximum_of_domain)
   apply(rule cfgSTD.from_to_is_to)
   apply(force)
  apply(erule exE)+
  apply(rename_tac n)(*strict*)
  apply(rename_tac nb)
  apply(rename_tac nb)(*strict*)
  apply(subgoal_tac " \<forall>n. \<forall>d w1 w2. setA w1 \<subseteq> cfg_nonterminals G' \<and> setB w1 \<subseteq> cfg_events G' \<and> setA w2 = {} \<and> cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w2\<rparr>} \<and> maximum_of_domain d n \<longrightarrow> cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w2\<rparr>}")
   apply(rename_tac nb)(*strict*)
   apply(clarsimp)
  apply(rename_tac nb)(*strict*)
  apply(thin_tac "setA w1 \<subseteq> cfg_nonterminals G'")
  apply(thin_tac "setB w1 \<subseteq> cfg_events G'")
  apply(thin_tac "setA w2 = {}")
  apply(thin_tac "cfgSTD.derivation_from_to G d {pair None \<lparr>cfg_conf = w1\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w2\<rparr>}")
  apply(thin_tac "maximum_of_domain d nb")
  apply(rule allI)
  apply(rename_tac nb n)(*strict*)
  apply(rule nat_induct)
   apply(rename_tac nb n)(*strict*)
   apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(subgoal_tac "\<forall>m>0. d m = None")
    apply(rename_tac d w1 w2)(*strict*)
    apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_def)
    apply(clarsimp)
    apply(rename_tac d w1 w2 i n x)(*strict*)
    apply(case_tac i)
     apply(rename_tac d w1 w2 i n x)(*strict*)
     apply(clarsimp)
     apply(rename_tac d w1 w2 n x)(*strict*)
     apply(case_tac "d 0")
      apply(rename_tac d w1 w2 n x)(*strict*)
      apply(clarsimp)
     apply(rename_tac d w1 w2 n x a)(*strict*)
     apply(clarsimp)
    apply(rename_tac d w1 w2 i n x nat)(*strict*)
    apply(clarsimp)
   apply(rename_tac d w1 w2)(*strict*)
   apply(rule cfgSTD.noSomeAfterMaxDom)
    apply(rename_tac d w1 w2)(*strict*)
    apply(rule cfgSTD.from_to_is_der)
    apply(blast)
   apply(rename_tac d w1 w2)(*strict*)
   apply(clarsimp)
  apply(rename_tac nb n na)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2)(*strict*)
  apply(subgoal_tac "\<exists>e c. d (Suc 0) = Some (pair (Some e) c)")
   apply(rename_tac na d w1 w2)(*strict*)
   prefer 2
   apply(rule cfgSTD.some_position_has_details_before_max_dom_after_0)
     apply(rename_tac na d w1 w2)(*strict*)
     apply(rule cfgSTD.from_to_is_der)
     apply(blast)
    apply(rename_tac na d w1 w2)(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2)(*strict*)
   apply(arith)
  apply(rename_tac na d w1 w2)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac na d w1 w2 e c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac na d w1 w2 e cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac na d w1 w2 e w)(*strict*)
  apply(subgoal_tac "setA w \<subseteq> cfg_nonterminals G'")
   apply(rename_tac na d w1 w2 e w)(*strict*)
   prefer 2
   apply(rule everyConfHasOnlyFromRNPPGrammar)
         apply(rename_tac na d w1 w2 e w)(*strict*)
         apply(blast)
        apply(rename_tac na d w1 w2 e w)(*strict*)
        apply(blast)
       apply(rename_tac na d w1 w2 e w)(*strict*)
       apply(blast)
      apply(rename_tac na d w1 w2 e w)(*strict*)
      apply(blast)
     apply(rename_tac na d w1 w2 e w)(*strict*)
     apply(blast)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2 e w)(*strict*)
   apply(blast)
  apply(rename_tac na d w1 w2 e w)(*strict*)
  apply(subgoal_tac "\<exists>x \<in> {pair None \<lparr>cfg_conf = w1\<rparr>}. d 0 = Some x")
   apply(rename_tac na d w1 w2 e w)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_from_starts_from)
   apply(rule cfgSTD.from_to_is_from)
   apply(blast)
  apply(rename_tac na d w1 w2 e w)(*strict*)
  apply(erule_tac
      x="derivation_drop d (Suc 0)"
      in allE)
  apply(erule_tac
      x="w"
      in allE)
  apply(erule_tac
      x="w2"
      in allE)
  apply(erule impE)
   apply(rename_tac na d w1 w2 e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2 e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(rule_tac
      s="cfg_events G"
      and t="cfg_events G'"
      in ssubst)
     apply(rename_tac na d w1 w2 e w)(*strict*)
     apply(simp add: F_CFG_EB_def)
     apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
      apply(rename_tac na d w1 w2 e w)(*strict*)
      apply(force)
     apply(rename_tac na d w1 w2 e w)(*strict*)
     apply(force)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(rule_tac
      d="d"
      and w'="w"
      and w="w1"
      and i="0"
      and j="Suc 0"
      in staysInSigma2)
         apply(rename_tac na d w1 w2 e w)(*strict*)
         apply(blast)
        apply(rename_tac na d w1 w2 e w)(*strict*)
        apply(rule_tac
      B="cfg_nonterminals G'"
      in subset_trans)
         apply(rename_tac na d w1 w2 e w)(*strict*)
         apply(blast)
        apply(rename_tac na d w1 w2 e w)(*strict*)
        apply(rule_tac
      s="F_CFG_EB__fp G {}"
      and t="cfg_nonterminals G'"
      in ssubst)
         apply(rename_tac na d w1 w2 e w)(*strict*)
         apply(simp add: F_CFG_EB_def)
         apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
          apply(rename_tac na d w1 w2 e w)(*strict*)
          apply(force)
         apply(rename_tac na d w1 w2 e w)(*strict*)
         apply(force)
        apply(rename_tac na d w1 w2 e w)(*strict*)
        apply(rule F_CFG_EB_F_CFG_EB__fp_invariant_02_unfold)
        apply(simp add: F_CFG_EB__fp_valid_input_def)
       apply(rename_tac na d w1 w2 e w)(*strict*)
       apply(rule_tac
      t="cfg_events G"
      and s="cfg_events G'"
      in ssubst)
        apply(rename_tac na d w1 w2 e w)(*strict*)
        apply(simp add: F_CFG_EB_def)
        apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
         apply(rename_tac na d w1 w2 e w)(*strict*)
         apply(force)
        apply(rename_tac na d w1 w2 e w)(*strict*)
        apply(force)
       apply(rename_tac na d w1 w2 e w)(*strict*)
       apply(force)
      apply(rename_tac na d w1 w2 e w)(*strict*)
      apply(rule cfgSTD.from_to_is_der)
      apply(blast)
     apply(rename_tac na d w1 w2 e w)(*strict*)
     apply(blast)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(clarsimp)
    apply(blast)
   apply(rename_tac na d w1 w2 e w)(*strict*)
   apply(rule conjI,blast)
   apply(rename_tac na d w1 w2 e w)(*strict*)
   apply(rule conjI)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(rule_tac
      m = "na"
      in cfgSTD.derivation_drop_preserves_derivation_from_to2)
       apply(rename_tac na d w1 w2 e w)(*strict*)
       apply(blast)
      apply(rename_tac na d w1 w2 e w)(*strict*)
      apply(rule_tac
      s = "Suc na"
      in ssubst)
       apply(rename_tac na d w1 w2 e w)(*strict*)
       apply(arith)
      apply(rename_tac na d w1 w2 e w)(*strict*)
      apply(blast)
     apply(rename_tac na d w1 w2 e w)(*strict*)
     apply(blast)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(rule impI)
    apply(subgoal_tac "\<exists>e. d (Suc 0) = Some (pair e \<lparr>cfg_conf = w2\<rparr>)")
     apply(rename_tac na d w1 w2 e w)(*strict*)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(rule cfgSTD.reachesToAtMaxDom)
     apply(rename_tac na d w1 w2 e w)(*strict*)
     apply(rule cfgSTD.from_to_is_to)
     apply(blast)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(blast)
   apply(rename_tac na d w1 w2 e w)(*strict*)
   apply(rule derivation_drop_preserves_generates_maximum_of_domain)
   apply(blast)
  apply(rename_tac na d w1 w2 e w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>e. d (Suc na) = Some (pair e \<lparr>cfg_conf=w2\<rparr>)")
   apply(rename_tac na d w1 w2 e w)(*strict*)
   prefer 2
   apply(rule cfgSTD.reachesToAtMaxDom)
    apply(rename_tac na d w1 w2 e w)(*strict*)
    apply(rule cfgSTD.from_to_is_to)
    apply(blast)
   apply(rename_tac na d w1 w2 e w)(*strict*)
   apply(clarsimp)
  apply(rename_tac na d w1 w2 e w)(*strict*)
  apply(clarsimp)
    (*
  valid_cfg G
  F_CFG_EB G = Some G'
  setA w1 \<subseteq> cfg_nonterminals G'
  setB w1 \<subseteq> cfg_events G'
  setA w2 = {}
  G:d:Suc na:w1\<longrightarrow>*w2
  d (Suc 0) = Some (pair (Some e) \<lparr>cfg_conf = w\<rparr>)
  setA w \<subseteq> cfg_nonterminals G'
  d 0 = Some (pair None \<lparr>cfg_conf = w1\<rparr>)
  d (Suc na) = Some (pair (Some ea) \<lparr>cfg_conf = w2\<rparr>)
  G':(skip d 1):w\<longrightarrow>*w2
  \<Longrightarrow>
  G':d:w1\<longrightarrow>*w2
  ---
  the goal is simple, for every step beyond the first step.
  the first step:
*)
  apply(rename_tac na d w1 w2 e w ea)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G' \<lparr>cfg_conf=w1\<rparr> e \<lparr>cfg_conf=w\<rparr>")
   apply(rename_tac na d w1 w2 e w ea)(*strict*)
   apply(subgoal_tac "cfgSTD.derivation G' d")
    apply(rename_tac na d w1 w2 e w ea)(*strict*)
    apply(simp (no_asm) add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
    apply(rule conjI)
     apply(rename_tac na d w1 w2 e w ea)(*strict*)
     apply(blast)
    apply(rename_tac na d w1 w2 e w ea)(*strict*)
    apply(rule conjI)
     apply(rename_tac na d w1 w2 e w ea)(*strict*)
     apply(clarsimp)
    apply(rename_tac na d w1 w2 e w ea)(*strict*)
    apply(rule conjI)
     apply(rename_tac na d w1 w2 e w ea)(*strict*)
     apply(blast)
    apply(rename_tac na d w1 w2 e w ea)(*strict*)
    apply(rule_tac
      x="Suc na"
      in exI)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac na d w1 w2 e w ea)(*strict*)
   apply(rule derivation_drop_Transfer_to_Other_Grammar_first_Step)
        apply(rename_tac na d w1 w2 e w ea)(*strict*)
        apply(rule cfgSTD.from_to_is_der)
        apply(blast)
       apply(rename_tac na d w1 w2 e w ea)(*strict*)
       apply(rule cfgSTD.from_to_is_der)
       apply(blast)
      apply(rename_tac na d w1 w2 e w ea)(*strict*)
      apply(blast)
     apply(rename_tac na d w1 w2 e w ea)(*strict*)
     apply(blast)+
  apply(rename_tac na d w1 w2 e w ea)(*strict*)
  apply(subgoal_tac "cfgSTD_step_relation G \<lparr>cfg_conf = w1\<rparr> e \<lparr>cfg_conf = w\<rparr>")
   apply(rename_tac na d w1 w2 e w ea)(*strict*)
   apply(simp add: cfgSTD_step_relation_def)
   apply(clarsimp)
   apply(rename_tac na d w2 e ea l r)(*strict*)
   apply(simp add: F_CFG_EB_def)
   apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
    apply(rename_tac na d w2 e ea l r)(*strict*)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac na d w2 e ea l r)(*strict*)
     apply(rule_tac
      A="setA (l @ teA (prod_lhs e) # r)"
      in set_mp)
      apply(rename_tac na d w2 e ea l r)(*strict*)
      apply(blast)
     apply(rename_tac na d w2 e ea l r)(*strict*)
     apply(rule elemInsetA)
    apply(rename_tac na d w2 e ea l r)(*strict*)
    apply(rule_tac
      B="setA (l @ prod_rhs e @ r)"
      in subset_trans)
     apply(rename_tac na d w2 e ea l r)(*strict*)
     apply(simp (no_asm) only: setAConcat concat_asso)
     apply(clarsimp)
    apply(rename_tac na d w2 e ea l r)(*strict*)
    apply(blast)
   apply(rename_tac na d w2 e ea l r)(*strict*)
   apply(force)
  apply(rename_tac na d w1 w2 e w ea)(*strict*)
  apply(rule cfgSTD.stepOnlyDueToStepRelation)
     apply(rename_tac na d w1 w2 e w ea)(*strict*)
     apply(blast)
    apply(rename_tac na d w1 w2 e w ea)(*strict*)
    apply(rule cfgSTD.from_to_is_der)
    apply(blast)
   apply(rename_tac na d w1 w2 e w ea)(*strict*)
   apply(blast)
  apply(rename_tac na d w1 w2 e w ea)(*strict*)
  apply(blast)
  done

theorem F_CFG_EB_None_implies_empty_lang: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = None
  \<Longrightarrow> cfgSTD.marked_language G = {}"
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "cfg_initial G \<notin> cfgSTD_Nonblockingness_nonterminals G")
   prefer 2
   apply (metis F_CFG_EBSoundL)
  apply(thin_tac "cfg_initial G \<notin> F_CFG_EB__fp G {}")
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(erule impE)
   apply(simp add: valid_cfg_def)
  apply(rule order_antisym)
   prefer 2
   apply(force)
  apply(simp add: cfgSTD.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(erule_tac
      x="d"
      in allE)
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(rename_tac x d i e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d i e c cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac x d i e w)(*strict*)
  apply(erule_tac
      x="w"
      in allE)
  apply(clarsimp)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfgSTD.derivation_initial_def)
  apply(case_tac "d 0")
   apply(rename_tac x d i e w)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d i e w a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d i e w a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d i e w b)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d i e w)(*strict*)
  apply(erule_tac
      x="i"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "d (Suc i)=None")
   apply(rename_tac x d i e w)(*strict*)
   apply(force)
  apply(rename_tac x d i e w)(*strict*)
  apply(thin_tac "(\<exists>y. d (Suc i) = Some y) \<or> (\<forall>y. (\<forall>x. y \<noteq> pair x \<lparr>cfg_conf = w\<rparr>) \<or> pair e \<lparr>cfg_conf = w\<rparr> \<noteq> y)")
  apply(rename_tac x d i e w)(*strict*)
  apply(thin_tac "\<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr> \<in> cfg_configurations G")
  apply(thin_tac "\<lparr>cfg_conf = w\<rparr> \<in> cfg_configurations G")
  apply(thin_tac "d 0 = Some (pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>)")
  apply(thin_tac "x \<in> cfg_marked_effect G d")
  apply (metis CFG_nonterm_free_conf_at_maximum_of_domain Suc_n_not_le_n cfgSTD.allPreMaxDomSome_prime)
  done

lemma F_CFG_EB_lang_eq1: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfgSTD.marked_language G \<subseteq> cfgSTD.marked_language G'"
  apply(simp add: cfgSTD.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(subgoal_tac "cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = [teA(cfg_initial G)]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = liftB x\<rparr>}")
   apply(rename_tac x d)(*strict*)
   prefer 2
   apply(rule canMimik)
        apply(rename_tac x d)(*strict*)
        apply(force)
       apply(rename_tac x d)(*strict*)
       apply(force)
      apply(rename_tac x d)(*strict*)
      apply(simp add: F_CFG_EB_def)
      apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
       apply(rename_tac x d)(*strict*)
       prefer 2
       apply(force)
      apply(rename_tac x d)(*strict*)
      apply(force)
     apply(rename_tac x d)(*strict*)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply (metis setA_liftB)
   apply(rename_tac x d)(*strict*)
   apply(simp add: cfgSTD.derivation_initial_def cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfg_initial_configurations_def cfg_marked_effect_def)
   apply(case_tac "d 0")
    apply(rename_tac x d)(*strict*)
    apply(force)
   apply(rename_tac x d a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d a e c i)(*strict*)
   apply(case_tac a)
   apply(rename_tac x d a e c i option b)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d e c i b)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac x d e c i)(*strict*)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply (metis setA_liftB cfg_no_step_without_nonterms)
  apply(rename_tac x d)(*strict*)
  apply(subgoal_tac "set x \<subseteq> cfg_events G")
   apply(rename_tac x d)(*strict*)
   prefer 2
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfg_marked_effect_def cfg_marking_condition_def cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac x d xa e i c ea ca ia n xaa)(*strict*)
   apply(case_tac c)
   apply(rename_tac x d xa e i c ea ca ia n xaa cfg_confa)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
   apply(case_tac "d 0")
    apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
    apply(force)
   apply(rename_tac x d xa e i ea ca ia n xaa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
   apply(subgoal_tac "\<lparr>cfg_conf = liftB x\<rparr> \<in> cfg_configurations G")
    apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
    apply(simp add: cfg_configurations_def)
    apply (metis set_setB_liftB subsetD)
   apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
   apply(rule_tac
      d="d"
      and i="n"
      in cfgSTD.belongs_configurations)
    apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
   apply(rule cfgSTD.derivation_initial_belongs)
    apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
    apply(force)
   apply(rename_tac x d xa e i ea ca ia n xaa)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfg_initial_configurations_def cfg_marked_effect_def cfg_marking_condition_def)
  apply(case_tac "d 0")
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i c ea ca ia n xa)(*strict*)
  apply(simp add: cfg_initial_configurations_def)
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   apply(rename_tac x d e i c ea ca ia n xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x d e i c ea ca ia n xa)(*strict*)
  apply(clarsimp)
  apply(simp add: cfg_configurations_def)
  apply(rule_tac
      x="ia"
      in exI)
  apply(rule_tac
      x="e"
      in exI)
  apply(rule_tac
      x="c"
      in exI)
  apply(clarsimp)
  apply(simp add: cfg_marking_configuration_def cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d e i c ea ia n xa cb)(*strict*)
  apply(case_tac c)
  apply(rename_tac x d e i c ea ia n xa cb cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i ea ia n xa cb xb)(*strict*)
  apply(subgoal_tac "xb\<in> set x")
   apply(rename_tac x d e i ea ia n xa cb xb)(*strict*)
   prefer 2
   apply (metis set_setB_liftB)
  apply(rename_tac x d e i ea ia n xa cb xb)(*strict*)
  apply(rule_tac
      A="set x"
      in set_mp)
   apply(rename_tac x d e i ea ia n xa cb xb)(*strict*)
   apply(force)
  apply(rename_tac x d e i ea ia n xa cb xb)(*strict*)
  apply(force)
  done

lemma canMimikRev: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfgSTD.derivation G' d
  \<Longrightarrow> cfgSTD.derivation G d"
  apply(simp (no_asm) add: cfgSTD.derivation_def)
  apply(clarsimp)
  apply(rename_tac i)(*strict*)
  apply(case_tac i)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(simp add: cfgSTD.derivation_def)
   apply(erule_tac
      x="0"
      in allE)
   apply(clarsimp)
  apply(rename_tac i nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat)(*strict*)
  apply(case_tac "d (Suc nat)")
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
  apply(rename_tac nat a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i a)
  apply(rename_tac i a)(*strict*)
  apply(subgoal_tac "\<exists>e1 e2 c1 c2. d i = Some (pair e1 c1) \<and> d (Suc i) = Some (pair (Some e2) c2) \<and> cfgSTD_step_relation G' c1 e2 c2")
   apply(rename_tac i a)(*strict*)
   prefer 2
   apply(rule_tac
      m="Suc i"
      in cfgSTD.step_detail_before_some_position)
     apply(rename_tac i a)(*strict*)
     apply(force)
    apply(rename_tac i a)(*strict*)
    apply(force)
   apply(rename_tac i a)(*strict*)
   apply(force)
  apply(rename_tac i a)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c1 c2)(*strict*)
  apply(simp add: cfgSTD_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i e1 e2 c1 c2 l r)(*strict*)
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   apply(rename_tac i e1 e2 c1 c2 l r)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i e1 e2 c1 c2 l r)(*strict*)
  apply(force)
  done

lemma F_CFG_EB_lang_eq2: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfgSTD.marked_language G \<supseteq> cfgSTD.marked_language G'"
  apply(simp add: cfgSTD.marked_language_def)
  apply(clarsimp)
  apply(rename_tac x d)(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(subgoal_tac "cfgSTD.derivation G d")
   apply(rename_tac x d)(*strict*)
   prefer 2
   apply(rule canMimikRev)
     apply(rename_tac x d)(*strict*)
     apply(force)
    apply(rename_tac x d)(*strict*)
    apply(force)
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d)(*strict*)
  apply(simp add: cfgSTD.derivation_initial_def)
  apply(case_tac "d 0")
   apply(rename_tac x d)(*strict*)
   apply(force)
  apply(rename_tac x d a)(*strict*)
  apply(clarsimp)
  apply(case_tac a)
  apply(rename_tac x d a option b)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d b)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d b)(*strict*)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rename_tac x d)(*strict*)
   apply(simp add: F_CFG_EB_def)
   apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
    apply(rename_tac x d)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x d)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(simp add: valid_cfg_def)
   apply(force)
  apply(rename_tac x d b)(*strict*)
  apply(rule conjI)
   apply(rename_tac x d b)(*strict*)
   apply(simp add: cfg_marked_effect_def)
  apply(rename_tac x d b)(*strict*)
  apply(simp add: cfg_marking_condition_def)
  apply(clarsimp)
  apply(rename_tac x d b i e c)(*strict*)
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
  apply(simp add: cfg_marking_configuration_def cfg_configurations_def)
  apply(clarsimp)
  apply(rename_tac x d b i e ca xa)(*strict*)
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
   apply(rename_tac x d b i e ca xa)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x d b i e ca xa)(*strict*)
  apply(clarsimp)
  apply(rule_tac
      A="setB ca"
      in set_mp)
   apply(rename_tac x d b i e ca xa)(*strict*)
   apply(force)
  apply(rename_tac x d b i e ca xa)(*strict*)
  apply(force)
  done

lemma F_CFG_EB_lang_eq: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfgSTD.marked_language G = cfgSTD.marked_language G'"
  apply(rule order_antisym)
   apply(rule F_CFG_EB_lang_eq1)
    apply(force)
   apply(force)
  apply(rule F_CFG_EB_lang_eq2)
   apply(force)
  apply(force)
  done

lemma F_CFG_EB_idemp1: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfgSTD_Nonblockingness_nonterminals G' = cfgSTD_Nonblockingness_nonterminals G"
  apply(rule order_antisym)
   apply(rule_tac
      t="cfgSTD_Nonblockingness_nonterminals G"
      and s="F_CFG_EB__fp G {}"
      in ssubst)
    apply(rule F_CFG_EBSoundL)
    apply(force)
   apply(rule_tac
      t="F_CFG_EB__fp G {}"
      and s="cfg_nonterminals G'"
      in ssubst)
    apply(simp add: F_CFG_EB_def)
    apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
     apply(force)
    apply(force)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
   apply(clarsimp)
  apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
  apply(clarsimp)
  apply(rename_tac x d w')(*strict*)
  apply(rule context_conjI)
   apply(rename_tac x d w')(*strict*)
   apply(rule_tac
      s="F_CFG_EB__fp G {}"
      and t="cfg_nonterminals G'"
      in ssubst)
    apply(rename_tac x d w')(*strict*)
    apply(simp add: F_CFG_EB_def)
    apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
     apply(rename_tac x d w')(*strict*)
     apply(force)
    apply(rename_tac x d w')(*strict*)
    apply(force)
   apply(rename_tac x d w')(*strict*)
   apply(rule_tac
      s="cfgSTD_Nonblockingness_nonterminals G"
      and t="F_CFG_EB__fp G {}"
      in subst)
    apply(rename_tac x d w')(*strict*)
    apply(rule F_CFG_EBSoundL)
    apply(force)
   apply(rename_tac x d w')(*strict*)
   apply(simp add: cfgSTD_Nonblockingness_nonterminals_def)
   apply(rule_tac
      x="d"
      in exI)
   apply(rule_tac
      x="w'"
      in exI)
   apply(clarsimp)
  apply(rename_tac x d w')(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(rule_tac
      x="w'"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d w')(*strict*)
   apply(rule canMimik)
        apply(rename_tac x d w')(*strict*)
        apply(force)+
  done

lemma F_CFG_EB_makes_Nonblockingness: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> Nonblockingness (cfgSTD.unmarked_language G') (cfgSTD.marked_language G')"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_EBSound3)
    apply(force)
   apply(force)
  apply(rule NonblockingnessI)
   prefer 2
   apply(rule CFG_Nonblockingness2)
   apply(force)
  apply(simp add: nonblockingness_language_def)
  apply(simp add: cfgSTD.unmarked_language_def cfgSTD.marked_language_def prefix_closure_def prefix_def cfg_initial_configurations_def cfg_unmarked_effect_def)
  apply(clarsimp)
  apply(rename_tac x d e c i z)(*strict*)
  apply(subgoal_tac "cfgSTD.belongs G' d")
   apply(rename_tac x d e c i z)(*strict*)
   prefer 2
   apply(rule cfgSTD.derivation_initial_belongs)
    apply(rename_tac x d e c i z)(*strict*)
    apply(force)
   apply(rename_tac x d e c i z)(*strict*)
   apply(force)
  apply(rename_tac x d e c i z)(*strict*)
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = liftB x@z\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
   apply(rename_tac x d e c i z)(*strict*)
   prefer 2
   apply(rule canElimCombine)
    apply(rename_tac x d e c i z)(*strict*)
    apply(force)
   apply(rename_tac x d e c i z)(*strict*)
   apply(rule_tac
      t="cfgSTD_Nonblockingness_nonterminals G'"
      and s="cfg_nonterminals G'"
      in ssubst)
    apply(rename_tac x d e c i z)(*strict*)
    apply(rule_tac
      t="cfg_nonterminals G'"
      and s="F_CFG_EB__fp G {}"
      in ssubst)
     apply(rename_tac x d e c i z)(*strict*)
     apply(simp add: F_CFG_EB_def)
     apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
      apply(rename_tac x d e c i z)(*strict*)
      apply(force)
     apply(rename_tac x d e c i z)(*strict*)
     apply(force)
    apply(rename_tac x d e c i z)(*strict*)
    apply(rule_tac
      t="cfgSTD_Nonblockingness_nonterminals G'"
      and s="cfgSTD_Nonblockingness_nonterminals G"
      in ssubst)
     apply(rename_tac x d e c i z)(*strict*)
     prefer 2
     apply(rule F_CFG_EBSoundL)
     apply(force)
    apply(rename_tac x d e c i z)(*strict*)
    apply(rule F_CFG_EB_idemp1)
     apply(rename_tac x d e c i z)(*strict*)
     apply(force)
    apply(rename_tac x d e c i z)(*strict*)
    apply(force)
   apply(rename_tac x d e c i z)(*strict*)
   apply(subgoal_tac "c \<in> cfg_configurations G'")
    apply(rename_tac x d e c i z)(*strict*)
    prefer 2
    apply(rule cfgSTD.belongs_configurations)
     apply(rename_tac x d e c i z)(*strict*)
     apply(force)
    apply(rename_tac x d e c i z)(*strict*)
    apply(force)
   apply(rename_tac x d e c i z)(*strict*)
   apply(simp add: cfg_configurations_def)
   apply(force)
  apply(rename_tac x d e c i z)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e c i z da w')(*strict*)
  apply(case_tac c)
  apply(rename_tac x d e c i z da w' cfg_confa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z da w')(*strict*)
  apply(rule_tac
      x="filterB w'"
      in exI)
  apply(rule conjI)
   apply(rename_tac x d e i z da w')(*strict*)
   apply(subgoal_tac "\<exists>n. maximum_of_domain da n")
    apply(rename_tac x d e i z da w')(*strict*)
    prefer 2
    apply(rule cfgSTD.to_has_maximum_of_domain)
    apply(rule cfgSTD.from_to_is_to)
    apply(force)
   apply(rename_tac x d e i z da w')(*strict*)
   apply(clarsimp)
   apply(rename_tac x d e i z da w' n)(*strict*)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(clarsimp)
   apply(rename_tac x d e i z da w' n na xa)(*strict*)
   apply(case_tac "da 0")
    apply(rename_tac x d e i z da w' n na xa)(*strict*)
    apply(clarsimp)
   apply(rename_tac x d e i z da w' n na xa a)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d e i z da w' n na xa)(*strict*)
   apply(subgoal_tac "cfgSTD.belongs G' da")
    apply(rename_tac x d e i z da w' n na xa)(*strict*)
    prefer 2
    apply(rule cfgSTD.derivation_belongs)
       apply(rename_tac x d e i z da w' n na xa)(*strict*)
       apply(force)
      apply(rename_tac x d e i z da w' n na xa)(*strict*)
      apply(force)
     apply(rename_tac x d e i z da w' n na xa)(*strict*)
     apply(rule_tac
      d="d"
      in cfgSTD.belongs_configurations)
      apply(rename_tac x d e i z da w' n na xa)(*strict*)
      apply(force)
     apply(rename_tac x d e i z da w' n na xa)(*strict*)
     apply(force)
    apply(rename_tac x d e i z da w' n na xa)(*strict*)
    apply(force)
   apply(rename_tac x d e i z da w' n na xa)(*strict*)
   apply(subgoal_tac "na=n")
    apply(rename_tac x d e i z da w' n na xa)(*strict*)
    prefer 2
    apply(rule_tac
      d="da"
      in cfgSTD.maximum_of_domainUnique)
      apply(rename_tac x d e i z da w' n na xa)(*strict*)
      apply(force)
     apply(rename_tac x d e i z da w' n na xa)(*strict*)
     apply(force)
    apply(rename_tac x d e i z da w' n na xa)(*strict*)
    apply(simp add: maximum_of_domain_def)
   apply(rename_tac x d e i z da w' n na xa)(*strict*)
   apply(case_tac n)
    apply(rename_tac x d e i z da w' n na xa)(*strict*)
    apply(clarsimp)
    apply(rename_tac x d e i z da)(*strict*)
    apply(rule_tac
      x="d"
      in exI)
    apply(clarsimp)
    apply(simp add: cfg_marking_condition_def cfg_marked_effect_def)
    apply(rule conjI)
     apply(rename_tac x d e i z da)(*strict*)
     apply(rule_tac
      x="e"
      in exI)
     apply(rule_tac
      x="\<lparr>cfg_conf = liftB x @ z\<rparr>"
      in exI)
     apply(clarsimp)
     apply(rule conjI)
      apply(rename_tac x d e i z da)(*strict*)
      apply(rule_tac
      x="i"
      in exI)
      apply(force)
     apply(rename_tac x d e i z da)(*strict*)
     apply(rule liftBDeConv2)
     apply(force)
    apply(rename_tac x d e i z da)(*strict*)
    apply(rule_tac
      x="i"
      in exI)
    apply(rule_tac
      x="e"
      in exI)
    apply(rule_tac
      x="\<lparr>cfg_conf = liftB x @ z\<rparr>"
      in exI)
    apply(clarsimp)
    apply(simp add: cfg_marking_configuration_def)
    apply(rule cfgSTD.belongs_configurations)
     apply(rename_tac x d e i z da)(*strict*)
     apply(force)
    apply(rename_tac x d e i z da)(*strict*)
    apply(force)
   apply(rename_tac x d e i z da w' n na xa nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac x d e i z da w' xa nat)(*strict*)
   apply(rule_tac
      x="derivation_append (derivation_take d i) da i"
      in exI)
   apply(rule conjI)
    apply(rename_tac x d e i z da w' xa nat)(*strict*)
    apply(simp add: cfgSTD.derivation_initial_def)
    apply(rule conjI)
     apply(rename_tac x d e i z da w' xa nat)(*strict*)
     apply(rule cfgSTD.derivation_concat2)
        apply(rename_tac x d e i z da w' xa nat)(*strict*)
        apply(rule cfgSTD.derivation_take_preserves_derivation)
        apply(force)
       apply(rename_tac x d e i z da w' xa nat)(*strict*)
       apply(rule maximum_of_domain_derivation_take)
       apply(force)
      apply(rename_tac x d e i z da w' xa nat)(*strict*)
      apply(force)
     apply(rename_tac x d e i z da w' xa nat)(*strict*)
     apply(simp add: derivation_take_def derivation_append_def)
    apply(rename_tac x d e i z da w' xa nat)(*strict*)
    apply(simp add: derivation_take_def derivation_append_def)
   apply(rename_tac x d e i z da w' xa nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d e i z da w' xa nat)(*strict*)
    apply(simp add: cfg_marked_effect_def derivation_append_def)
    apply(rule_tac
      x="xa"
      in exI)
    apply(rule_tac
      x="\<lparr>cfg_conf = w'\<rparr>"
      in exI)
    apply(clarsimp)
    apply(rule conjI)
     apply(rename_tac x d e i z da w' xa nat)(*strict*)
     apply(rule_tac
      x="i+(Suc nat)"
      in exI)
     apply(rule conjI)
      apply(rename_tac x d e i z da w' xa nat)(*strict*)
      apply(clarsimp)
     apply(rename_tac x d e i z da w' xa nat)(*strict*)
     apply(clarsimp)
    apply(rename_tac x d e i z da w' xa nat)(*strict*)
    apply(rule liftBDeConv2)
    apply(force)
   apply(rename_tac x d e i z da w' xa nat)(*strict*)
   apply(rule conjI)
    apply(rename_tac x d e i z da w' xa nat)(*strict*)
    apply(rule cfgSTD.derivation_concat2)
       apply(rename_tac x d e i z da w' xa nat)(*strict*)
       apply(rule cfgSTD.derivation_take_preserves_derivation)
       apply(force)
      apply(rename_tac x d e i z da w' xa nat)(*strict*)
      apply(rule maximum_of_domain_derivation_take)
      apply(force)
     apply(rename_tac x d e i z da w' xa nat)(*strict*)
     apply(force)
    apply(rename_tac x d e i z da w' xa nat)(*strict*)
    apply(simp add: derivation_take_def)
   apply(rename_tac x d e i z da w' xa nat)(*strict*)
   apply(simp add: cfg_marking_condition_def)
   apply(rule_tac
      x="i+(Suc nat)"
      in exI)
   apply(rule_tac
      x="xa"
      in exI)
   apply(rule_tac
      x="\<lparr>cfg_conf = w'\<rparr>"
      in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac x d e i z da w' xa nat)(*strict*)
    apply(simp add: derivation_append_def derivation_take_def)
   apply(rename_tac x d e i z da w' xa nat)(*strict*)
   apply(simp add: cfg_marking_configuration_def)
   apply(rule_tac
      d="da"
      in cfgSTD.belongs_configurations)
    apply(rename_tac x d e i z da w' xa nat)(*strict*)
    apply(force)
   apply(rename_tac x d e i z da w' xa nat)(*strict*)
   apply(force)
  apply(rename_tac x d e i z da w')(*strict*)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac x d e i z da w' n xa)(*strict*)
  apply(case_tac "da 0")
   apply(rename_tac x d e i z da w' n xa)(*strict*)
   apply(clarsimp)
  apply(rename_tac x d e i z da w' n xa a)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z da w' n xa)(*strict*)
  apply(subgoal_tac "\<exists>e w. da n = Some (pair e \<lparr>cfg_conf = (liftB x) @ w\<rparr>)")
   apply(rename_tac x d e i z da w' n xa)(*strict*)
   prefer 2
   apply(rule_tac
      m="0"
      and n="n"
      in terminals_at_beginning_are_never_modified)
       apply(rename_tac x d e i z da w' n xa)(*strict*)
       apply(force)
      apply(rename_tac x d e i z da w' n xa)(*strict*)
      apply(simp add: maximum_of_domain_def)
     apply(rename_tac x d e i z da w' n xa)(*strict*)
     apply(force)
    apply(rename_tac x d e i z da w' n xa)(*strict*)
    apply(force)
   apply(rename_tac x d e i z da w' n xa)(*strict*)
   apply(force)
  apply(rename_tac x d e i z da w' n xa)(*strict*)
  apply(clarsimp)
  apply(rename_tac x d e i z da n xa w)(*strict*)
  apply(rule_tac
      x="filterB w"
      in exI)
  apply(rule_tac
      t="filterB (liftB x @ w)"
      and s="filterB (liftB x) @ (filterB w)"
      in ssubst)
   apply(rename_tac x d e i z da n xa w)(*strict*)
   apply(rule filterB_commutes_over_concat)
  apply(rename_tac x d e i z da n xa w)(*strict*)
  apply(clarsimp)
  apply(rule sym)
  apply(rule liftBDeConv1)
  done

lemma F_CFG_EB_makes_Nonblockingness_id: "
  valid_cfg G
  \<Longrightarrow> F_CFG_EB G = Some G'
  \<Longrightarrow> cfgSTD.Nonblockingness_branching G'"
  apply(subgoal_tac "valid_cfg G'")
   prefer 2
   apply(rule F_CFG_EBSound3)
    apply(force)
   apply(force)
  apply(subgoal_tac "cfgSTD_Nonblockingness_nonterminals G' = cfg_nonterminals G'")
   prefer 2
   apply(subgoal_tac "cfgSTD_Nonblockingness_nonterminals G' = cfgSTD_Nonblockingness_nonterminals G")
    prefer 2
    apply(rule F_CFG_EB_idemp1)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(rule F_CFG_EBSoundA)
    apply(force)
   apply(force)
  apply(simp add: cfgSTD.Nonblockingness_branching_def)
  apply(clarsimp)
  apply(rename_tac dh n)(*strict*)
  apply(subgoal_tac "\<exists>e c. dh n= Some (pair e c)")
   apply(rename_tac dh n)(*strict*)
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
   apply(rename_tac dh n y)(*strict*)
   apply(case_tac y)
   apply(rename_tac dh n y option b)(*strict*)
   apply(force)
  apply(rename_tac dh n)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e c)(*strict*)
  apply(case_tac c)
  apply(rename_tac dh n e c cfg_conf)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e cfg_conf)(*strict*)
  apply(rename_tac w)
  apply(rename_tac dh n e w)(*strict*)
  apply(subgoal_tac "\<lparr>cfg_conf = w\<rparr> \<in> cfg_configurations G'")
   apply(rename_tac dh n e w)(*strict*)
   prefer 2
   apply(rule cfgSTD.belongs_configurations)
    apply(rename_tac dh n e w)(*strict*)
    apply(rule cfgSTD.derivation_initial_belongs)
     apply(rename_tac dh n e w)(*strict*)
     apply(force)
    apply(rename_tac dh n e w)(*strict*)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(subgoal_tac "\<exists>d w'. cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = w\<rparr>} {y. \<exists>x. y = pair x \<lparr>cfg_conf = w'\<rparr>} \<and> setA w' = {}")
   apply(rename_tac dh n e w)(*strict*)
   prefer 2
   apply(rule canElimCombine)
    apply(rename_tac dh n e w)(*strict*)
    apply(force)
   apply(rename_tac dh n e w)(*strict*)
   apply(rule_tac
      B="cfg_nonterminals G'"
      in subset_trans)
    apply(rename_tac dh n e w)(*strict*)
    apply(simp add: cfg_configurations_def)
   apply(rename_tac dh n e w)(*strict*)
   apply(force)
  apply(rename_tac dh n e w)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w d w')(*strict*)
  apply(rule_tac
      x="d"
      in exI)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  apply(clarsimp)
  apply(rename_tac dh n e w d w' na x)(*strict*)
  apply(case_tac "d 0")
   apply(rename_tac dh n e w d w' na x)(*strict*)
   apply(force)
  apply(rename_tac dh n e w d w' na x a)(*strict*)
  apply(clarsimp)
  apply(rename_tac dh n e w d w' na x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w d w' na x)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac dh n e w d w' na x)(*strict*)
      apply(force)
     apply(rename_tac dh n e w d w' na x)(*strict*)
     apply(force)
    apply(rename_tac dh n e w d w' na x)(*strict*)
    apply(force)
   apply(rename_tac dh n e w d w' na x)(*strict*)
   apply(force)
  apply(rename_tac dh n e w d w' na x)(*strict*)
  apply(rule conjI)
   apply(rename_tac dh n e w d w' na x)(*strict*)
   apply(rule_tac
      x="na"
      in exI)
   apply(simp add: maximum_of_domain_def)
  apply(rename_tac dh n e w d w' na x)(*strict*)
  apply(rule context_conjI)
   apply(rename_tac dh n e w d w' na x)(*strict*)
   apply(simp add: derivation_append_fit_def)
  apply(rename_tac dh n e w d w' na x)(*strict*)
  apply(simp add: derivation_append_fit_def)
  apply(simp add: cfg_marking_condition_def derivation_append_def)
  apply(rule_tac
      x="n+na"
      in exI)
  apply(clarsimp)
  apply(subgoal_tac "\<lparr>cfg_conf = w'\<rparr> \<in> cfg_marking_configuration G'")
   apply(rename_tac dh n e w d w' na x)(*strict*)
   apply(case_tac na)
    apply(rename_tac dh n e w d w' na x)(*strict*)
    apply(force)
   apply(rename_tac dh n e w d w' na x nat)(*strict*)
   apply(force)
  apply(rename_tac dh n e w d w' na x)(*strict*)
  apply(simp add: cfg_marking_configuration_def)
  apply(rule_tac
      d="d"
      in cfgSTD.belongs_configurations)
   apply(rename_tac dh n e w d w' na x)(*strict*)
   apply(rule cfgSTD.derivation_belongs)
      apply(rename_tac dh n e w d w' na x)(*strict*)
      apply(force)
     apply(rename_tac dh n e w d w' na x)(*strict*)
     apply(force)
    apply(rename_tac dh n e w d w' na x)(*strict*)
    apply(rule_tac
      d="dh"
      in cfgSTD.belongs_configurations)
     apply(rename_tac dh n e w d w' na x)(*strict*)
     apply(rule cfgSTD.derivation_initial_belongs)
      apply(rename_tac dh n e w d w' na x)(*strict*)
      apply(force)
     apply(rename_tac dh n e w d w' na x)(*strict*)
     apply(force)
    apply(rename_tac dh n e w d w' na x)(*strict*)
    apply(force)
   apply(rename_tac dh n e w d w' na x)(*strict*)
   apply(force)
  apply(rename_tac dh n e w d w' na x)(*strict*)
  apply(force)
  done

definition F_CFG_EB__SpecInput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> bool"
  where
    "F_CFG_EB__SpecInput G \<equiv>
  valid_cfg G"

definition F_CFG_EB__SpecOutput :: "
  ('nonterminal, 'event) cfg
  \<Rightarrow> ('nonterminal, 'event) cfg option
  \<Rightarrow> bool"
  where
    "F_CFG_EB__SpecOutput Gi Go \<equiv>
  case Go of
    None \<Rightarrow> cfgLM.marked_language Gi = {}
    | Some Go \<Rightarrow>
      valid_cfg Go
      \<and> cfg_sub Go Gi
      \<and> cfgLM.marked_language Go = cfgLM.marked_language Gi
      \<and> cfgLM.initial_marking_derivations Go = cfgLM.initial_marking_derivations Gi
      \<and> cfg_nonterminals Go = cfgSTD_Nonblockingness_nonterminals Gi
      \<and> cfg_nonterminals Go = cfgSTD_Nonblockingness_nonterminals Go
      \<and> cfgLM.marked_language Go \<noteq> {}"

lemma F_CFG_EB_preserves_cfgLM_language_relevant_nonterminals: "
  F_CFG_EB G = Some G'
  \<Longrightarrow> valid_cfg G
  \<Longrightarrow> valid_cfg G'
  \<Longrightarrow> cfg_sub G' G
  \<Longrightarrow> cfg_nonterminals G' = cfgSTD_Nonblockingness_nonterminals G
  \<Longrightarrow> cfgLM_language_relevant_nonterminals G = cfgLM_language_relevant_nonterminals G'"
  apply(rule sym)
  apply(rule antisym)
   apply(rule cfg_sub_cfgLM_language_relevant_nonterminals_hlp1)
     apply(force)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(simp add: cfgLM_language_relevant_nonterminals_def cfg_marking_condition_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(rename_tac w)
  apply(clarsimp)
  apply(simp add: cfg_marking_configuration_def)
  apply(clarsimp)
  apply(subgoal_tac "\<exists>wx. w=liftB wx")
   prefer 2
   apply(rule_tac x="filterB w" in exI)
   apply (metis liftBDeConv2)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule earliest_occurence_in_list)
   apply(force)
  apply(clarsimp)
  apply(case_tac "i<n")
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac n="i" and m="n" and d="d" in cfgLM.step_detail_before_some_position)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(case_tac "i=n")
   apply(clarsimp)
  apply(simp add: setAConcat)
  apply(subgoal_tac "n<i")
   prefer 2
   apply(force)
  apply(clarsimp)
  apply(subgoal_tac "maximum_of_domain d i")
   prefer 2
   apply(simp add: maximum_of_domain_def)
   apply(case_tac "d (Suc i)")
    apply(force)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac n="i" and m="Suc i" and d="d" in cfgLM.step_detail_before_some_position)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(force)
     apply(force)
    apply(force)
   apply(clarsimp)
   apply(simp add: cfgLM_step_relation_def)
   apply(clarsimp)
   apply(simp add: setAConcat)
  apply(subgoal_tac "       cfgLM.derivation_initial G' d
")
   apply(thin_tac "cfgLM.derivation_initial G d")
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac G="G'" and n="i-n" and d="derivation_drop d n" and w'="liftB wx" and ?w1.0="w1" and ?w2.0="teA x # w2" in CFGLM_derivationCanBeDecomposed2_with_labels)
      apply(force)
     apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
     apply(rule context_conjI)
      apply(rule_tac m="i-n" in cfgLM.derivation_drop_preserves_derivation)
       apply(simp add: cfgLM.derivation_initial_def)
      apply(clarsimp)
     apply(clarsimp)
     apply(rule conjI)
      apply(simp add: derivation_drop_def)
     apply(rule_tac x="i-n" in exI)
     apply(simp add: derivation_drop_def)
     apply(simp add: maximum_of_domain_def)
    apply(simp add: derivation_drop_def)
    apply(simp add: maximum_of_domain_def)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_from_to_def cfgLM.derivation_from_def cfgLM.derivation_to_def)
   apply(clarsimp)
   apply(case_tac ca)
   apply(clarsimp)
   apply(rule_tac x="derivation_append d (derivation_append (derivation_map d1 (%c. \<lparr>cfg_conf=(cfg_conf c)@teA x # w2\<rparr>)) (derivation_map d2 (%c. \<lparr>cfg_conf=w1'@(cfg_conf c)\<rparr>)) na) n" in exI)
   apply(rule conjI)
    prefer 2
    apply(rule conjI)
     apply(rule_tac x="n+na+nb" in exI)
     apply(simp add: derivation_append_def derivation_map_def)
     apply(rule conjI)
      apply(clarsimp)
      apply (metis liftB_with_nonterminal_inside)
     apply(clarsimp)
     apply(subgoal_tac "\<lparr>cfg_conf = liftB wx\<rparr> \<in> cfg_configurations G'")
      apply(force)
     apply(simp add: F_CFG_EB_def)
     apply(case_tac "cfg_initial G \<in> F_CFG_EB__fp G {}")
      prefer 2
      apply(force)
     apply(clarsimp)
     apply(simp add: cfg_configurations_def)
    apply(rule_tac x="n+na" in exI)
    apply(simp add: derivation_append_def derivation_map_def)
    apply(rule conjI)
     apply(clarsimp)
     apply(simp add: setAConcat)
    apply(simp add: setAConcat)
   apply(rule cfgLM.derivation_append_preserves_derivation_initial)
     apply(force)
    apply(force)
   apply(rule cfgLM.derivation_append_preserves_derivation)
     apply(simp add: cfgLM.derivation_initial_def)
    apply(rule cfgLM.derivation_append_preserves_derivation)
      apply(simp add: cfgLM.derivation_initial_def)
      apply(rule cfgLM.derivation_map_preserves_derivation2)
       apply(simp add: cfgLM.derivation_initial_def cfgLM_step_relation_def)
      apply(simp add: cfgLM.derivation_initial_def cfgLM_step_relation_def)
      apply(clarsimp)
      apply(case_tac a)
      apply(case_tac b)
      apply(clarsimp)
      apply(rule_tac x="l" in exI)
      apply(force)
     apply(rule cfgLM.derivation_map_preserves_derivation2)
      apply(simp add: cfgLM.derivation_initial_def cfgLM_step_relation_def)
     apply(simp add: cfgLM.derivation_initial_def cfgLM_step_relation_def)
     apply(clarsimp)
     apply(case_tac a)
     apply(case_tac b)
     apply(clarsimp)
     apply(rule_tac x="w1'@l" in exI)
     apply(clarsimp)
     apply(simp add: setAConcat)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "X" for X)
     apply(thin_tac "maximum_of_domain d1 n1")
     apply(thin_tac "       maximum_of_domain d2 n2")
     apply(thin_tac "       n1 + n2 = i - n ")
     apply(thin_tac "       set (get_labels (derivation_drop d n) (i - n)) =
       set (get_labels d1 n1) \<union> set (get_labels d2 n2)")
     apply(thin_tac "       case d1 0 of None \<Rightarrow> False | Some x \<Rightarrow> x \<in> {pair None \<lparr>cfg_conf = w1\<rparr>}")
     apply(thin_tac "       case d2 0 of None \<Rightarrow> False
       | Some xa \<Rightarrow> xa \<in> {pair None \<lparr>cfg_conf = teA x # w2\<rparr>}")
     apply(thin_tac "       cfgLM.derivation G' d1 ")
     apply(thin_tac "       cfgLM.derivation G' d2 ")
     apply(thin_tac "       d1 (Suc na) = None ")
     apply(thin_tac "       d2 (Suc nb) = None ")
     apply(thin_tac "       d1 na = Some (pair xa \<lparr>cfg_conf = w1'\<rparr>) ")
     apply(thin_tac "       d2 nb = Some (pair xaa \<lparr>cfg_conf = w2'\<rparr>) ")
     apply(thin_tac "       cfgLM.derivation G' d ")
     apply(thin_tac "       case d 0 of None \<Rightarrow> False
       | Some (pair e c) \<Rightarrow> c \<in> cfg_initial_configurations G' \<and> e = None ")
     apply(thin_tac "       eb \<in> cfg_productions G' ")
     apply(thin_tac "setA l = {}")
     apply(clarsimp)
     apply (metis liftBSplit prefix_also_no_nonterms)
    apply(simp add: derivation_map_def)
    apply(case_tac "d2 0")
     apply(clarsimp)
    apply(clarsimp)
   apply(case_tac "d n")
    apply(clarsimp)
   apply(clarsimp)
   apply(simp add: derivation_append_def)
   apply(simp add: derivation_map_def)
   apply(case_tac "d1 0")
    apply(clarsimp)
   apply(clarsimp)
  apply(subgoal_tac "cfgSTD.derivation_from_to G' d {pair None \<lparr>cfg_conf = [teA (cfg_initial G)]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = liftB wx\<rparr>}")
   prefer 2
   apply(rule canMimik)
        apply(force)
       apply(force)
      apply(simp add: valid_cfg_def cfg_sub_def)
     apply(simp add: valid_cfg_def)
    apply(force)
   apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
   apply(rule context_conjI)
    apply(simp add: cfgLM.derivation_initial_def)
    apply(clarsimp)
    apply (metis cfgLM_derivations_are_cfg_derivations)
   apply(clarsimp)
   apply(case_tac "d 0")
    apply(clarsimp)
    apply(simp add: cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac a)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def)
   apply(clarsimp)
   apply(case_tac ca)
   apply(clarsimp)
   apply(rule_tac x="i" in exI)
   apply(clarsimp)
   apply(simp add: maximum_of_domain_def)
  apply(rule cfgSTD_to_cfgLM_translate_derivation_initial)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: cfgSTD.derivation_initial_def cfg_initial_configurations_def)
  apply(case_tac "d 0")
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_initial_def)
  apply(clarsimp)
  apply(case_tac a)
  apply(clarsimp)
  apply(simp add: cfgLM.derivation_initial_def cfg_initial_configurations_def cfg_configurations_def valid_cfg_def cfg_sub_def)
  apply(simp add: cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def)
  done

lemma F_CFG_EB_preserves_cfgLM_initial_marking_derivations: "
  valid_cfg Gi
  \<Longrightarrow> valid_cfg Go
  \<Longrightarrow> cfg_sub Go Gi
  \<Longrightarrow> Some Go = F_CFG_EB Gi
  \<Longrightarrow> cfgLM.initial_marking_derivations Gi \<subseteq> cfgLM.initial_marking_derivations Go"
  apply(simp add: cfgLM.initial_marking_derivations_def)
  apply(clarsimp)
  apply(rename_tac d)
  apply(rule conjI)
   prefer 2
   apply(simp add: cfg_marking_condition_def)
   apply(simp add: cfg_marking_configuration_def cfg_configurations_def cfg_sub_def)
   apply(clarsimp)
   apply(rule_tac x="i" in exI)
   apply(clarsimp)
   apply(simp add: F_CFG_EB_def)
   apply(case_tac "cfg_initial Gi \<in> F_CFG_EB__fp Gi {}")
    apply(force)
   apply(force)
  apply(simp add: cfg_marking_condition_def cfg_marking_configuration_def)
  apply(clarsimp)
  apply(case_tac c)
  apply(clarsimp)
  apply(rename_tac w)
  apply(subgoal_tac "cfgSTD.derivation_from_to Go d {pair None \<lparr>cfg_conf = [teA(cfg_initial Gi)]\<rparr>} {y. \<exists>xa. y = pair xa \<lparr>cfg_conf = w\<rparr>}")
   prefer 2
   apply(rule canMimik)
        apply(force)
       apply(force)
      apply(simp add: F_CFG_EB_def)
      apply(case_tac "cfg_initial Gi \<in> F_CFG_EB__fp Gi {}")
       prefer 2
       apply(force)
      apply(force)
     apply(force)
    apply (metis setA_liftB)
   apply(simp add: cfgSTD.derivation_initial_def cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfg_initial_configurations_def cfg_marked_effect_def)
   apply(case_tac "d 0")
    apply(simp add: cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(case_tac a)
   apply(clarsimp)
   apply(simp add: cfgLM.derivation_initial_def)
   apply(clarsimp)
   apply(simp add: cfg_initial_configurations_def)
   apply(clarsimp)
   apply(rule conjI)
    apply (metis cfgLM_derivations_are_cfg_derivations)
   apply(rule_tac
      x="i"
      in exI)
   apply(clarsimp)
   apply (metis cfgLM_no_step_without_nonterms cfg_configuration.select_convs(1))
  apply(rule cfgSTD_to_cfgLM_translate_derivation_initial)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(simp add: cfgLM.derivation_initial_def cfgSTD.derivation_initial_def cfgSTD.derivation_from_to_def cfgSTD.derivation_from_def cfgSTD.derivation_to_def cfg_initial_configurations_def cfg_marked_effect_def cfg_marking_condition_def)
  apply(case_tac "d 0")
   apply(force)
  apply(clarsimp)
  apply(simp add: cfg_initial_configurations_def cfg_configurations_def valid_cfg_def)
  apply(simp add: F_CFG_EB_def)
  apply(case_tac "cfg_initial Gi \<in> F_CFG_EB__fp Gi {}")
   prefer 2
   apply(force)
  apply(force)
  done

lemma F_CFG_EB_makes_equal_cfgLM_initial_marking_derivations: "
  valid_cfg Gi
  \<Longrightarrow> valid_cfg Go
  \<Longrightarrow> cfg_sub Go Gi
  \<Longrightarrow> Some Go = F_CFG_EB Gi
  \<Longrightarrow> cfgLM.initial_marking_derivations Go = cfgLM.initial_marking_derivations Gi"
  apply(rule antisym)
   apply(rule cfg_sub_preserves_cfgLM_initial_marking_derivations)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_CFG_EB_preserves_cfgLM_initial_marking_derivations)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

theorem F_CFG_EB__SOUND: "
  F_CFG_EB__SpecInput G
  \<Longrightarrow> F_CFG_EB__SpecOutput G (F_CFG_EB G)"
  apply(simp add: F_CFG_EB__SpecOutput_def F_CFG_EB__SpecInput_def)
  apply(case_tac "F_CFG_EB G")
   apply(clarsimp)
   apply (metis CFG_lang_lm_lang_equal F_CFG_EB_None_implies_empty_lang)
  apply(clarsimp)
  apply(rename_tac Go)
  apply(rule context_conjI)
   apply (metis F_CFG_EBSound3)
  apply(rule context_conjI)
   apply (metis F_CFG_EB_makes_cfg_sub)
  apply(rule context_conjI)
   apply (metis CFG_lang_lm_lang_equal F_CFG_EB_lang_eq)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EB_idemp1)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_CFG_EBSoundA)
    apply(force)
   apply(force)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac G="Go" in CFG_Nonblockingness_is_lang_notempty)
    apply(force)
   apply(rule F_CFG_EB_makes_Nonblockingness_id)
    apply(force)
   apply(force)
  apply(clarsimp)
  apply(rule propSym)
  apply(rule context_conjI)
   apply(rule_tac t="cfgLM.marked_language G" and s="cfgLM.marked_language Go" in ssubst)
    apply(force)
   apply(rule_tac t="cfgLM.marked_language Go" and s="cfgSTD.marked_language Go" in ssubst)
    apply (metis CFG_lang_lm_lang_equal)
   apply(force)
  apply(rule F_CFG_EB_makes_equal_cfgLM_initial_marking_derivations)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

end
