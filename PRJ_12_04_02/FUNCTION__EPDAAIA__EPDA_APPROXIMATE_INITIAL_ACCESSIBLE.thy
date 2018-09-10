section {*FUNCTION\_\_EPDAAIA\_\_EPDA\_APPROXIMATE\_INITIAL\_ACCESSIBLE*}
theory
  FUNCTION__EPDAAIA__EPDA_APPROXIMATE_INITIAL_ACCESSIBLE

imports
  PRJ_12_04_02__ENTRY

begin

definition F_EPDA_AIA__fp_invariant_01 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> bool"
  where
    "F_EPDA_AIA__fp_invariant_01 G k N \<equiv>
  F_EPDA_AIA__fp_start G k \<in> N"

definition F_EPDA_AIA__codom :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set"
  where
    "F_EPDA_AIA__codom G k \<equiv>
  {cons_tuple2 q (take k s) | q s. q \<in> epda_states G \<and> set s \<subseteq> epda_gamma G}
  \<union> {F_EPDA_AIA__fp_start G k}"

definition F_EPDA_AIA__fp_invariant_02 :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> bool"
  where
    "F_EPDA_AIA__fp_invariant_02 G k N \<equiv>
  N \<subseteq> F_EPDA_AIA__codom G k"

definition F_EPDA_AIA__fp_invariants :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> bool"
  where
    "F_EPDA_AIA__fp_invariants G k N \<equiv>
  F_EPDA_AIA__fp_invariant_01 G k N
  \<and> F_EPDA_AIA__fp_invariant_02 G k N"

definition F_EPDA_AIA__fp_all_have_parent_element :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> bool"
  where
    "F_EPDA_AIA__fp_all_have_parent_element G k E \<equiv>
  \<forall>q2 s2.
  cons_tuple2 q2 s2 \<in> E - {F_EPDA_AIA__fp_start G k}
  \<longrightarrow> (\<exists>q1 x w1 w2 s1.
      cons_tuple2 q1 s1 \<in> E
      \<and> \<lparr>edge_src = q1,
        edge_event = x,
        edge_pop = w1,
        edge_push = w2,
        edge_trg = q2\<rparr> \<in> epda_delta G
      \<and> s2 = take k (w2 @ (drop (length w1) s1)))"

definition F_EPDA_AIA__fp_valid_input :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> bool"
  where
    "F_EPDA_AIA__fp_valid_input G k E \<equiv>
  valid_epda G
  \<and> F_EPDA_AIA__fp_start G k \<in> E
  \<and> E \<subseteq> F_EPDA_AIA__codom G k
  \<and> F_EPDA_AIA__fp_all_have_parent_element G k E"

lemma F_EPDA_AIA__fp_valid_input_implies_F_EPDA_AIA__fp_invariants: "
  F_EPDA_AIA__fp_valid_input G k N
  \<Longrightarrow> F_EPDA_AIA__fp_invariants G k N"
  apply(simp add: F_EPDA_AIA__fp_invariants_def)
  apply(simp add: F_EPDA_AIA__fp_valid_input_def F_EPDA_AIA__fp_invariant_01_def F_EPDA_AIA__fp_invariant_02_def F_EPDA_AIA__fp_start_def)
  done

lemma F_EPDA_AIA__fp_one_preserves_F_EPDA_AIA__fp_valid_input: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp_one G k E)"
  apply(simp add: F_EPDA_AIA__fp_valid_input_def F_EPDA_AIA__fp_one_def valid_epda_def F_EPDA_AIA__fp_one_def F_EPDA_AIA__fp_start_def)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(rename_tac q1 s1 q2 xa w1 w2)(*strict*)
   apply(thin_tac "w1 \<sqsubseteq> s1 \<or> s1 \<sqsubseteq> w1")
   apply(subgoal_tac "cons_tuple2 q1 s1 \<in> F_EPDA_AIA__codom G k")
    apply(rename_tac q1 s1 q2 xa w1 w2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q1 s1 q2 xa w1 w2)(*strict*)
   apply(thin_tac " E \<subseteq> F_EPDA_AIA__codom G k")
   apply(thin_tac "cons_tuple2 q1 s1
       \<in> E")
   apply(simp add: F_EPDA_AIA__codom_def)
   apply(erule_tac x="\<lparr>edge_src = q1, edge_event = xa, edge_pop = w1, edge_push = w2,
          edge_trg = q2\<rparr>" in ballE)
    apply(rename_tac q1 s1 q2 xa w1 w2)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac q1 s1 q2 xa w1 w2)(*strict*)
   apply(rule disjI2)
   apply(erule disjE)
    apply(rename_tac q1 s1 q2 xa w1 w2)(*strict*)
    apply(simp add: valid_epda_step_label_def may_terminated_by_def F_EPDA_AIA__fp_start_def)
    apply(simp add: append_language_def kleene_star_def)
    apply(clarsimp)
    apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
    apply(rule_tac x="take k w2 @
             take (k - length w2) (drop (length w1) (take k [epda_box G]))" in exI)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
     prefer 2
     apply(rule_tac a="(length w2)" and b="k" in min_alt)
    apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
    apply(erule_tac P="min (length w2) k = length w2 \<and> length w2 \<le> k" in disjE)
     apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
     apply(rule conjI)
      apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
      apply(clarsimp)
     apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
     apply(rule conjI)
      apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
      apply(rule set_take_subset2)
      apply(force)
     apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
     apply(rule set_take_subset2)
     apply(case_tac k)
      apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
      apply(clarsimp)
     apply(rename_tac q2 xa w1 w2 a aa nat)(*strict*)
     apply(clarsimp)
     apply(rename_tac q2 xa w1 w2 a aa nat x)(*strict*)
     apply(case_tac w1)
      apply(rename_tac q2 xa w1 w2 a aa nat x)(*strict*)
      apply(clarsimp)
     apply(rename_tac q2 xa w1 w2 a aa nat x ab list)(*strict*)
     apply(clarsimp)
    apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
    apply(rule conjI)
     apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
     apply(clarsimp)
    apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
    apply(rule conjI)
     apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
     apply(rule set_take_subset2)
     apply(force)
    apply(rename_tac q2 xa w1 w2 a aa)(*strict*)
    apply(force)
   apply(rename_tac q1 s1 q2 xa w1 w2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
   apply(rule_tac x="take k w2 @
             take (k - length w2) (drop (length w1) (take k s))" in exI)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
    apply(case_tac "min (length w2) k = length w2")
     apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
     apply(clarsimp)
    apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
    apply(subgoal_tac "min (length w2) k = k")
     apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
    apply(clarsimp)
   apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
   apply(rule conjI)
    apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
    apply(simp add: valid_epda_step_label_def)
   apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
   apply(rule conjI)
    apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
    apply(rule set_take_subset2)
    apply(simp add: valid_epda_step_label_def may_terminated_by_def append_language_def kleene_star_def)
    apply(force)
   apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
   apply(rule set_take_subset2)
   apply(rule_tac subset_trans)
    apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
    apply(rule set_drop_subset)
   apply(rename_tac q1 q2 xa w1 w2 s)(*strict*)
   apply(rule set_take_subset2)
   apply(force)
  apply(simp add: F_EPDA_AIA__fp_all_have_parent_element_def)
  apply(clarsimp)
  apply(rename_tac q2 s2)(*strict*)
  apply(erule disjE)
   apply(rename_tac q2 s2)(*strict*)
   apply(erule_tac x="q2" in allE)
   apply(erule_tac x="s2" in allE)
   apply(erule impE)
    apply(rename_tac q2 s2)(*strict*)
    apply(force)
   apply(rename_tac q2 s2)(*strict*)
   apply(clarsimp)
   apply(rename_tac q2 q1 x w1 w2 s1)(*strict*)
   apply(rule_tac x="q1" in exI)
   apply(rule_tac x="x" in exI)
   apply(rule_tac x="w1" in exI)
   apply(rule_tac x="w2" in exI)
   apply(rule_tac x="s1" in exI)
   apply(clarsimp)
  apply(rename_tac q2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac q2 q1 s1 x w1 w2)(*strict*)
  apply(rule_tac x="q1" in exI)
  apply(rule_tac x="x" in exI)
  apply(rule_tac x="w1" in exI)
  apply(rule_tac x="w2" in exI)
  apply(rule_tac x="s1" in exI)
  apply(clarsimp)
  done

lemma F_EPDA_AIA__fp_one_mono: "
  E \<subseteq> F_EPDA_AIA__fp_one G k E"
  apply(simp add: F_EPDA_AIA__fp_one_def)
  done

lemma finite_F_EPDA_AIA__codom: "
  valid_epda G
  \<Longrightarrow> finite (F_EPDA_AIA__codom G k)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac h="\<lambda>(q,s). cons_tuple2 q s" and F="(epda_states G \<times> {take k w| w. set w \<subseteq> epda_gamma G})" in finite_imageI)
   apply(rule finite_cartesian_product)
    apply(simp add: F_EPDA_AIA__fp_valid_input_def valid_epda_def)
   apply(rule wordsUpToLengthFinite2)
   apply(simp add: F_EPDA_AIA__fp_valid_input_def valid_epda_def)
  apply(rule_tac
      s="((\<lambda>(q, s). cons_tuple2 q s) `
      (epda_states G \<times> {take k w |w. set w \<subseteq> epda_gamma G}))"
      and t="F_EPDA_AIA__codom G k"
      in ssubst)
   prefer 2
   apply(force)
  apply(simp add: F_EPDA_AIA__codom_def)
  apply(rule antisym)
   apply(clarsimp)
   apply(rule conjI)
    apply(rule inMap)
    apply(rule_tac x="(epda_initial G,take k [epda_box G])" in bexI)
     apply(clarsimp)
     apply(simp add: F_EPDA_AIA__fp_start_def)
    apply(clarsimp)
    apply(simp add: valid_epda_def)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_EPDA_AIA__fp_one_increases_cardinality: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> F_EPDA_AIA__fp_one G k E \<noteq> E
  \<Longrightarrow> card (F_EPDA_AIA__codom G k - F_EPDA_AIA__fp_one G k E) < card (F_EPDA_AIA__codom G k - E)"
  apply(rule Finite_Set.psubset_card_mono)
   prefer 2
   apply(rule rev_subset)
    prefer 3
    apply(rule_tac
      B = "F_EPDA_AIA__codom G k"
      in Finite_Set.finite_subset)
     apply(force)
    prefer 2
    apply(subgoal_tac "E\<subseteq> F_EPDA_AIA__fp_one G k E")
     apply(blast)
    apply(rule F_EPDA_AIA__fp_one_mono)
   prefer 2
   apply(subgoal_tac "F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp_one G k E)")
    prefer 2
    apply(rule F_EPDA_AIA__fp_one_preserves_F_EPDA_AIA__fp_valid_input)
    apply(blast)
   apply(simp add: F_EPDA_AIA__fp_valid_input_def)
  apply(rule finite_F_EPDA_AIA__codom)
  apply(simp add: F_EPDA_AIA__fp_valid_input_def)
  done

lemma F_EPDA_AIA__fp_valid_input_implies_termination: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> F_EPDA_AIA__fp_dom (G, k, E)"
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,k,E). F_EPDA_AIA__fp_valid_input G k E"
      and RECURSIVE_COND = "\<lambda>(G,k,E). F_EPDA_AIA__fp_one G k E\<noteq>E"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,k,E). (G,k,F_EPDA_AIA__fp_one G k E)"
      and MEASURE = "\<lambda>(G,k,E). card (F_EPDA_AIA__codom G k - E)"
      in partial_termination_wf)
      apply(auto)
       apply(rename_tac a aa b x)(*strict*)
       apply(thin_tac "F_EPDA_AIA__fp_valid_input G k E")
       apply(rename_tac G k E x)
       apply(rename_tac G k E x)(*strict*)
       apply(thin_tac "x \<in> F_EPDA_AIA__fp_one G k E")
       apply(subgoal_tac "F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp_one G k E)")
        apply(rename_tac G k E x)(*strict*)
        apply(blast)
       apply(rename_tac G k E x)(*strict*)
       apply(thin_tac "\<not> F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp_one G k E)")
       apply(rule F_EPDA_AIA__fp_one_preserves_F_EPDA_AIA__fp_valid_input)
       apply(blast)
      apply(rename_tac a aa b x)(*strict*)
      apply(thin_tac "F_EPDA_AIA__fp_valid_input G k E")
      apply(rename_tac G k E x)
      apply(rename_tac G k E x)(*strict*)
      apply(thin_tac "x \<in> E")
      apply(subgoal_tac "F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp_one G k E)")
       apply(rename_tac G k E x)(*strict*)
       apply(blast)
      apply(rename_tac G k E x)(*strict*)
      apply(thin_tac "\<not> F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp_one G k E)")
      apply(rule F_EPDA_AIA__fp_one_preserves_F_EPDA_AIA__fp_valid_input)
      apply(blast)
     apply(rename_tac a aa b x)(*strict*)
     apply(thin_tac "F_EPDA_AIA__fp_valid_input G k E")
     apply(rename_tac G k E x)
     apply(rename_tac G k E x)(*strict*)
     apply(case_tac "F_EPDA_AIA__fp_one G k E = E")
      apply(rename_tac G k E x)(*strict*)
      apply(force)
     apply(rename_tac G k E x)(*strict*)
     apply(thin_tac "x \<in> F_EPDA_AIA__fp_one G k E")
     apply(subgoal_tac "card (F_EPDA_AIA__codom G k - F_EPDA_AIA__fp_one G k E) < card (F_EPDA_AIA__codom G k - E)")
      apply(rename_tac G k E x)(*strict*)
      apply(blast)
     apply(rename_tac G k E x)(*strict*)
     apply(thin_tac "\<not> card (F_EPDA_AIA__codom G k - F_EPDA_AIA__fp_one G k E) < card (F_EPDA_AIA__codom G k - E)")
     apply(rule F_EPDA_AIA__fp_one_increases_cardinality)
      apply(rename_tac G k E x)(*strict*)
      apply(blast)
     apply(rename_tac G k E x)(*strict*)
     apply(force)
    apply(rename_tac a aa b x)(*strict*)
    apply(thin_tac "F_EPDA_AIA__fp_valid_input G k E")
    apply(rename_tac G k E x)
    apply(rename_tac G k E x)(*strict*)
    apply(subgoal_tac "E \<subseteq> F_EPDA_AIA__fp_one G k E")
     apply(rename_tac G k E x)(*strict*)
     prefer 2
     apply(rule F_EPDA_AIA__fp_one_mono)
    apply(rename_tac G k E x)(*strict*)
    apply(blast)
   apply(rename_tac a aa b)(*strict*)
   apply(rule F_EPDA_AIA__fp.domintros)
    apply(rename_tac a aa b x)(*strict*)
    apply(force,force)
  apply(rename_tac a aa b)(*strict*)
  apply(rule F_EPDA_AIA__fp.domintros)
   apply(rename_tac a aa b x)(*strict*)
   apply(force,force)
  done

lemma F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_inner: "
  F_EPDA_AIA__fp_valid_input G k N
  \<Longrightarrow> F_EPDA_AIA__fp G k N = F_EPDA_AIA__fp G k (F_EPDA_AIA__fp_one G k N)"
  apply(rule_tac
      t = "F_EPDA_AIA__fp G k N"
      and s = "(if F_EPDA_AIA__fp_one G k N = N then N else F_EPDA_AIA__fp G k (F_EPDA_AIA__fp_one G k N))"
      in ssubst)
   apply(rule F_EPDA_AIA__fp.psimps)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_termination)
   apply(blast)
  apply(clarsimp)
  apply(rule_tac
      t = "F_EPDA_AIA__fp G k N"
      and s = "(if F_EPDA_AIA__fp_one G k N = N then N else F_EPDA_AIA__fp G k (F_EPDA_AIA__fp_one G k N))"
      in ssubst)
   apply(rule F_EPDA_AIA__fp.psimps)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_termination)
   apply(blast)
  apply(clarsimp)
  done

lemma F_EPDA_AIA__fp_Meta_Lift_Without_Argument_With_Argument: "
  F_EPDA_AIA__fp_valid_input G k N
  \<Longrightarrow> (\<And>G k N. F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp_one G k N) \<Longrightarrow> F_EPDA_AIA__fp_valid_input G k N \<Longrightarrow> F_EPDA_AIA__fp_invariants G k N \<Longrightarrow> P G k (F_EPDA_AIA__fp_one G k N) (F_EPDA_AIA__fp G k N) \<Longrightarrow> P G k N (F_EPDA_AIA__fp G k N))
  \<Longrightarrow> (\<And>G k N. F_EPDA_AIA__fp_one G k N = N \<Longrightarrow> F_EPDA_AIA__fp_valid_input G k N \<Longrightarrow> P G k N (F_EPDA_AIA__fp G k N))
  \<Longrightarrow> P G k N (F_EPDA_AIA__fp G k N)"
  apply(subgoal_tac "(\<lambda>G k N. F_EPDA_AIA__fp_invariants G k N \<longrightarrow> (P G k N (F_EPDA_AIA__fp G k N))) G k N")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_F_EPDA_AIA__fp_invariants)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G,k,N). F_EPDA_AIA__fp_invariants G k N \<longrightarrow> (P G k N (F_EPDA_AIA__fp G k N))) (G,k,N)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,k,N). F_EPDA_AIA__fp_valid_input G k N"
      and RECURSIVE_COND = "\<lambda>(G,k,N). F_EPDA_AIA__fp_one G k N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,k,N). (G,k,F_EPDA_AIA__fp_one G k N)"
      and MEASURE = "\<lambda>(G,k,S). card (((F_EPDA_AIA__codom G k))-S)"
      and TERM_FUN = "(\<lambda>(G,k,N). F_EPDA_AIA__fp_invariants G k N \<longrightarrow> (P G k N (F_EPDA_AIA__fp G k N)))"
      and y = "(G,k,N)"
      in partial_termination_wf)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a aa b)(*strict*)
      apply(thin_tac "F_EPDA_AIA__fp_valid_input G k N")
      apply(rename_tac G k N)
      apply(rename_tac G k N)(*strict*)
      apply(rule F_EPDA_AIA__fp_one_preserves_F_EPDA_AIA__fp_valid_input)
      apply(blast)
     apply(thin_tac "F_EPDA_AIA__fp_valid_input G k N")
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rename_tac G k N)
     apply(rename_tac G k N)(*strict*)
     apply(rule F_EPDA_AIA__fp_one_increases_cardinality)
      apply(rename_tac G k N)(*strict*)
      apply(simp add: F_EPDA_AIA__fp_valid_input_def)
     apply(rename_tac G k N)(*strict*)
     apply(simp add: F_EPDA_AIA__fp_valid_input_def)
    apply(simp add: F_EPDA_AIA__fp_valid_input_def)
   prefer 2
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(thin_tac "F_EPDA_AIA__fp_valid_input G k N")
  apply(rename_tac G k N)
  apply(rename_tac G k N)(*strict*)
  apply(erule impE)
   apply(rename_tac G k N)(*strict*)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_F_EPDA_AIA__fp_invariants)
   apply(rename_tac G k N)(*strict*)
   apply(blast)
  apply(rename_tac G k N)(*strict*)
  apply(subgoal_tac "P G k (F_EPDA_AIA__fp_one G k N) (F_EPDA_AIA__fp G k N)")
   apply(rename_tac G k N)(*strict*)
   apply(thin_tac "P G k (F_EPDA_AIA__fp_one G k N) (F_EPDA_AIA__fp G k (F_EPDA_AIA__fp_one G k N))")
   prefer 2
   apply(rule_tac
      t="F_EPDA_AIA__fp G k N"
      and s="F_EPDA_AIA__fp G k (F_EPDA_AIA__fp_one G k N)"
      in ssubst)
    apply(rename_tac G k N)(*strict*)
    apply(rule F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_inner)
    apply(force)
   apply(rename_tac G k N)(*strict*)
   apply(force)
  apply(rename_tac G k N)(*strict*)
  apply(force)
  done

lemma F_EPDA_AIA__fp_mono: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> E \<subseteq> F_EPDA_AIA__fp G k E"
  apply(rule F_EPDA_AIA__fp_Meta_Lift_Without_Argument_With_Argument)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(rule_tac B="F_EPDA_AIA__fp_one Ga ka N" in subset_trans)
    apply(rename_tac Ga ka N)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(simp add: F_EPDA_AIA__fp_one_def)
  apply(rename_tac Ga ka N)(*strict*)
  apply(rule_tac ?x.0="Ga" and ?xa.0="ka" and ?xb.0="N" in F_EPDA_AIA__fp.pelims)
    apply(rename_tac Ga ka N)(*strict*)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_termination)
   apply(force)
  apply(rename_tac Ga ka N Gaa kaa Ea)(*strict*)
  apply(clarsimp)
  done

lemma F_EPDA_AIA__fp_start_in_F_EPDA_AIA__codom: "
  valid_epda G
  \<Longrightarrow> F_EPDA_AIA__fp_start G k \<in> F_EPDA_AIA__codom G k"
  apply(simp add: F_EPDA_AIA__fp_start_def F_EPDA_AIA__codom_def)
  done

lemma F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start: "
  valid_epda G
  \<Longrightarrow> F_EPDA_AIA__fp_valid_input G k {F_EPDA_AIA__fp_start G k}"
  apply(simp add: F_EPDA_AIA__fp_valid_input_def)
  apply(rule conjI)
   apply(rule F_EPDA_AIA__fp_start_in_F_EPDA_AIA__codom)
   apply(force)
  apply(simp add: F_EPDA_AIA__fp_all_have_parent_element_def)
  done

definition F_EPDA_AIA__fp_computed_stack_approximation :: "
  (('state, 'event, 'stack) epda_step_label, ('state, 'event, 'stack) epdaH_conf) derivation
  \<Rightarrow> nat
  \<Rightarrow> nat
  \<Rightarrow> nat"
  where
    "F_EPDA_AIA__fp_computed_stack_approximation d i k \<equiv>
  foldl
    (\<lambda>n e. min k (n - length (edge_pop e) + length (edge_push e)))
    (min k (Suc 0))
    (map (\<lambda>i. the (get_label (d i))) (nat_seq (Suc 0) i))"

definition F_EPDA_AIA__fp_one_step_contained :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> bool"
  where
    "F_EPDA_AIA__fp_one_step_contained G k E \<equiv>
  \<forall>d i e1 c1 e2 c2.
  epdaH.derivation_initial G d
  \<longrightarrow> d i = Some (pair e1 c1)
  \<longrightarrow> d (Suc i) = Some (pair (Some e2) c2)
  \<longrightarrow> (\<exists>w1 w2.
          cons_tuple2 (epdaH_conf_state c1) (take k w1) \<in> E
          \<and> cons_tuple2 (epdaH_conf_state c2) (take k w2) \<in> E
          \<and> cons_tuple2 (epdaH_conf_state c2) (take k w2) \<in> F_EPDA_AIA__fp_one G k {cons_tuple2 (epdaH_conf_state c1) (take k w1)}
          \<and> w1 = take (F_EPDA_AIA__fp_computed_stack_approximation d i k) (epdaH_conf_stack c1)
          \<and> w2 = take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k) (epdaH_conf_stack c2))"

lemma F_EPDA_AIA__fp_Meta_Lift_Without_Argument: "
  F_EPDA_AIA__fp_valid_input G k N
  \<Longrightarrow> (\<And>G k N. F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp_one G k N) \<Longrightarrow> F_EPDA_AIA__fp_valid_input G k N \<Longrightarrow> F_EPDA_AIA__fp_invariants G k N \<Longrightarrow> P G k (F_EPDA_AIA__fp G k (F_EPDA_AIA__fp_one G k N)) \<Longrightarrow> P G k (F_EPDA_AIA__fp G k N))
  \<Longrightarrow> (\<And>G k N. F_EPDA_AIA__fp_one G k N = N \<Longrightarrow> F_EPDA_AIA__fp_valid_input G k N \<Longrightarrow> F_EPDA_AIA__fp_invariants G k N \<Longrightarrow> P G k (F_EPDA_AIA__fp G k N))
  \<Longrightarrow> P G k (F_EPDA_AIA__fp G k N)"
  apply(subgoal_tac "(\<lambda>G k N. F_EPDA_AIA__fp_invariants G k N \<longrightarrow> (P G k (F_EPDA_AIA__fp G k N))) G k N")
   apply(erule impE)
    prefer 2
    apply(blast)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_F_EPDA_AIA__fp_invariants)
   apply(blast)
  apply(subgoal_tac "(\<lambda>(G,k,N). F_EPDA_AIA__fp_invariants G k N \<longrightarrow> (P G k (F_EPDA_AIA__fp G k N))) (G,k,N)")
   apply(blast)
  apply(rule_tac
      TERM_ARGS_TEST = "\<lambda>(G,k,N). F_EPDA_AIA__fp_valid_input G k N"
      and RECURSIVE_COND = "\<lambda>(G,k,N). F_EPDA_AIA__fp_one G k N\<noteq>N"
      and MODIFY_ARGS_FOR_REC_CALL = "\<lambda>(G,k,N). (G,k,F_EPDA_AIA__fp_one G k N)"
      and MEASURE = "\<lambda>(G,k,S). card (((F_EPDA_AIA__codom G k))-S)"
      and TERM_FUN = "(\<lambda>(G,k,N). F_EPDA_AIA__fp_invariants G k N \<longrightarrow> (P G k (F_EPDA_AIA__fp G k N)))"
      and y = "(G,k,N)"
      in partial_termination_wf)
      apply(rule allI)
      apply(rename_tac x)(*strict*)
      apply(clarify)
      apply(rename_tac a aa b)(*strict*)
      apply(thin_tac "F_EPDA_AIA__fp_valid_input G k N")
      apply(rename_tac G k N)
      apply(rename_tac G k N)(*strict*)
      apply(rule F_EPDA_AIA__fp_one_preserves_F_EPDA_AIA__fp_valid_input)
      apply(blast)
     apply(thin_tac "F_EPDA_AIA__fp_valid_input G k N")
     apply(clarsimp)
     apply(rename_tac a aa b)(*strict*)
     apply(rename_tac G k N)
     apply(rename_tac G k N)(*strict*)
     apply(rule F_EPDA_AIA__fp_one_increases_cardinality)
      apply(rename_tac G k N)(*strict*)
      apply(simp add: F_EPDA_AIA__fp_valid_input_def)
     apply(rename_tac G k N)(*strict*)
     apply(simp add: F_EPDA_AIA__fp_valid_input_def)
    apply(simp add: F_EPDA_AIA__fp_valid_input_def)
   prefer 2
   apply(clarsimp)
  apply(clarsimp)
  apply(rename_tac a aa b)(*strict*)
  apply(erule impE)
   apply(rename_tac a aa b)(*strict*)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_F_EPDA_AIA__fp_invariants)
   apply(rename_tac a aa b)(*strict*)
   apply(blast)
  apply(rename_tac a aa b)(*strict*)
  apply(blast)
  done

lemma F_EPDA_AIA__fp_one_intro2: "
  cons_tuple2 q1 s1 \<in> E
  \<Longrightarrow> \<lparr>edge_src = q1, edge_event = x, edge_pop = w1, edge_push = w2, edge_trg = q2\<rparr> \<in> epda_delta G
  \<Longrightarrow> s2 = take k (w2 @ (drop (length w1) s1))
  \<Longrightarrow> prefix s1 w1 \<or> prefix w1 s1
  \<Longrightarrow> cons_tuple2 q2 s2 \<in> F_EPDA_AIA__fp_one G k E"
  apply(simp add: F_EPDA_AIA__fp_one_def)
  apply(force)
  done

lemma F_EPDA_AIA__fp_one_intro3: "
  cons_tuple2 q1 s1 \<in> E
  \<Longrightarrow> F_EPDA_AIA__fp_one G k E = E
  \<Longrightarrow> \<lparr>edge_src = q1, edge_event = x, edge_pop = w1, edge_push = w2, edge_trg = q2\<rparr> \<in> epda_delta G
  \<Longrightarrow> s2 = take k (w2 @ (drop (length w1) s1))
  \<Longrightarrow> prefix s1 w1 \<or> prefix w1 s1
  \<Longrightarrow> cons_tuple2 q2 s2 \<in> E \<and> cons_tuple2 q2 s2 \<in> F_EPDA_AIA__fp_one G k {cons_tuple2 q1 s1}"
  apply(rule conjI)
   apply(rule_tac t="E" and s="F_EPDA_AIA__fp_one G k E" in ssubst)
    apply(force)
   apply(rule F_EPDA_AIA__fp_one_intro2)
      apply(force)
     apply(force)
    apply(force)
   apply(force)
  apply(rule F_EPDA_AIA__fp_one_intro2)
     apply(force)
    apply(force)
   apply(force)
  apply(force)
  done

lemma F_EPDA_AIA__fp_computed_stack_approximation_smaller_than_k: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d i = Some (pair (Some e) c)
  \<Longrightarrow> F_EPDA_AIA__fp_computed_stack_approximation d i k \<le> k"
  apply(simp add: F_EPDA_AIA__fp_computed_stack_approximation_def)
  apply(case_tac i)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) 0 = []")
    apply(clarsimp)
   apply (metis derivation_configuration.inject epdaH.derivation_initial_has_configuration_at_position_0 option.distinct(1) option.sel)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac i)
  apply(rename_tac i)(*strict*)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc i) = nat_seq (Suc 0) (i) @[Suc i]")
   apply(rename_tac i)(*strict*)
   prefer 2
   apply (metis append_Cons append_assoc natUptTo_n_Sucn nat_seq_drop_last_prime self_append_conv2)
  apply(rename_tac i)(*strict*)
  apply(force)
  done

lemma F_EPDA_AIA__fp_computed_stack_approximation_unfold: "
  d (Suc i) = Some (pair (Some e) c)
  \<Longrightarrow> edge_pop e = po
  \<Longrightarrow> edge_push e = pu
  \<Longrightarrow> F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k = min k (F_EPDA_AIA__fp_computed_stack_approximation d i k - length po + length pu)"
  apply(simp add: F_EPDA_AIA__fp_computed_stack_approximation_def)
  apply(rule_tac t="nat_seq (Suc 0) (Suc i)" and s="nat_seq (Suc 0) i @ [Suc i]" in ssubst)
   apply (metis append_Cons append_assoc natUptTo_n_Sucn nat_seq_drop_last_prime self_append_conv2)
  apply(rule_tac t="foldl
     (\<lambda>n e. min k (n - length (edge_pop e) + length (edge_push e)))
     (min k (Suc 0))
     (map (\<lambda>i. the (get_label (d i)))
       (nat_seq (Suc 0) i @ [Suc i]))" and s="(\<lambda>n e. min k (n - length (edge_pop e) + length (edge_push e))) (foldl
     (\<lambda>n e. min k (n - length (edge_pop e) + length (edge_push e)))
     (min k (Suc 0))
     (map (\<lambda>i. the (get_label (d i)))
       (nat_seq (Suc 0) i))) e" in ssubst)
   apply(clarsimp)
   apply(simp add: get_label_def)
  apply(clarsimp)
  done

lemma F_EPDA_AIA__fp_some_tuple_reachable_hlp2: "
  F_EPDA_AIA__fp_one G k E = E
  \<Longrightarrow> F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> F_EPDA_AIA__fp_invariants G k E
  \<Longrightarrow> F_EPDA_AIA__fp G k E = E
  \<Longrightarrow> F_EPDA_AIA__fp_dom (G, k, E)
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e1 c1)
  \<Longrightarrow> d (Suc i) = Some (pair (Some e2) c2)
  \<Longrightarrow> \<exists>w1 w2. cons_tuple2 (epdaH_conf_state c1) (take k w1) \<in> E \<and> cons_tuple2 (epdaH_conf_state c2) (take k w2) \<in> E \<and> cons_tuple2 (epdaH_conf_state c2) (take k w2) \<in> F_EPDA_AIA__fp_one G k {cons_tuple2 (epdaH_conf_state c1) (take k w1) } \<and> w1 = take (F_EPDA_AIA__fp_computed_stack_approximation d i k) (epdaH_conf_stack c1) \<and> w2 = take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k) (epdaH_conf_stack c2)"
  apply(induct i arbitrary: e1 c1 e2 c2)
   apply(rename_tac e1 c1 e2 c2)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e1 c1 e2 c2)(*strict*)
    prefer 2
    apply(rule_tac
      d="d" and
      n="0" and
      m="Suc 0"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac e1 c1 e2 c2)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac e1 c1 e2 c2)(*strict*)
   apply(clarsimp)
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e1 c1 e2 c2 w)(*strict*)
   apply(case_tac c1)
   apply(rename_tac e1 c1 e2 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(case_tac c2)
   apply(rename_tac e1 c1 e2 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa)(*strict*)
   apply(case_tac e2)
   apply(rename_tac e1 c1 e2 c2 w epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka epdaH_conf_stateaa epdaH_conf_historyaa epdaH_conf_stackaa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(rename_tac q1 h1 s1 q2 h2 s2 qs r po pu qt)
   apply(rename_tac e1 c1 e2 c2 w q1 h1 s1 q2 h2 s2 qs r po pu qt)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 w h1 qs r po pu qt)(*strict*)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def F_EPDA_AIA__fp_invariants_def F_EPDA_AIA__fp_invariant_01_def F_EPDA_AIA__fp_start_def)
   apply(clarsimp)
   apply(rename_tac w r po pu qt)(*strict*)
   apply(simp add: F_EPDA_AIA__fp_computed_stack_approximation_def)
   apply(subgoal_tac "nat_seq (Suc 0) 0 = []")
    apply(rename_tac w r po pu qt)(*strict*)
    prefer 2
    apply (metis append_Cons append_assoc natUptTo_n_Sucn nat_seq_drop_last_prime self_append_conv2)
   apply(rename_tac w r po pu qt)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "nat_seq (Suc 0) (Suc 0) = [Suc 0]")
    apply(rename_tac w r po pu qt)(*strict*)
    prefer 2
    apply (metis append_Cons append_assoc natUptTo_n_Sucn nat_seq_drop_last_prime self_append_conv2)
   apply(rename_tac w r po pu qt)(*strict*)
   apply(clarsimp)
   apply(simp add: get_label_def)
   apply(case_tac k)
    apply(rename_tac w r po pu qt)(*strict*)
    apply(clarsimp)
    apply(rule F_EPDA_AIA__fp_one_intro3)
        apply(rename_tac w r po pu qt)(*strict*)
        apply(force)
       apply(rename_tac w r po pu qt)(*strict*)
       apply(force)
      apply(rename_tac w r po pu qt)(*strict*)
      apply(force)
     apply(rename_tac w r po pu qt)(*strict*)
     apply(force)
    apply(rename_tac w r po pu qt)(*strict*)
    apply(simp add: prefix_def)
   apply(rename_tac w r po pu qt nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac k)
   apply(rename_tac w r po pu qt k)(*strict*)
   apply(case_tac po)
    apply(rename_tac w r po pu qt k)(*strict*)
    apply(clarsimp)
    apply(rename_tac r pu qt k)(*strict*)
    apply(rule F_EPDA_AIA__fp_one_intro3)
        apply(rename_tac r pu qt k)(*strict*)
        apply(force)
       apply(rename_tac r pu qt k)(*strict*)
       apply(force)
      apply(rename_tac r pu qt k)(*strict*)
      apply(force)
     apply(rename_tac r pu qt k)(*strict*)
     prefer 2
     apply(simp add: prefix_def)
    apply(rename_tac r pu qt k)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     apply(rename_tac r pu qt k)(*strict*)
     prefer 2
     apply(rule_tac b="(length pu)" and a="k" in min_alt)
    apply(rename_tac r pu qt k)(*strict*)
    apply(erule disjE)
     apply(rename_tac r pu qt k)(*strict*)
     apply(clarsimp)
    apply(rename_tac r pu qt k)(*strict*)
    apply(clarsimp)
   apply(rename_tac w r po pu qt k a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac r pu qt k)(*strict*)
   apply(rule F_EPDA_AIA__fp_one_intro3)
       apply(rename_tac r pu qt k)(*strict*)
       apply(force)
      apply(rename_tac r pu qt k)(*strict*)
      apply(force)
     apply(rename_tac r pu qt k)(*strict*)
     apply(force)
    apply(rename_tac r pu qt k)(*strict*)
    prefer 2
    apply(simp add: prefix_def)
   apply(rename_tac r pu qt k)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac r pu qt k)(*strict*)
    prefer 2
    apply(rule_tac b="(length pu)" and a="Suc k" in min_alt)
   apply(rename_tac r pu qt k)(*strict*)
   apply(erule disjE)
    apply(rename_tac r pu qt k)(*strict*)
    apply(clarsimp)
   apply(rename_tac r pu qt k)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e1 c1 e2 c2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e1 c1 e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="i" and
      m="Suc i"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac i e1 c1 e2 c2)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac i e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac i e1 c1 e2 c2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e1 c1 e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="Suc i" and
      m="Suc (Suc i)"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac i e1 c1 e2 c2)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac i e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac i e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac i e1 c1 e2 c2)(*strict*)
  apply(erule exE)+
  apply(rename_tac i e1 c1 e2 c2 e1a e1b e2a e2b c1a c1b c2a c2b)(*strict*)
  apply(clarsimp)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a)(*strict*)
  apply(erule_tac x="e1a" in meta_allE)
  apply(clarsimp)
  apply(erule_tac x="c1a" in meta_allE)
  apply(clarsimp)
  apply(erule_tac x="e2a" in meta_allE)
  apply(clarsimp)
  apply(erule_tac x="c1" in meta_allE)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa)(*strict*)
  apply(case_tac c1a)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q2 h2 s2)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1 q2 h2 s2)(*strict*)
  apply(case_tac c2)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1 q2 h2 s2 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac q3 h3 s3)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1 q2 h2 s2 q3 h3 s3)(*strict*)
  apply(case_tac e2)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1 q2 h2 s2 q3 h3 s3 edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs1 r1 po1 pu1 qt1)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1 q2 h2 s2 q3 h3 s3 qs1 r1 po1 pu1 qt1)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1 q2 h2 s2 q3 h3 s3 qs1 r1 po1 pu1 qt1 edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac qs2 r2 po2 pu2 qt2)
  apply(rename_tac i c1 e2 c2 e1a e2a c1a w wa q1 h1 s1 q2 h2 s2 q3 h3 s3 qs1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(rule F_EPDA_AIA__fp_one_intro3)
      apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
      prefer 2
      apply(force)
     apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(force)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(case_tac "min k (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k) - length po1")
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(rule disjI1)
    apply(clarsimp)
    apply(simp add: prefix_def)
    apply(rule_tac x="drop (min k (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k)) po1" in exI)
    apply(rule append_take_drop_id)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2 nat)(*strict*)
   apply(rule disjI2)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(rule_tac x="take (Suc nat) w" in exI)
   apply(clarsimp)
   apply(rule sym)
   apply(rule take_all)
   apply(force)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(subgoal_tac "F_EPDA_AIA__fp_computed_stack_approximation d (Suc (Suc i)) k \<le> k")
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(rule F_EPDA_AIA__fp_computed_stack_approximation_smaller_than_k)
     apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
     apply(simp add: F_EPDA_AIA__fp_valid_input_def)
     apply(force)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(force)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(force)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(subgoal_tac "F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i)) k \<le> k")
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(rule F_EPDA_AIA__fp_computed_stack_approximation_smaller_than_k)
     apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
     apply(simp add: F_EPDA_AIA__fp_valid_input_def)
     apply(force)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(force)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(force)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "min k (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (Suc i)) k) = (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (Suc i)) k)")
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(subgoal_tac "min k (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k) = (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i)) k)")
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(rule_tac t="F_EPDA_AIA__fp_computed_stack_approximation d (Suc (Suc i)) k" and s="
  min k (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k - length po1 + length pu1)" in ssubst)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(rule F_EPDA_AIA__fp_computed_stack_approximation_unfold)
     apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
     apply(force)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(force)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(force)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(rule_tac a="length pu1" and b="k" in min_alt)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(erule disjE)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule_tac t="(min k
          (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k - length po1 + length pu1))" and s="k" in ssubst)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(force)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(clarsimp)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(rule_tac a="length po1" and b="F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k" in min_alt)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(erule disjE)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(rule_tac b="(F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k + length pu1 - length po1)" and a="k" in min_alt)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(erule disjE)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    prefer 2
    apply(rule_tac a="k - length pu1" and  b="(F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k - length po1)" in min_alt)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(erule disjE)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(clarsimp)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(clarsimp)
   apply(rule_tac t="F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k - length po1" and s="k-length pu1" in ssubst)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(rule antisym)
     apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
     apply(force)
    apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
    apply(rule to_mutual_sub1)
    apply(force)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   apply(force)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(rule_tac a="k - length pu1" and  b="(F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k - length po1)" in min_alt)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(erule disjE)
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k - length po1 \<le> k - length pu1")
   apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
   prefer 2
   apply(rule to_mutual_sub2)
   apply(force)
  apply(rename_tac i e1a w wa h1 r1 po1 pu1 qt1 qs2 r2 po2 pu2 qt2)(*strict*)
  apply(force)
  done

lemma F_EPDA_AIA__fp_some_tuple_reachable_hlp1: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> \<forall>d i e1 c1 e2 c2. epdaH.derivation_initial G d \<longrightarrow> d i = Some (pair e1 c1) \<longrightarrow> d (Suc i) = Some (pair (Some e2) c2) \<longrightarrow> (\<exists>w1 w2. cons_tuple2 (epdaH_conf_state c1) (take k w1) \<in> (F_EPDA_AIA__fp G k E) \<and> cons_tuple2 (epdaH_conf_state c2) (take k w2) \<in> (F_EPDA_AIA__fp G k E) \<and> cons_tuple2 (epdaH_conf_state c2) (take k w2) \<in> F_EPDA_AIA__fp_one G k {cons_tuple2 (epdaH_conf_state c1) (take k w1) } \<and> w1 = take (F_EPDA_AIA__fp_computed_stack_approximation d i k) (epdaH_conf_stack c1) \<and> w2 = take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k) (epdaH_conf_stack c2))"
  apply(rule_tac P="\<lambda>Ga ka N. \<forall>d i e1 c1 e2 c2.
          epdaH.derivation_initial Ga
           d \<longrightarrow>
          d i = Some (pair e1 c1) \<longrightarrow>
          d (Suc i) = Some (pair (Some e2) c2) \<longrightarrow>
          (\<exists>w1 w2.
              cons_tuple2 (epdaH_conf_state c1) (take ka w1) \<in> N \<and>
              cons_tuple2 (epdaH_conf_state c2) (take ka w2) \<in> N \<and>
              cons_tuple2 (epdaH_conf_state c2) (take ka w2)
              \<in> F_EPDA_AIA__fp_one Ga ka
                  {cons_tuple2 (epdaH_conf_state c1) (take ka w1)} \<and>
              w1 = take (F_EPDA_AIA__fp_computed_stack_approximation d i ka) (epdaH_conf_stack c1) \<and>
              w2 = take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) ka) (epdaH_conf_stack c2))" in F_EPDA_AIA__fp_Meta_Lift_Without_Argument)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(rule_tac t="(F_EPDA_AIA__fp Ga ka N)"  and s="(F_EPDA_AIA__fp Ga ka (F_EPDA_AIA__fp_one Ga ka N))" in ssubst)
    apply(rename_tac Ga ka N)(*strict*)
    apply(rule F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_inner)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(force)
  apply(rename_tac Ga ka N)(*strict*)
  apply(rule_tac ?x.0="Ga" and ?xa.0="ka" and ?xb.0="N" in F_EPDA_AIA__fp.pelims)
    apply(rename_tac Ga ka N)(*strict*)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_termination)
   apply(force)
  apply(rename_tac Ga ka N Gaa kaa Ea)(*strict*)
  apply(clarsimp)
  apply(rename_tac Ga ka Ea d i e1 c1 e2 c2)(*strict*)
  apply(thin_tac "X" for X)
  apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
   prefer 2
   apply(rule_tac i="i" in F_EPDA_AIA__fp_some_tuple_reachable_hlp2)
          apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
          apply(force)
         apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
         apply(force)
        apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
        apply(force)
       apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
       apply(force)
      apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
      apply(force)
     apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac Ga ka E d i e1 c1 e2 c2)(*strict*)
  apply(force)
  done

theorem F_EPDA_AIA__fp_some_tuple_reachable: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e1 c1)
  \<Longrightarrow> d (Suc i) = Some (pair (Some e2) c2)
  \<Longrightarrow> \<exists>w1 w2. cons_tuple2 (epdaH_conf_state c1) (take k w1) \<in> (F_EPDA_AIA__fp G k E) \<and> cons_tuple2 (epdaH_conf_state c2) (take k w2) \<in> (F_EPDA_AIA__fp G k E) \<and> cons_tuple2 (epdaH_conf_state c2) (take k w2) \<in> F_EPDA_AIA__fp_one G k {cons_tuple2 (epdaH_conf_state c1) (take k w1) } \<and> w1 = take (F_EPDA_AIA__fp_computed_stack_approximation d i k) (epdaH_conf_stack c1) \<and> w2 = take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k) (epdaH_conf_stack c2)"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule F_EPDA_AIA__fp_some_tuple_reachable_hlp1)
   apply(force)
  apply(force)
  done

theorem F_EPDA_AIA__fp_enforces_F_EPDA_AIA__fp_one_step_contained: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> F_EPDA_AIA__fp_one_step_contained G k (F_EPDA_AIA__fp G k E)"
  apply(simp only: F_EPDA_AIA__fp_one_step_contained_def)
  apply(rule allI)+
  apply(rename_tac d i e1 c1 e2 c2)(*strict*)
  apply(rule impI)+
  apply(rule_tac F_EPDA_AIA__fp_some_tuple_reachable)
     apply(rename_tac d i e1 c1 e2 c2)(*strict*)
     apply(force)
    apply(rename_tac d i e1 c1 e2 c2)(*strict*)
    apply(force)
   apply(rename_tac d i e1 c1 e2 c2)(*strict*)
   apply(force)
  apply(rename_tac d i e1 c1 e2 c2)(*strict*)
  apply(force)
  done

theorem F_EPDA_AIA__fp_identifies_only_useless_states: "
  valid_epda G
  \<Longrightarrow> Q = {q | q s. cons_tuple2 q s \<in> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}}
  \<Longrightarrow> q \<in> epda_states G - Q
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e c)
  \<Longrightarrow> epdaH_conf_state c = q
  \<Longrightarrow> False"
  apply(clarsimp)
  apply(case_tac i)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
   apply(clarsimp)
   apply(case_tac c)
   apply(rename_tac epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(clarsimp)
   apply(erule_tac x="take k [epda_box G]" in allE)
   apply(fold F_EPDA_AIA__fp_start_def)
   apply(subgoal_tac "F_EPDA_AIA__fp_start G k \<in> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}")
    apply(force)
   apply(rule_tac A="{F_EPDA_AIA__fp_start G k}" in set_mp)
    prefer 2
    apply(force)
   apply(rule F_EPDA_AIA__fp_mono)
   apply(rule F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="nat" and
      m="Suc nat"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac nat)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 e2 c1)(*strict*)
  apply(subgoal_tac "F_EPDA_AIA__fp_one_step_contained G k (F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k})")
   apply(rename_tac nat e1 e2 c1)(*strict*)
   prefer 2
   apply(rule F_EPDA_AIA__fp_enforces_F_EPDA_AIA__fp_one_step_contained)
   apply(rule F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start)
   apply(force)
  apply(rename_tac nat e1 e2 c1)(*strict*)
  apply(simp add: F_EPDA_AIA__fp_one_step_contained_def)
  apply(erule_tac x="d" in allE)
  apply(clarsimp)
  apply(erule_tac x="nat" in allE)
  apply(force)
  done

lemma F_EPDA_AIA_preserves_epdaH_accessible_states: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_states G \<subseteq> {q | q s. cons_tuple2 q s \<in> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}}"
  apply(simp add: epdaH_accessible_states_def)
  apply(clarsimp)
  apply(rename_tac d n e c)(*strict*)
  apply(case_tac " \<exists>s. cons_tuple2 (epdaH_conf_state c) s
           \<in> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}")
   apply(rename_tac d n e c)(*strict*)
   apply(force)
  apply(rename_tac d n e c)(*strict*)
  apply(clarsimp)
  apply(rule_tac k="k" in F_EPDA_AIA__fp_identifies_only_useless_states)
       apply(rename_tac d n e c)(*strict*)
       apply(force)
      apply(rename_tac d n e c)(*strict*)
      apply(force)
     apply(rename_tac d n e c)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac d n e c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac d n e c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac d n e c)(*strict*)
  apply(clarsimp)
  apply(thin_tac "\<forall>s. cons_tuple2 (epdaH_conf_state c) s
           \<notin> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}")
  apply(subgoal_tac "c \<in> epdaH_configurations G")
   apply(rename_tac d n e c)(*strict*)
   apply(simp add: epdaH_configurations_def)
   apply(force)
  apply(rename_tac d n e c)(*strict*)
  apply (metis epdaH.derivation_initial_configurations)
  done

theorem F_EPDA_AIA__fp_identifies_only_useless_edges: "
  valid_epda G
  \<Longrightarrow> D = {e | q s e. cons_tuple2 q s \<in> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k} \<and> edge_src e = q \<and> (prefix (edge_pop e) s \<or> prefix s (edge_pop e)) }
  \<Longrightarrow> e \<in> epda_delta G - D
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d i = Some (pair (Some e) c)
  \<Longrightarrow> False"
  apply(clarsimp)
  apply(case_tac i)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nat)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="nat" and
      m="Suc nat"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac nat)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac nat)(*strict*)
    apply(force)
   apply(rename_tac nat)(*strict*)
   apply(force)
  apply(rename_tac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac nat e1 c1)(*strict*)
  apply(subgoal_tac "F_EPDA_AIA__fp_one_step_contained G k (F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k})")
   apply(rename_tac nat e1 c1)(*strict*)
   prefer 2
   apply(rule F_EPDA_AIA__fp_enforces_F_EPDA_AIA__fp_one_step_contained)
   apply(rule F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start)
   apply(force)
  apply(rename_tac nat e1 c1)(*strict*)
  apply(case_tac nat)
   apply(rename_tac nat e1 c1)(*strict*)
   apply(clarsimp)
   apply(rename_tac e1 c1)(*strict*)
   apply(simp add: F_EPDA_AIA__fp_one_step_contained_def)
   apply(erule_tac x="d" in allE)
   apply(clarsimp)
   apply(erule_tac x="0" in allE)
   apply(clarsimp)
   apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac c1 w)(*strict*)
   apply(case_tac e)
   apply(rename_tac c1 w edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
   apply(rename_tac q r po pu q')
   apply(rename_tac c1 w q r po pu q')(*strict*)
   apply(case_tac c)
   apply(rename_tac c1 w q r po pu q' epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(rename_tac q1 h1 s1)
   apply(rename_tac c1 w q r po pu q' q1 h1 s1)(*strict*)
   apply(case_tac c1)
   apply(rename_tac c1 w q r po pu q' q1 h1 s1 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
   apply(rename_tac q2 h2 s2)
   apply(rename_tac c1 w q r po pu q' q1 h1 s1 q2 h2 s2)(*strict*)
   apply(clarsimp)
   apply(rename_tac w r po pu q')(*strict*)
   apply(erule_tac x="take k [epda_box G]" in allE)
   apply(erule impE)
    apply(rename_tac w r po pu q')(*strict*)
    apply(fold F_EPDA_AIA__fp_start_def)
    apply(rule_tac A="{F_EPDA_AIA__fp_start G k}" in set_mp)
     apply(rename_tac w r po pu q')(*strict*)
     apply(rule F_EPDA_AIA__fp_mono)
     apply(rule F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start)
     apply(force)
    apply(rename_tac w r po pu q')(*strict*)
    apply(clarsimp)
   apply(rename_tac w r po pu q')(*strict*)
   apply(simp add: prefix_def)
   apply(clarsimp)
   apply(case_tac po)
    apply(rename_tac w r po pu q')(*strict*)
    apply(force)
   apply(rename_tac w r po pu q' a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac r pu q')(*strict*)
   apply(case_tac k)
    apply(rename_tac r pu q')(*strict*)
    apply(force)
   apply(force)
  apply(rename_tac nat e1 c1 nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1 c1 nata)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e1 c1 nata)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="nata" and
      m="Suc nata"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac e1 c1 nata)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac e1 c1 nata)(*strict*)
    apply(force)
   apply(rename_tac e1 c1 nata)(*strict*)
   apply(force)
  apply(rename_tac e1 c1 nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac c1 nata e1a e2 c1a)(*strict*)
  apply(simp add: F_EPDA_AIA__fp_one_step_contained_def)
  apply(erule_tac x="d" in allE)
  apply(clarsimp)
  apply(erule_tac x="nata" in allE)
  apply(clarsimp)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac c1 nata e1a e2 c1a w wa)(*strict*)
  apply(case_tac e)
  apply(rename_tac c1 nata e1a e2 c1a w wa edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac q2 r2 po2 pu2 q2')
  apply(rename_tac c1 nata e1a e2 c1a w wa q2 r2 po2 pu2 q2')(*strict*)
  apply(case_tac e2)
  apply(rename_tac c1 nata e1a e2 c1a w wa q2 r2 po2 pu2 q2' edge_srca edge_eventa edge_popa edge_pusha edge_trga)(*strict*)
  apply(rename_tac q1 r1 po1 pu1 q1')
  apply(rename_tac c1 nata e1a e2 c1a w wa q2 r2 po2 pu2 q2' q1 r1 po1 pu1 q1')(*strict*)
  apply(case_tac c)
  apply(rename_tac c1 nata e1a e2 c1a w wa q2 r2 po2 pu2 q2' q1 r1 po1 pu1 q1' epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac p1 h1 s1)
  apply(rename_tac c1 nata e1a e2 c1a w wa q2 r2 po2 pu2 q2' q1 r1 po1 pu1 q1' p1 h1 s1)(*strict*)
  apply(case_tac c1)
  apply(rename_tac c1 nata e1a e2 c1a w wa q2 r2 po2 pu2 q2' q1 r1 po1 pu1 q1' p1 h1 s1 epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac p2 h2 s2)
  apply(rename_tac c1 nata e1a e2 c1a w wa q2 r2 po2 pu2 q2' q1 r1 po1 pu1 q1' p1 h1 s1 p2 h2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac nata e1a c1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1')(*strict*)
  apply(case_tac c1a)
  apply(rename_tac nata e1a c1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' epdaH_conf_statea epdaH_conf_historya epdaH_conf_stacka)(*strict*)
  apply(rename_tac p3 h3 s3)
  apply(rename_tac nata e1a c1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' p3 h3 s3)(*strict*)
  apply(clarsimp)
  apply(rename_tac nata e1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' p3 h3)(*strict*)
  apply(erule_tac x="X" for X in allE)
  apply(erule impE)
   apply(rename_tac nata e1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' p3 h3)(*strict*)
   apply(force)
  apply(rename_tac nata e1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' p3 h3)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac nata e1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' p3 h3)(*strict*)
   prefer 2
   apply(rule_tac a="(min k (F_EPDA_AIA__fp_computed_stack_approximation d (Suc nata) k))" and b="length po2" in min_alt)
  apply(rename_tac nata e1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' p3 h3)(*strict*)
  apply(erule disjE)
   apply(rename_tac nata e1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' p3 h3)(*strict*)
   apply(clarsimp)
   apply(simp add: prefix_def)
   apply(erule_tac x="drop (min k (F_EPDA_AIA__fp_computed_stack_approximation d (Suc nata) k)) po2" in allE)+
   apply(force)
  apply(rename_tac nata e1a w wa r2 po2 pu2 q2' r1 po1 pu1 q1' p3 h3)(*strict*)
  apply(clarsimp)
  apply(simp add: prefix_def)
  done

lemma F_EPDA_AIA_preserves_epdaH_accessible_edges: "
  valid_epda G
  \<Longrightarrow> epdaH_accessible_edges G \<subseteq> {e | q s e. e \<in> epda_delta G \<and> cons_tuple2 q s \<in> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k} \<and> edge_src e = q \<and> (prefix (edge_pop e) s \<or> prefix s (edge_pop e))}"
  apply(simp add: epdaH_accessible_edges_def)
  apply(clarsimp)
  apply(rename_tac x d n c)(*strict*)
  apply(case_tac " \<exists>s. cons_tuple2 (edge_src x) s
           \<in> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k} \<and>
           (edge_pop x \<sqsubseteq> s \<or> s \<sqsubseteq> edge_pop x)")
   apply(rename_tac x d n c)(*strict*)
   apply(force)
  apply(rename_tac x d n c)(*strict*)
  apply(subgoal_tac "False")
   apply(rename_tac x d n c)(*strict*)
   apply(force)
  apply(rename_tac x d n c)(*strict*)
  apply(rule_tac k="k" in F_EPDA_AIA__fp_identifies_only_useless_edges)
      apply(rename_tac x d n c)(*strict*)
      apply(force)
     apply(rename_tac x d n c)(*strict*)
     apply(force)
    apply(rename_tac x d n c)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac x d n c)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x d n c)(*strict*)
  apply(clarsimp)
  done

definition F_EPDA_AIA__SpecInput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> bool"
  where
    "F_EPDA_AIA__SpecInput G k \<equiv>
  valid_epda G"

definition F_EPDA_AIA__SpecOutput :: "
  ('state, 'event, 'stack) epda
  \<Rightarrow> nat
  \<Rightarrow> ('state, 'stack list) DT_tuple2 set
  \<Rightarrow> bool"
  where
    "F_EPDA_AIA__SpecOutput G k E \<equiv>
  epdaH_accessible_edges G \<subseteq>
    {e | q s e.
      e \<in> epda_delta G
      \<and> cons_tuple2 q s \<in> E
      \<and> edge_src e = q
      \<and> (prefix (edge_pop e) s \<or> prefix s (edge_pop e))}
  \<and> epdaH_accessible_states G \<subseteq> {q | q s. cons_tuple2 q s \<in> E}"

theorem F_EPDA_AIA__SOUND: "
  F_EPDA_AIA__SpecInput G k
  \<Longrightarrow> F_EPDA_AIA__SpecOutput G k (F_EPDA_AIA G k)"
  apply(simp add: F_EPDA_AIA__SpecOutput_def F_EPDA_AIA__SpecInput_def)
  apply(rule conjI)
   apply(simp only: F_EPDA_AIA_def)
   apply(rule_tac B="X" for X in subset_trans)
    apply(rule F_EPDA_AIA_preserves_epdaH_accessible_edges)
    apply(force)
   apply(force)
  apply(simp only: F_EPDA_AIA_def)
  apply(rule_tac B="X" for X in subset_trans)
   apply(rule F_EPDA_AIA_preserves_epdaH_accessible_states)
   apply(force)
  apply(force)
  done

lemma F_EPDA_AIA__fp_computed_stack_approximation_initial: "
  F_EPDA_AIA__fp_computed_stack_approximation d 0 k = min k (Suc 0)"
  apply(simp add: F_EPDA_AIA__fp_computed_stack_approximation_def)
  apply(subgoal_tac "nat_seq (Suc 0) 0 = []")
   apply(clarsimp)
  apply (metis append_Cons append_assoc natUptTo_n_Sucn nat_seq_drop_last_prime self_append_conv2)
  done
declare F_EPDA_AIA__fp_computed_stack_approximation_initial [simp add]

lemma F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_outer: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> F_EPDA_AIA__fp G k E = F_EPDA_AIA__fp_one G k (F_EPDA_AIA__fp G k E)"
  apply(rule_tac G="G" and k="k" and N="E" in F_EPDA_AIA__fp_Meta_Lift_Without_Argument)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply (metis F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_inner)
  apply(rename_tac Ga ka N)(*strict*)
  apply (metis F_EPDA_AIA__fp.psimps F_EPDA_AIA__fp_valid_input_implies_termination)
  done

lemma F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_outer_explicit: "
  valid_epda G
  \<Longrightarrow> F_EPDA_AIA__fp_one G k (F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}) = F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}"
  apply(rule sym)
  apply(rule F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_outer)
  apply(rule F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start)
  apply(force)
  done

lemma F_EPDA_AIA__fp_strong_dependency: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d i = Some (pair e1 c1)
  \<Longrightarrow> d (i+j) = Some (pair e2 c2)
  \<Longrightarrow> k > 0
  \<Longrightarrow> \<exists>w.
      length w = Suc j
      \<and> set w \<subseteq> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k}
      \<and> (\<forall>ik<length w.
          \<forall>e c.
          d (i+ik) = Some (pair e c)
          \<longrightarrow> w!ik
            = cons_tuple2
                (epdaH_conf_state c)
                (take (F_EPDA_AIA__fp_computed_stack_approximation d (i+ik) k) (epdaH_conf_stack c)))
      \<and> (\<forall>ik.
          Suc ik<length w
          \<longrightarrow> w ! Suc ik
            \<in> F_EPDA_AIA__fp_one G k {w ! ik})"
  apply(induct j arbitrary: e2 c2)
   apply(rename_tac e2 c2)(*strict*)
   apply(clarsimp)
   apply(case_tac i)
    apply(clarsimp)
    apply(rule_tac x="[F_EPDA_AIA__fp_start G k]" in exI)
    apply(rule conjI)
     apply(force)
    apply(rule conjI)
     apply(simp (no_asm))
     apply(rule_tac A="{F_EPDA_AIA__fp_start G k}" in set_mp)
      prefer 2
      apply(force)
     apply(rule F_EPDA_AIA__fp_mono)
     apply(rule F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start)
     apply(force)
    apply(rule conjI)
     apply(clarsimp)
     apply(simp add: epdaH.derivation_initial_def epdaH_initial_configurations_def F_EPDA_AIA__fp_start_def)
    apply(clarsimp)
   apply(rename_tac nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac i)
   apply(rename_tac i)(*strict*)
   apply(subgoal_tac "F_EPDA_AIA__fp_one_step_contained G k (F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k})")
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule F_EPDA_AIA__fp_enforces_F_EPDA_AIA__fp_one_step_contained)
    apply(rule F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(simp add: F_EPDA_AIA__fp_one_step_contained_def)
   apply(erule_tac x="d" in allE)
   apply(clarsimp)
   apply(erule_tac x="i" in allE)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac i)(*strict*)
    prefer 2
    apply(rule_tac
      d="d" and
      n="i" and
      m="Suc i"
      in epdaH.step_detail_before_some_position)
      apply(rename_tac i)(*strict*)
      apply(rule epdaH.derivation_initial_is_derivation)
      apply(force)
     apply(rename_tac i)(*strict*)
     apply(force)
    apply(rename_tac i)(*strict*)
    apply(force)
   apply(rename_tac i)(*strict*)
   apply(clarsimp)
   apply(rename_tac i e1 e2 c1a)(*strict*)
   apply(rule_tac x="[cons_tuple2 (epdaH_conf_state c1) X]" for X in exI)
   apply(rule conjI)
    apply(rename_tac i e1 e2 c1a)(*strict*)
    apply(force)
   apply(rename_tac i e1 e2 c1a)(*strict*)
   apply(rule conjI)
    apply(rename_tac i e1 e2 c1a)(*strict*)
    apply(force)
   apply(rename_tac i e1 e2 c1a)(*strict*)
   apply(rule conjI)
    apply(rename_tac i e1 e2 c1a)(*strict*)
    apply(clarsimp)
    apply(rule_tac t="min k (F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k)" and s = "F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k" in ssubst)
     apply(rename_tac i e1 e2 c1a)(*strict*)
     apply (metis F_EPDA_AIA__fp_computed_stack_approximation_smaller_than_k min_absorb2)
    apply(rename_tac i e1 e2 c1a)(*strict*)
    apply(force)
   apply(rename_tac i e1 e2 c1a)(*strict*)
   apply(force)
  apply(rename_tac j e2 c2)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac j e2 c2)(*strict*)
   prefer 2
   apply(rule_tac
      d="d" and
      n="i+j" and
      m="i+Suc j"
      in epdaH.step_detail_before_some_position)
     apply(rename_tac j e2 c2)(*strict*)
     apply(rule epdaH.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac j e2 c2)(*strict*)
    apply(force)
   apply(rename_tac j e2 c2)(*strict*)
   apply(force)
  apply(rename_tac j e2 c2)(*strict*)
  apply(clarsimp)
  apply(rename_tac j c2 e1a e2a c1a)(*strict*)
  apply(erule_tac x="e1a" in meta_allE)
  apply(erule_tac x="c1a" in meta_allE)
  apply(erule_tac meta_impE)
   apply(rename_tac j c2 e1a e2a c1a)(*strict*)
   apply(force)
  apply(rename_tac j c2 e1a e2a c1a)(*strict*)
  apply(erule exE)+
  apply(rename_tac j c2 e1a e2a c1a w)(*strict*)
  apply(erule conjE)+
  apply(rule_tac xs="w" in rev_cases)
   apply(rename_tac j c2 e1a e2a c1a w)(*strict*)
   apply(force)
  apply(rename_tac j c2 e1a e2a c1a w ys y)(*strict*)
  apply(clarsimp)
  apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
  apply(subgoal_tac "cons_tuple2 (epdaH_conf_state c2)
                      (take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i + length ys)) k)
                        (epdaH_conf_stack c2)) \<in> F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k} \<and> cons_tuple2 (epdaH_conf_state c2)
                      (take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i + length ys)) k)
                        (epdaH_conf_stack c2)) \<in> F_EPDA_AIA__fp_one G k {y}")
   apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
   apply(rule_tac x="ys@[y,cons_tuple2 (epdaH_conf_state c2)
                      (take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i + length ys)) k)
                        (epdaH_conf_stack c2))]" in exI)
   apply(rule conjI)
    apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
    apply(force)
   apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
   apply(rule conjI)
    apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
    apply(clarsimp)
   apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
   apply(clarsimp)
   apply(rule conjI)
    apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
    apply(clarsimp)
    apply(rename_tac c2 e1a e2a c1a ys y ik e c)(*strict*)
    apply(case_tac "ik = (Suc (length ys))")
     apply(rename_tac c2 e1a e2a c1a ys y ik e c)(*strict*)
     apply(clarsimp)
     apply(rename_tac e1a e2a c1a ys y c)(*strict*)
     apply (metis (no_types, hide_lams) append_Cons append_Nil append_assoc length_Suc nth_append_length)
    apply(rename_tac c2 e1a e2a c1a ys y ik e c)(*strict*)
    apply(erule_tac x="ik" in allE)+
    apply(clarsimp)
    apply(case_tac "ik = ((length ys))")
     apply(rename_tac c2 e1a e2a c1a ys y ik e c)(*strict*)
     apply(clarsimp)
    apply(rename_tac c2 e1a e2a c1a ys y ik e c)(*strict*)
    apply(clarsimp)
    apply (metis less_Suc_eq nth_append)
   apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac c2 e1a e2a c1a ys y ik)(*strict*)
   apply(case_tac "ik=length ys")
    apply(rename_tac c2 e1a e2a c1a ys y ik)(*strict*)
    apply(clarsimp)
    apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
    apply(rule_tac t="(ys @
        [y, cons_tuple2 (epdaH_conf_state c2)
             (take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i + length ys)) k)
               (epdaH_conf_stack c2))]) !
       Suc (length ys)" and s="cons_tuple2 (epdaH_conf_state c2)
             (take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i + length ys)) k)
               (epdaH_conf_stack c2))" in ssubst)
     apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
     apply (metis append_Cons append_Nil append_assoc length_Suc nth_append_length)
    apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
    apply(case_tac e2a)
    apply(rename_tac c2 e1a e2a c1a ys y edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
    apply(rename_tac q r po pu q')
    apply(rename_tac c2 e1a e2a c1a ys y q r po pu q')(*strict*)
    apply(thin_tac "\<forall>ik<length ys.
          (ys @ [y]) ! Suc ik
          \<in> F_EPDA_AIA__fp_one G k {(ys @ [y]) ! ik}")
    apply(erule_tac x="length ys" in allE)
    apply(clarsimp)
   apply(rename_tac c2 e1a e2a c1a ys y ik)(*strict*)
   apply(thin_tac "\<forall>ik<Suc (length ys).
          \<forall>e c. d (i + ik) = Some (pair e c) \<longrightarrow>
                (ys @ [y]) ! ik =
                cons_tuple2 (epdaH_conf_state c)
                 (take (F_EPDA_AIA__fp_computed_stack_approximation d (i + ik) k)
                   (epdaH_conf_stack c))")
   apply(erule_tac x="ik" in allE)
   apply(clarsimp)
   apply(rule_tac t="(ys @
        [y, cons_tuple2 (epdaH_conf_state c2)
             (take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i + length ys)) k)
               (epdaH_conf_stack c2))]) !
       Suc ik" and s=" (ys @ [y]) ! Suc ik" in ssubst)
    apply(rename_tac c2 e1a e2a c1a ys y ik)(*strict*)
    apply (metis (mono_tags, hide_lams) Suc_less_eq less_Suc_eq monoid_add_class.add.right_neutral nth_Cons_0 nth_append nth_append_length_plus)
   apply(rename_tac c2 e1a e2a c1a ys y ik)(*strict*)
   apply(rule_tac t="(ys @
             [y, cons_tuple2 (epdaH_conf_state c2)
                  (take (F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i + length ys)) k)
                    (epdaH_conf_stack c2))]) !
            ik" and s=" (ys @ [y]) ! ik" in ssubst)
    apply(rename_tac c2 e1a e2a c1a ys y ik)(*strict*)
    apply (metis Suc_less_eq less_Suc_eq nth_append nth_append_length)
   apply(rename_tac c2 e1a e2a c1a ys y ik)(*strict*)
   apply(force)
  apply(rename_tac c2 e1a e2a c1a ys y)(*strict*)
  apply(thin_tac "\<forall>ik<length ys.
          (ys @ [y]) ! Suc ik
          \<in> F_EPDA_AIA__fp_one G k {(ys @ [y]) ! ik}")
  apply(erule_tac x="length ys" in allE)
  apply(clarsimp)
  apply(rename_tac c2 e1a e2a c1a ys)(*strict*)
  apply(case_tac e2a)
  apply(rename_tac c2 e1a e2a c1a ys edge_src edge_event edge_pop edge_push edge_trg)(*strict*)
  apply(rename_tac q r po pu q')
  apply(rename_tac c2 e1a e2a c1a ys q r po pu q')(*strict*)
  apply(case_tac c1a)
  apply(rename_tac c2 e1a e2a c1a ys q r po pu q' epdaH_conf_statea epdaH_conf_history epdaH_conf_stacka)(*strict*)
  apply(rename_tac q1 h1 s1)
  apply(rename_tac c2 e1a e2a c1a ys q r po pu q' q1 h1 s1)(*strict*)
  apply(case_tac c2)
  apply(rename_tac c2 e1a e2a c1a ys q r po pu q' q1 h1 s1 epdaH_conf_statea epdaH_conf_history epdaH_conf_stacka)(*strict*)
  apply(rename_tac q2 h2 s2)
  apply(rename_tac c2 e1a e2a c1a ys q r po pu q' q1 h1 s1 q2 h2 s2)(*strict*)
  apply(clarsimp)
  apply(rename_tac e1a ys q r po pu q' q1 h1 s1 q2 h2 s2)(*strict*)
  apply(rule F_EPDA_AIA__fp_one_intro3)
      apply(rename_tac e1a ys q r po pu q' q1 h1 s1 q2 h2 s2)(*strict*)
      apply(force)
     apply(rename_tac e1a ys q r po pu q' q1 h1 s1 q2 h2 s2)(*strict*)
     apply(rule F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_outer_explicit)
     apply(force)
    apply(rename_tac e1a ys q r po pu q' q1 h1 s1 q2 h2 s2)(*strict*)
    apply(simp add: epdaH_step_relation_def)
    apply(force)
   apply(rename_tac e1a ys q r po pu q' q1 h1 s1 q2 h2 s2)(*strict*)
   prefer 2
   apply(simp add: epdaH_step_relation_def)
   apply(clarsimp)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   apply(case_tac "(F_EPDA_AIA__fp_computed_stack_approximation d (i + length ys) k - length po)")
    apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
    apply(thin_tac "\<not> po \<sqsubseteq>
          take (F_EPDA_AIA__fp_computed_stack_approximation d (i + length ys) k) po @
          take (F_EPDA_AIA__fp_computed_stack_approximation d (i + length ys) k - length po) w")
    apply(simp add: prefix_def)
    apply(rule_tac x="drop (F_EPDA_AIA__fp_computed_stack_approximation d (i + length ys) k) po" in exI)
    apply(rule append_take_drop_id)
   apply(rename_tac e1a ys q r po pu q' h1 w nat)(*strict*)
   apply(subgoal_tac "po \<sqsubseteq>
          take (F_EPDA_AIA__fp_computed_stack_approximation d (i + length ys) k) po @
          take (F_EPDA_AIA__fp_computed_stack_approximation d (i + length ys) k - length po) w")
    apply(rename_tac e1a ys q r po pu q' h1 w nat)(*strict*)
    apply(force)
   apply(rename_tac e1a ys q r po pu q' h1 w nat)(*strict*)
   apply(thin_tac "\<not> po \<sqsubseteq>
          take (F_EPDA_AIA__fp_computed_stack_approximation d (i + length ys) k) po @
          take (F_EPDA_AIA__fp_computed_stack_approximation d (i + length ys) k - length po) w")
   apply(clarsimp)
   apply(simp add: prefix_def)
  apply(rename_tac e1a ys q r po pu q' q1 h1 s1 q2 h2 s2)(*strict*)
  apply(simp add: epdaH_step_relation_def)
  apply(clarsimp)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(rule_tac t="F_EPDA_AIA__fp_computed_stack_approximation d (Suc (i + length ys)) k" and s="
  min k (F_EPDA_AIA__fp_computed_stack_approximation d ((i + length ys)) k - length po + length pu)" in ssubst)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   apply(rule F_EPDA_AIA__fp_computed_stack_approximation_unfold)
     apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
     apply(force)
    apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
    apply(force)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   apply(force)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   prefer 2
   apply(rule_tac a="length pu" and b="k" in min_alt)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(erule disjE)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   prefer 2
   apply(clarsimp)
   apply(rule_tac t="(min k
          (F_EPDA_AIA__fp_computed_stack_approximation d (i+length ys) k - length po + length pu))" and s="k" in ssubst)
    apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
    apply(force)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   apply(clarsimp)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   prefer 2
   apply(rule_tac a="length po" and b="F_EPDA_AIA__fp_computed_stack_approximation d (i+length ys) k" in min_alt)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(erule disjE)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   prefer 2
   apply(rule_tac b="(F_EPDA_AIA__fp_computed_stack_approximation d (i+length ys) k + length pu - length po)" and a="k" in min_alt)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(erule disjE)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
    prefer 2
    apply(rule_tac a="k - length pu" and  b="(F_EPDA_AIA__fp_computed_stack_approximation d (i+length ys) k - length po)" in min_alt)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   apply(erule disjE)
    apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
    apply(clarsimp)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   apply(clarsimp)
   apply(rule_tac t="F_EPDA_AIA__fp_computed_stack_approximation d (i+length ys) k - length po" and s="k-length pu" in ssubst)
    apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
    apply(rule antisym)
     apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
     apply(force)
    apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
    apply(rule to_mutual_sub1)
    apply(force)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   apply(force)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   prefer 2
   apply(rule_tac a="k - length pu" and  b="(F_EPDA_AIA__fp_computed_stack_approximation d (i+length ys) k - length po)" in min_alt)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(erule disjE)
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   prefer 2
   apply(clarsimp)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "F_EPDA_AIA__fp_computed_stack_approximation d (i+length ys) k - length po \<le> k - length pu")
   apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
   prefer 2
   apply(rule to_mutual_sub2)
   apply(force)
  apply(rename_tac e1a ys q r po pu q' h1 w)(*strict*)
  apply(force)
  done

lemma F_EPDA_AIA__fp_one_intro1: "
  x \<in> E
  \<Longrightarrow> x \<in> F_EPDA_AIA__fp_one G k E"
  apply(simp add: F_EPDA_AIA__fp_one_def)
  done

lemma F_EPDA_AIA__fp_some_tuple_reachable_hlp3: "
  take (min (k - length pu1) (k - (length pu2 + length ca))) cc = take (k - length pu1) (drop (length pu2 + length ca - (min (length pu2) k + min (length ca) (k - length pu2))) (take (k - (length pu2 + length ca)) cc))"
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac a="(k - length pu1)" and b="(k - (length pu2 + length ca))" in min_alt)
  apply(erule disjE)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac a="length pu2" and b="k" in min_alt)
   apply(erule disjE)
    apply(clarsimp)
    apply(subgoal_tac "X" for X)
     prefer 2
     apply(rule_tac a="length ca" and b="k-length pu2" in min_alt)
    apply(erule disjE)
     apply(clarsimp)
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   prefer 2
   apply(rule_tac a="length ca" and b="k-length pu2" in min_alt)
  apply(erule disjE)
   apply(clarsimp)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac a="length pu2" and b="k" in min_alt)
   apply(erule disjE)
    apply(clarsimp)
   apply(clarsimp)
  apply(clarsimp)
  done

lemma F_EPDA_AIA__fp_one_in_F_EPDA_AIA__fp: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> F_EPDA_AIA__fp_one G k E \<subseteq> F_EPDA_AIA__fp G k E"
  apply(rule_tac F_EPDA_AIA__fp_Meta_Lift_Without_Argument_With_Argument)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(rule_tac B="F_EPDA_AIA__fp_one Ga ka (F_EPDA_AIA__fp_one Ga ka N)" in subset_trans)
    apply(rename_tac Ga ka N)(*strict*)
    apply(rule F_EPDA_AIA__fp_one_mono)
   apply(rename_tac Ga ka N)(*strict*)
   apply(force)
  apply(rename_tac Ga ka N)(*strict*)
  apply(rule_tac ?xb.0="N" in F_EPDA_AIA__fp.pelims)
    apply(rename_tac Ga ka N)(*strict*)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(rule_tac G="Ga" and k="ka" in F_EPDA_AIA__fp_valid_input_implies_termination)
   apply(force)
  apply(rename_tac Ga ka N Gaa kaa Ea)(*strict*)
  apply(clarsimp)
  done

lemma F_EPDA_AIA__fp_computed_stack_approximation_not_zero_after_push: "
  valid_epda G
  \<Longrightarrow> epdaH.derivation_initial G d
  \<Longrightarrow> d (Suc i) = Some (pair (Some e) c)
  \<Longrightarrow> edge_event e = None
  \<Longrightarrow> edge_push e = [A, X]
  \<Longrightarrow> edge_pop e = [X]
  \<Longrightarrow> k > 0
  \<Longrightarrow> F_EPDA_AIA__fp_computed_stack_approximation d (Suc i) k > 0"
  apply(simp add: F_EPDA_AIA__fp_computed_stack_approximation_def)
  apply(subgoal_tac "nat_seq (Suc 0) (Suc i) = nat_seq (Suc 0) i @[Suc i]")
   prefer 2
   apply (metis diff_Suc_Suc minus_nat.diff_0 nat_seq_last zero_less_Suc)
  apply(clarsimp)
  apply(simp add: get_label_def)
  done

theorem F_EPDA_AIA__fp_preserves_F_EPDA_AIA__fp_valid_input: "
  F_EPDA_AIA__fp_valid_input G k E
  \<Longrightarrow> F_EPDA_AIA__fp_valid_input G k (F_EPDA_AIA__fp G k E)"
  apply(rule F_EPDA_AIA__fp_Meta_Lift_Without_Argument)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(rule_tac t="(F_EPDA_AIA__fp Ga ka N)"  and s="(F_EPDA_AIA__fp Ga ka (F_EPDA_AIA__fp_one Ga ka N))" in ssubst)
    apply(rename_tac Ga ka N)(*strict*)
    apply(rule F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_inner)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(force)
  apply(rename_tac Ga ka N)(*strict*)
  apply(rule_tac ?x.0="Ga" and ?xa.0="ka" and ?xb.0="N" in F_EPDA_AIA__fp.pelims)
    apply(rename_tac Ga ka N)(*strict*)
    apply(force)
   apply(rename_tac Ga ka N)(*strict*)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_termination)
   apply(force)
  apply(rename_tac Ga ka N Gaa kaa Ea)(*strict*)
  apply(clarsimp)
  done

lemma F_EPDA_AIA__fp_enforces_F_EPDA_AIA__fp_all_have_parent_element: "
  valid_epda G
  \<Longrightarrow> F_EPDA_AIA__fp_all_have_parent_element G k (F_EPDA_AIA__fp G k {F_EPDA_AIA__fp_start G k})"
  apply(rule F_EPDA_AIA__fp_Meta_Lift_Without_Argument)
    apply (metis F_EPDA_AIA__fp_valid_input_with_F_EPDA_AIA__fp_start)
   apply(rename_tac Ga k N)(*strict*)
   apply (metis F_EPDA_AIA__fp_F_EPDA_AIA__fp_one_idempotent_inner)
  apply(rename_tac Ga k N)(*strict*)
  apply(rule_tac ?x.0="Ga" and ?xa.0="k" and ?xb.0="N" in F_EPDA_AIA__fp.pelims)
    apply(rename_tac Ga k N)(*strict*)
    apply(force)
   apply(rename_tac Ga k N)(*strict*)
   apply(rule F_EPDA_AIA__fp_valid_input_implies_termination)
   apply(force)
  apply(rename_tac Ga k N Gaa ka E)(*strict*)
  apply(simp add: F_EPDA_AIA__fp_valid_input_def)
  done

end
