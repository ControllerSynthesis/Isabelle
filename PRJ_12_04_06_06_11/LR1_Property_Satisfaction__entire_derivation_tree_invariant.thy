section {*LR1\_Property\_Satisfaction\_\_entire\_derivation\_tree\_invariant*}
theory
  LR1_Property_Satisfaction__entire_derivation_tree_invariant

imports
  PRJ_12_04_06_06_11__ENTRY

begin

definition EValidSplitExt_no_elim_before_nonterminal :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplitExt_no_elim_before_nonterminal S \<equiv>
  \<forall>k < length S. 
    (\<exists>A. ESplitItem_elem (S ! k) = Some (teA A))
    \<longrightarrow> (\<forall>i \<le> k. ESplitItem_elim (S ! i) = [])"

definition EValidSplitExt_no_pop_in_prods_before_nonterminal :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplitExt_no_pop_in_prods_before_nonterminal S \<equiv>
  \<forall>k < length S. 
    (\<exists>A. ESplitItem_elem (S ! k) = Some (teA A)) 
    \<longrightarrow> (\<forall>i \<le> k. \<forall>j < length (ESplitItem_prods (S ! i)) . prod_rhs (ESplitItem_prods (S ! i) ! j) \<noteq> [])"

definition Eident_line :: "
  ('q, 's, 't) ESplitItem
  \<Rightarrow> bool"
  where
    "Eident_line S \<equiv>
   (ESplitItem_prods S = []
  \<and> ESplitItem_elim S = [])"

definition Eident_lines :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> nat set"
  where
    "Eident_lines S \<equiv>
  {n. n < length S
  \<and> Eident_line (S ! n) }"

definition EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal S \<equiv>
   (\<forall>k < length S. (\<exists>A. ESplitItem_elem (S ! k) = Some (teA A)) \<longrightarrow> (\<forall>i < k. i \<notin> Eident_lines S))"

definition EValidSplitExt :: "
  ('q, 's, 't) ESplit
  \<Rightarrow> bool"
  where
    "EValidSplitExt S \<equiv>
   (EValidSplitExt_no_elim_before_nonterminal S
  \<and> EValidSplitExt_no_pop_in_prods_before_nonterminal S
  \<and> EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal S)"

lemma entirely_ignored_can_not_happend_to_early: "
  F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> EValidSplit G (S@SX#SY#SZ#S')
  \<Longrightarrow> EValidSplitExt (S@SX#SY#SZ#S')
  \<Longrightarrow> ESplitItem_elim SY = []
  \<Longrightarrow> ESplitItem_prods SY = []
  \<Longrightarrow> ESplitItem_to SX = X#to
  \<Longrightarrow> ESplitItem_ignore SX = ig
  \<Longrightarrow> ESplitItem_ignore SZ = c @ to @ ig
  \<Longrightarrow> Q"
  apply(simp add: EValidSplit_def)
  apply(clarsimp)
  apply(simp add: EValidSplit_interline_def)
  apply(erule_tac x="length S" in allE')
  apply(erule_tac
      x="Suc(length S)"
      in allE)
  apply(clarsimp)
  apply(subgoal_tac "(S @ SX # SY # SZ # S') ! (length S) = SX")
   prefer 2
   apply(force)
  apply(subgoal_tac "(S @ SX # SY # SZ # S') ! Suc (length S) = SY")
   prefer 2
   apply (metis drop_append2 drop_nth_hlp1)
  apply(subgoal_tac "(S @ SX # SY # SZ # S') ! Suc (Suc(length S)) = SSX" for SSX)
   prefer 2
   apply(rule nth_append_2)
   apply(force)
  apply(clarsimp)
  apply(simp add: EValidSplit_interlineX_def)
  apply(case_tac "ESplitItem_from SY")
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="SY"
      in ballE_prime)
    apply(clarsimp)
   apply(simp add: option_to_list_def)
   apply(subgoal_tac "SY \<in> set (butlast (S @ SX # SY # SZ # S'))")
    apply(force)
   apply(thin_tac "SY \<notin> set (butlast (S @ SX # SY # SZ # S'))")
   apply(rule_tac
      xs="S'"
      in rev_cases)
    apply(clarsimp)
    apply(rule_tac
      t="butlast (S @ [SX, SY, SZ])"
      in ssubst)
     apply(rule butlast_direct)
     apply(force)
    apply(force)
   apply(rename_tac ys y)(*strict*)
   apply(clarsimp)
   apply(rule_tac
      t="butlast (S @ SX # SY # SZ # ys @ [y])"
      in ssubst)
    apply(rename_tac ys y)(*strict*)
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac ys y)(*strict*)
   apply(force)
  apply(rename_tac a)(*strict*)
  apply(case_tac "ESplitItem_from SX")
   apply(rename_tac a)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="SX"
      in ballE_prime)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
   apply(rename_tac a)(*strict*)
   apply(subgoal_tac "SX \<in> set (butlast (S @ SX # SY # SZ # S'))")
    apply(rename_tac a)(*strict*)
    apply(force)
   apply(rename_tac a)(*strict*)
   apply(rule_tac
      xs="S'"
      in rev_cases)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast (S @ [SX, SY, SZ]) = SSX" for SSX)
     apply(rename_tac a)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac a)(*strict*)
    apply(clarsimp)
   apply(rename_tac a ys y)(*strict*)
   apply(clarsimp)
   apply(subgoal_tac "butlast (S @ SX # SY # SZ # ys @ [y]) = SSX" for SSX)
    apply(rename_tac a ys y)(*strict*)
    prefer 2
    apply(rule butlast_direct)
    apply(force)
   apply(rename_tac a ys y)(*strict*)
   apply(clarsimp)
  apply(rename_tac a aa)(*strict*)
  apply(clarsimp)
  apply(simp add: option_to_list_def)
  apply(case_tac "ESplitItem_to SX")
   apply(rename_tac a aa)(*strict*)
   apply(clarsimp)
  apply(rename_tac a aa ab list)(*strict*)
  apply(clarsimp)
  apply(rename_tac aa)(*strict*)
  apply(subgoal_tac "ESplitItem_to SY = []")
   apply(rename_tac aa)(*strict*)
   prefer 2
   apply(simp add: EValidSplit_ValidItem_def)
   apply(clarsimp)
   apply(simp add: EValidSplitItem_def EValidSplitItem_gen_def)
   apply(clarsimp)
   apply(rename_tac aa d da db)(*strict*)
   apply(simp add: cfgLM.trans_der_def option_to_list_def)
   apply(clarsimp)
   apply(rename_tac aa d da db e eb)(*strict*)
   apply(simp add: EValidSplit_producing_def)
   apply(erule_tac
      x="SY"
      and A="set (butlast (S @ SX # SY # SZ # S'))"
      in ballE)
    apply(rename_tac aa d da db e eb)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_to SY")
     apply(rename_tac aa d da db e eb)(*strict*)
     apply(force)
    apply(rename_tac aa d da db e eb a list)(*strict*)
    apply(force)
   apply(rename_tac aa d da db e eb)(*strict*)
   apply(subgoal_tac "SY \<in> set (butlast (S @ SX # SY # SZ # S'))")
    apply(rename_tac aa d da db e eb)(*strict*)
    apply(force)
   apply(rename_tac aa d da db e eb)(*strict*)
   apply(rule_tac
      xs="S'"
      in rev_cases)
    apply(rename_tac aa d da db e eb)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "butlast (S @ [SX, SY, SZ]) = SSX" for SSX)
     apply(rename_tac aa d da db e eb)(*strict*)
     prefer 2
     apply(rule butlast_direct)
     apply(force)
    apply(rename_tac aa d da db e eb)(*strict*)
    apply(clarsimp)
   apply(rename_tac aa d da db e eb ys y)(*strict*)
   apply(clarsimp)
   apply(rename_tac aa d da db e eb ys y dc ea)(*strict*)
   apply(subgoal_tac "butlast ((S @ SX # SY # SZ # ys) @ [y]) = SSX" for SSX)
    apply(rename_tac aa d da db e eb ys y dc ea)(*strict*)
    prefer 2
    apply(rule_tac
      w="S @ SX # SY # SZ # ys"
      in butlast_direct)
    apply(force)
   apply(rename_tac aa d da db e eb ys y dc ea)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa)(*strict*)
  apply(clarsimp)
  apply(case_tac "ESplitItem_from SZ")
   apply(rename_tac aa)(*strict*)
   prefer 2
   apply(rename_tac aa a)(*strict*)
   apply(clarsimp)
  apply(rename_tac aa)(*strict*)
  apply(clarsimp)
  apply(simp add: EValidSplit_produce_or_elim_def)
  done

lemma restrict_equal_before_step_nonterminal: "
       F2LR1inputx G' G
  \<Longrightarrow> split_TSstructure G'
  \<Longrightarrow> Esplit_signature S2 = w @ teB b # liftB \<alpha>1 @ teA A2 # liftB \<alpha>2
  \<Longrightarrow> EValidSplit G' S2
  \<Longrightarrow> EValidSplit G' (S2a @ S2b)
  \<Longrightarrow> Esplit_step_relation G' S2 \<lparr>prod_lhs = A2, prod_rhs = []\<rparr> (S2a @ S2b)
  \<Longrightarrow> Esplit_signature S2a = w @ [teB b]
  \<Longrightarrow> length S2a = Suc (length w)
  \<Longrightarrow> Esplit_signature S2b = liftB \<alpha>1 @ liftB \<alpha>2
  \<Longrightarrow> EValidSplitExt S2
  \<Longrightarrow> EValidSplitExt (S2a @ S2b)
  \<Longrightarrow> restrict G G' S2 (Suc(length w)) = restrict G G' (S2a @ S2b) (Suc (length w))"
  apply(simp (no_asm) add: restrict_def restrict_map_def restrict_len_def)
  apply(clarsimp)
  apply(rule_tac
      t="min (length S2) (Suc (length w))"
      and s="Suc (length w)"
      in ssubst)
   apply(subgoal_tac "X" for X)
    prefer 2
    apply(rule_tac
      S="S2"
      and S'="[]"
      in EValidSplit_Esplit_signature_length)
    apply(force)
   apply(clarsimp)
   apply(force)
  apply(clarsimp)
  apply(rename_tac x)(*strict*)
  apply(subgoal_tac "0\<le> x \<and> x \<le> SSX" for SSX)
   apply(rename_tac x)(*strict*)
   prefer 2
   apply(rule nat_seq_in_interval)
   apply(force)
  apply(rename_tac x)(*strict*)
  apply(clarsimp)
  apply(simp add: Esplit_step_relation_def)
  apply(clarsimp)
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(simp add: Xstep_gen_def)
  apply (simp add: Esplit_signature_append)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x S1 SL S2)(*strict*)
   prefer 2
   apply(rule_tac
      S="S1"
      and S'="SL#S2"
      in EValidSplit_Esplit_signature_length)
   apply(force)
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac x S1 SL S2)(*strict*)
   prefer 2
   apply (rule_tac
      w="SL"
      and v="S2"
      in Esplit_signature_Cons)
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(subgoal_tac "Esplit_signature S1 @ Esplit_signature [SL] @ Esplit_signature S2 = w @ teB b # liftB \<alpha>1 @ teA A2 # liftB \<alpha>2")
   apply(rename_tac x S1 SL S2)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(thin_tac "Esplit_signature S1 @ Esplit_signature (SL # S2) = w @ teB b # liftB \<alpha>1 @ teA A2 # liftB \<alpha>2")
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(thin_tac "Esplit_signature (SL # S2) = Esplit_signature [SL] @ Esplit_signature S2")
  apply(subgoal_tac "Esplit_signature [SL] = [teA A2]")
   apply(rename_tac x S1 SL S2)(*strict*)
   prefer 2
   apply(simp add: Esplit_signature_def option_to_list_def)
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "Esplit_signature S2 = liftB \<alpha>2")
   apply(rename_tac x S1 SL S2)(*strict*)
   prefer 2
   apply(rule_tac
      ?w1.0="Esplit_signature S1"
      and A="A2"
      in equal_terminal_suffix)
     apply(rename_tac x S1 SL S2)(*strict*)
     apply(force)
    apply(rename_tac x S1 SL S2)(*strict*)
    apply(force)
   apply(rename_tac x S1 SL S2)(*strict*)
   apply(rule setA_liftB)
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "strict_prefix S1 S2a \<or> SSX" for SSX)
   apply(rename_tac x S1 SL S2)(*strict*)
   prefer 2
   apply(rule mutual_strict_prefix_prefix)
   apply(rule sym)
   apply(force)
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(erule disjE)
   apply(rename_tac x S1 SL S2)(*strict*)
   apply(simp add: strict_prefix_def)
   apply(clarsimp)
  apply(rename_tac x S1 SL S2)(*strict*)
  apply(simp add: prefix_def)
  apply(clarsimp)
  apply(rename_tac x SL S2 c)(*strict*)
  apply (simp add: Esplit_signature_append)
  apply(subgoal_tac "(S2a @ c @ SL # S2) ! x = SSX" for SSX)
   apply(rename_tac x SL S2 c)(*strict*)
   prefer 2
   apply(rule nth_append_1)
   apply(force)
  apply(rename_tac x SL S2 c)(*strict*)
  apply(clarsimp)
  done

theorem Esplit_derivation_enforces_EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal: "
  Esplit_TSstructure G
  \<Longrightarrow> F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> Esplit.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e S)
  \<Longrightarrow> k<length S
  \<Longrightarrow> ESplitItem_elem (S!k) = Some (teA A)
  \<Longrightarrow> i<k
  \<Longrightarrow> i \<notin> (Eident_lines S)"
  apply(induct n arbitrary: e S k A i)
   apply(rename_tac e S k A i)(*strict*)
   apply(simp add: Esplit.derivation_initial_def)
   apply(clarsimp)
   apply(rename_tac S k A i)(*strict*)
   apply(simp add: Esplit_initial_configurations_def)
  apply(rename_tac n e S k A i)(*strict*)
  apply(clarsimp)
  apply(subgoal_tac "X" for X)
   apply(rename_tac n e S k A i)(*strict*)
   prefer 2
   apply(rule_tac
      G="G"
      and d="d"
      and n="n"
      and m="Suc n"
      in Esplit.step_detail_before_some_position)
     apply(rename_tac n e S k A i)(*strict*)
     apply(rule Esplit.derivation_initial_is_derivation)
     apply(force)
    apply(rename_tac n e S k A i)(*strict*)
    apply(force)
   apply(rename_tac n e S k A i)(*strict*)
   apply(force)
  apply(rename_tac n e S k A i)(*strict*)
  apply(clarsimp)
  apply(rename_tac n S k A i e1 e2 c1)(*strict*)
  apply(simp add: Esplit_step_relation_def)
  apply(clarsimp)
  apply(rename_tac n k A i e1 e2 S1 SL S2)(*strict*)
  apply(erule_tac
      x="e1"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="S1 @ SL # S2"
      in meta_allE)
  apply(clarsimp)
  apply(erule_tac
      x="length S1"
      in meta_allE)
  apply(clarsimp)
  apply(case_tac e2)
  apply(rename_tac n k A i e1 e2 S1 SL S2 prod_lhsa prod_rhsa)(*strict*)
  apply(rename_tac A w)
  apply(rename_tac n k Aa i e1 e2 S1 SL S2 A w)(*strict*)
  apply(erule_tac
      x="A"
      in meta_allE)
  apply(clarsimp)
  apply(rename_tac n k Aa i e1 S1 SL S2 A w)(*strict*)
  apply(thin_tac "Esplit.derivation_initial G d")
  apply(thin_tac "d (Suc n) = Some (pair (Some \<lparr>prod_lhs = A, prod_rhs = w\<rparr>) (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2))")
  apply(rename_tac n k Aa i e1 S1 SL S2 A w)(*strict*)
  apply(thin_tac "d n = Some (pair e1 (S1 @ SL # S2))")
  apply(case_tac "i<length S1")
   apply(rename_tac n k Aa i e1 S1 SL S2 A w)(*strict*)
   apply(erule_tac
      x="i"
      in meta_allE)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
   apply(simp add: Eident_lines_def Eident_line_def)
   apply(clarsimp)
   apply(subgoal_tac "(S1 @ SL # S2) ! i = (S1 @ Xstep_mergeL (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) (nth_opt S2 0) @ drop (Suc 0) S2) ! i")
    apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
    apply(clarsimp)
   apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
   apply(rule nth_eq_ignore_append)
     apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
     prefer 3
     apply(force)
    apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
   apply(force)
  apply(rename_tac n k Aa i e1 S1 SL S2 A w)(*strict*)
  apply(subgoal_tac "length S1\<le>i")
   apply(rename_tac n k Aa i e1 S1 SL S2 A w)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac n k Aa i e1 S1 SL S2 A w)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
  apply(subgoal_tac "length(Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)) = SSX" for SSX)
   apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
   prefer 2
   apply(rule Xstep_gen_length)
    apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
    apply(simp add: split_TSstructure_def)
    apply(force)
   apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
   apply(force)
  apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
  apply(case_tac S2)
   apply(rename_tac k Aa i S1 SL S2 A w)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A w)(*strict*)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_mergeL_def)
   apply(case_tac "Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL)")
    apply(rename_tac k Aa i S1 SL A w)(*strict*)
    apply(subgoal_tac "k < length S1 + (length (if True then [] else Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) + length (case ESplitItem_elem (if True then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))]))")
     apply(rename_tac k Aa i S1 SL A w)(*strict*)
     prefer 2
     apply(rule_tac
      t="True"
      and s="Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = []"
      in ssubst)
      apply(rename_tac k Aa i S1 SL A w)(*strict*)
      apply(force)
     apply(rename_tac k Aa i S1 SL A w)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A w)(*strict*)
    apply(thin_tac "k < length S1 + (length (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then [] else Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # butlast (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) + length (case ESplitItem_elem (if Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL) = [] then Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> else last (Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) of None \<Rightarrow> [Xstep_merge1 (last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))) EmptyESplitItem] | Some e \<Rightarrow> [last (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr> # Xstep_gen (filterA (tl w)) (ESplitItem_to SL @ ESplitItem_ignore SL))]))")
    apply(rename_tac k Aa i S1 SL A w)(*strict*)
    apply(clarsimp)
    apply(case_tac "ESplitItem_elem (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = w\<rparr>)")
     apply(rename_tac k Aa i S1 SL A w)(*strict*)
     apply(clarsimp)
    apply(rename_tac k Aa i S1 SL A w a)(*strict*)
    apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A w a list)(*strict*)
   apply(case_tac w)
    apply(rename_tac k Aa i S1 SL A w a list)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(subgoal_tac "a#list=[]")
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(rule_tac
      t="a#list"
      and s="Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in ssubst)
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(rule_tac
      t="[]"
      and s="Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL)"
      in subst)
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     apply(thin_tac "Xstep_gen [] (ESplitItem_to SL @ ESplitItem_ignore SL) = a # list")
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A w a list aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A a list aa lista)(*strict*)
   apply(case_tac lista)
    apply(rename_tac k Aa i S1 SL A a list aa lista)(*strict*)
    apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A a list aa lista ab listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
   apply(subgoal_tac "listb=[]")
    apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
    prefer 2
    apply(rule LR1_at_most_two_symbols)
     apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A a aa ab)(*strict*)
   apply(case_tac ab)
    apply(rename_tac k Aa i S1 SL A a aa ab ac)(*strict*)
    prefer 2
    apply(rename_tac k Aa i S1 SL A a aa ab b)(*strict*)
    apply(clarsimp)
    apply(rename_tac k Aa i S1 SL A a aa b)(*strict*)
    apply(simp add: Xstep_gen_def)
   apply(rename_tac k Aa i S1 SL A a aa ab ac)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A a aa ac)(*strict*)
   apply(simp add: Xstep_gen_def)
   apply(subgoal_tac "nat_seq 0 0 = [0]")
    apply(rename_tac k Aa i S1 SL A a aa ac)(*strict*)
    prefer 2
    apply (metis natUptTo_n_n)
   apply(rename_tac k Aa i S1 SL A a aa ac)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A aa ac)(*strict*)
   apply(simp add: Xstep_elem_def)
   apply(simp add: Xstep_gen_def)
   apply(simp add: nth_opt_def)
   apply(case_tac "Suc k = Suc (Suc (length S1))")
    apply(rename_tac k Aa i S1 SL A aa ac)(*strict*)
    apply(clarsimp)
    apply(rename_tac Aa i S1 SL A aa ac)(*strict*)
    apply(subgoal_tac "(S1 @ [SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa, teA ac]\<rparr>], ESplitItem_elem := Some aa, ESplitItem_to := ac # ESplitItem_to SL\<rparr>, \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ac, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ac), ESplitItem_to = []\<rparr>]) ! Suc (length S1) = [\<lparr>ESplitItem_elim = [], ESplitItem_from = Some ac, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ac), ESplitItem_to = []\<rparr>]!SSX" for SSX)
     apply(rename_tac Aa i S1 SL A aa ac)(*strict*)
     prefer 2
     apply(rule nth_append_2_prime)
       apply(rename_tac Aa i S1 SL A aa ac)(*strict*)
       apply(force)
      apply(rename_tac Aa i S1 SL A aa ac)(*strict*)
      apply(force)
     apply(rename_tac Aa i S1 SL A aa ac)(*strict*)
     apply(force)
    apply(rename_tac Aa i S1 SL A aa ac)(*strict*)
    apply(clarsimp)
    apply(rename_tac Aa i S1 SL A aa)(*strict*)
    apply(case_tac "i=length S1")
     apply(rename_tac Aa i S1 SL A aa)(*strict*)
     apply(clarsimp)
     apply(rename_tac Aa S1 SL A aa)(*strict*)
     apply(simp add: Eident_lines_def Eident_line_def)
    apply(rename_tac Aa i S1 SL A aa)(*strict*)
    apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A aa ac)(*strict*)
   apply(clarsimp)
  apply(rename_tac k Aa i S1 SL S2 A w a list)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i S1 SL A w a list)(*strict*)
  apply(simp add: nth_opt_def)
  apply(case_tac w)
   apply(rename_tac k Aa i S1 SL A w a list)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A a list)(*strict*)
   apply(simp add: Xstep_mergeL_def)
   apply(simp add: Xstep_gen_def)
   apply(simp add: Xstep_elem_def)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_merge1_def)
   apply(case_tac "strict_prefix (ESplitItem_elim a) (ESplitItem_to (Xstep_elem SL \<lparr>prod_lhs = A, prod_rhs = []\<rparr>))")
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(clarsimp)
    apply(simp add: Xstep_merge1_toWasNotEliminated_def Xstep_elem_def)
    apply(case_tac "length S1=k")
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     apply(clarsimp)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(subgoal_tac "length S1 < k")
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     prefer 2
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(clarsimp)
    apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods a) @ ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a @ drop (length (ESplitItem_elim a) + length (option_to_list (ESplitItem_from a))) (ESplitItem_to SL)\<rparr> # list) ! k = SSlistX" for SSlistX)
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     prefer 2
     apply(rule nth_append_2_prime)
       apply(rename_tac k Aa i S1 SL A a list)(*strict*)
       apply(force)
      apply(rename_tac k Aa i S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(clarsimp)
    apply(thin_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL, ESplitItem_from = ESplitItem_from SL, ESplitItem_ignore = ESplitItem_ignore SL, ESplitItem_elim_prods = ESplitItem_elim_prods SL, ESplitItem_prods = ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (ESplitItem_elim_prods a) @ ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a @ drop (length (ESplitItem_elim a) + length (option_to_list (ESplitItem_from a))) (ESplitItem_to SL)\<rparr> # list) ! k = list ! (k - Suc (length S1))")
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(rule Esplit_signature_Cons_not_empty_setA2)
      apply(rename_tac k Aa i S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list)(*strict*)
   apply(clarsimp)
   apply(simp add: Xstep_merge1_toWasEliminated_def Xstep_elem_def)
   apply(subgoal_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ drop (length (ESplitItem_to SL)) (ESplitItem_elim a), ESplitItem_from = ESplitItem_from a, ESplitItem_ignore = ESplitItem_ignore a, ESplitItem_elim_prods = ESplitItem_elim_prods SL @ (ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods a))) # drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods a), ESplitItem_prods = ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a\<rparr> # list) ! k = SSlistX" for SSlistX)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac k Aa i S1 SL A a list)(*strict*)
      apply(force)
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(S1 @ \<lparr>ESplitItem_elim = ESplitItem_elim SL @ option_to_list (ESplitItem_from SL) @ drop (length (ESplitItem_to SL)) (ESplitItem_elim a), ESplitItem_from = ESplitItem_from a, ESplitItem_ignore = ESplitItem_ignore a, ESplitItem_elim_prods = ESplitItem_elim_prods SL @ (ESplitItem_prods SL @ \<lparr>prod_lhs = A, prod_rhs = []\<rparr> # foldl (@) [] (take (length (ESplitItem_to SL)) (ESplitItem_elim_prods a))) # drop (length (ESplitItem_to SL)) (ESplitItem_elim_prods a), ESplitItem_prods = ESplitItem_prods a, ESplitItem_elem = ESplitItem_elem a, ESplitItem_to = ESplitItem_to a\<rparr> # list) ! k = list ! (k - Suc (length S1))")
   apply(rename_tac k Aa i S1 SL A a list)(*strict*)
   apply(rule Esplit_signature_Cons_not_empty_setA2)
     apply(rename_tac k Aa i S1 SL A a list)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list)(*strict*)
   apply(force)
  apply(rename_tac k Aa i S1 SL A w a list aa lista)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i S1 SL A a list aa lista)(*strict*)
  apply(case_tac lista)
   apply(rename_tac k Aa i S1 SL A a list aa lista)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
   apply(simp add: Xstep_mergeL_def)
   apply(simp add: Xstep_gen_def)
   apply(simp add: Xstep_elem_def)
   apply(simp add: nth_opt_def)
   apply(simp add: Xstep_elem_def)
   apply(subgoal_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa]\<rparr>], ESplitItem_elem := nth_opt [aa] 0\<rparr> # a # list) ! k = (a#list)!SSX" for SSX)
    apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
      apply(force)
     apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
   apply(clarsimp)
   apply(thin_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa]\<rparr>], ESplitItem_elem := nth_opt [aa] 0\<rparr> # a # list) ! k = (a # list) ! (k - Suc (length S1))")
   apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
   apply(case_tac "k-Suc(length S1)")
    apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
    apply(clarsimp)
    apply(rule Esplit_signature_Cons_not_empty_setA)
     apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list aa)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list aa nat)(*strict*)
   apply(clarsimp)
   apply(rule Esplit_signature_Cons_not_empty_setA2)
     apply(rename_tac k Aa i S1 SL A a list aa nat)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list aa nat)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list aa nat)(*strict*)
   apply(force)
  apply(rename_tac k Aa i S1 SL A a list aa lista ab listb)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
  apply(subgoal_tac "listb=[]")
   apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
   prefer 2
   apply(rule LR1_at_most_two_symbols)
    apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
   apply(force)
  apply(rename_tac k Aa i S1 SL A a list aa ab listb)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i S1 SL A a list aa ab)(*strict*)
  apply(case_tac ab)
   apply(rename_tac k Aa i S1 SL A a list aa ab ac)(*strict*)
   prefer 2
   apply(rename_tac k Aa i S1 SL A a list aa ab b)(*strict*)
   apply(clarsimp)
   apply(rename_tac k Aa i S1 SL A a list aa b)(*strict*)
   apply(rule LR1_terminal_only_at_front_in_prods)
    apply(rename_tac k Aa i S1 SL A a list aa b)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list aa b)(*strict*)
   apply(force)
  apply(rename_tac k Aa i S1 SL A a list aa ab ac)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
  apply(simp add: Xstep_mergeL_def)
  apply(simp add: Xstep_gen_def)
  apply(subgoal_tac "nat_seq 0 0 = [0]")
   apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
   prefer 2
   apply (metis natUptTo_n_n)
  apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
  apply(clarsimp)
  apply(simp add: Xstep_gen_def)
  apply(simp add: Xstep_elem_def)
  apply(simp add: nth_opt_def)
  apply(subgoal_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa, teA ac]\<rparr>], ESplitItem_elem := Some aa, ESplitItem_to := ac # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ac, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ac), ESplitItem_to = []\<rparr> # a # list) ! k = (SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa, teA ac]\<rparr>], ESplitItem_elem := Some aa, ESplitItem_to := ac # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ac, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ac), ESplitItem_to = []\<rparr> # a # list)!SSX" for SSX)
   apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
   prefer 2
   apply(rule nth_append_2_prime)
     apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
     apply(force)
    apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
    apply(force)
   apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
   apply(force)
  apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
  apply(clarsimp)
  apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
  apply(case_tac "k-length S1")
   apply(rename_tac k Aa i S1 SL A a list aa ac)(*strict*)
   apply(clarsimp)
  apply(rename_tac k Aa i S1 SL A a list aa ac nat)(*strict*)
  apply(subgoal_tac "k=Suc nat+length S1")
   apply(rename_tac k Aa i S1 SL A a list aa ac nat)(*strict*)
   prefer 2
   apply(force)
  apply(rename_tac k Aa i S1 SL A a list aa ac nat)(*strict*)
  apply(clarsimp)
  apply(rename_tac Aa i S1 SL A a list aa ac nat)(*strict*)
  apply(case_tac nat)
   apply(rename_tac Aa i S1 SL A a list aa ac nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac Aa i S1 SL A a list aa)(*strict*)
   apply(subgoal_tac "i=length S1")
    apply(rename_tac Aa i S1 SL A a list aa)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac Aa i S1 SL A a list aa)(*strict*)
   apply(clarsimp)
   apply(rename_tac Aa S1 SL A a list aa)(*strict*)
   apply(simp add: Eident_lines_def Eident_line_def)
  apply(rename_tac Aa i S1 SL A a list aa ac nat nata)(*strict*)
  apply(clarsimp)
  apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
  apply(case_tac "i=Suc(length S1)")
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac Aa S1 SL A a list aa ac nata)(*strict*)
   apply(simp add: Eident_lines_def Eident_line_def)
   apply(clarsimp)
   apply(subgoal_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa, teA ac]\<rparr>], ESplitItem_elem := Some aa, ESplitItem_to := ac # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ac, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ac), ESplitItem_to = []\<rparr> # a # list) ! Suc (length S1) = (\<lparr>ESplitItem_elim = [], ESplitItem_from = Some ac, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ac), ESplitItem_to = []\<rparr> # a # list)!SSY" for SSY)
    apply(rename_tac Aa S1 SL A a list aa ac nata)(*strict*)
    prefer 2
    apply(rule nth_append_2_prime)
      apply(rename_tac Aa S1 SL A a list aa ac nata)(*strict*)
      apply(force)
     apply(rename_tac Aa S1 SL A a list aa ac nata)(*strict*)
     apply(force)
    apply(rename_tac Aa S1 SL A a list aa ac nata)(*strict*)
    apply(force)
   apply(rename_tac Aa S1 SL A a list aa ac nata)(*strict*)
   apply(clarsimp)
   apply(case_tac nata)
    apply(rename_tac Aa S1 SL A a list aa ac nata)(*strict*)
    apply(clarsimp)
    apply(rename_tac Aa S1 SL A a list aa ac)(*strict*)
    apply(rule Esplit_signature_Cons_not_empty_setA)
     apply(rename_tac Aa S1 SL A a list aa ac)(*strict*)
     apply(force)
    apply(rename_tac Aa S1 SL A a list aa ac)(*strict*)
    apply(force)
   apply(rename_tac Aa S1 SL A a list aa ac nata nat)(*strict*)
   apply(clarsimp)
   apply(rename_tac Aa S1 SL A a list aa ac nat)(*strict*)
   apply(rule Esplit_signature_Cons_not_empty_setA2)
     apply(rename_tac Aa S1 SL A a list aa ac nat)(*strict*)
     apply(force)
    apply(rename_tac Aa S1 SL A a list aa ac nat)(*strict*)
    apply(force)
   apply(rename_tac Aa S1 SL A a list aa ac nat)(*strict*)
   apply(force)
  apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
  apply(simp add: Eident_lines_def Eident_line_def)
  apply(subgoal_tac "(S1 @ SL\<lparr>ESplitItem_prods := ESplitItem_prods SL @ [\<lparr>prod_lhs = A, prod_rhs = [aa, teA ac]\<rparr>], ESplitItem_elem := Some aa, ESplitItem_to := ac # ESplitItem_to SL\<rparr> # \<lparr>ESplitItem_elim = [], ESplitItem_from = Some ac, ESplitItem_ignore = ESplitItem_to SL @ ESplitItem_ignore SL, ESplitItem_elim_prods = [], ESplitItem_prods = [], ESplitItem_elem = Some (teA ac), ESplitItem_to = []\<rparr> # a # list) ! i = (a#list)!SSX" for SSX)
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   prefer 2
   apply(rule nth_append_2_prime)
     apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
     apply(force)
    apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
    apply(force)
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   apply(clarsimp)
   apply(case_tac "i<Suc (Suc (length S1))")
    apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   apply(clarsimp)
   apply(case_tac "Suc i=Suc (Suc (length S1))")
    apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
    apply(clarsimp)
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   apply(subgoal_tac "i < (Suc (length S1))")
    apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   apply(clarsimp)
   apply(case_tac "Suc i = Suc(length S1)")
    apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
    apply(force)
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   apply(subgoal_tac "Suc i<Suc (length S1)")
    apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
    prefer 2
    apply(force)
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   apply(force)
  apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
  apply(clarsimp)
  apply(case_tac nata)
   apply(rename_tac Aa i S1 SL A a list aa ac nata)(*strict*)
   apply(clarsimp)
   apply(rename_tac Aa i S1 SL A a list aa ac)(*strict*)
   apply(rule Esplit_signature_Cons_not_empty_setA)
    apply(rename_tac Aa i S1 SL A a list aa ac)(*strict*)
    apply(force)
   apply(rename_tac Aa i S1 SL A a list aa ac)(*strict*)
   apply(force)
  apply(rename_tac Aa i S1 SL A a list aa ac nata nat)(*strict*)
  apply(rule Esplit_signature_Cons_not_empty_setA2)
    apply(rename_tac Aa i S1 SL A a list aa ac nata nat)(*strict*)
    apply(force)
   apply(rename_tac Aa i S1 SL A a list aa ac nata nat)(*strict*)
   apply(force)
  apply(rename_tac Aa i S1 SL A a list aa ac nata nat)(*strict*)
  apply(force)
  done

theorem Esplit_derivation_enforces_EValidSplitExt: "
  Esplit_TSstructure G
  \<Longrightarrow> F2LR1inputx G G'
  \<Longrightarrow> split_TSstructure G
  \<Longrightarrow> Esplit.derivation_initial G d
  \<Longrightarrow> d n = Some (pair e S)
  \<Longrightarrow> EValidSplitExt S"
  apply(simp add: EValidSplitExt_def)
  apply(rule conjI)
   apply(simp add: EValidSplitExt_no_elim_before_nonterminal_def)
   apply(clarsimp)
   apply(rename_tac k A i)(*strict*)
   apply(rule Esplit_derivation_enforces_EValidSplitExt_no_elim_before_nonterminal)
          apply(rename_tac k A i)(*strict*)
          apply(force)
         apply(rename_tac k A i)(*strict*)
         apply(force)
        apply(rename_tac k A i)(*strict*)
        apply(force)
       apply(rename_tac k A i)(*strict*)
       apply(force)
      apply(rename_tac k A i)(*strict*)
      apply(force)
     apply(rename_tac k A i)(*strict*)
     apply(force)
    apply(rename_tac k A i)(*strict*)
    apply(force)
   apply(rename_tac k A i)(*strict*)
   apply(force)
  apply(rule conjI)
   apply(simp add: EValidSplitExt_no_pop_in_prods_before_nonterminal_def)
   apply(clarsimp)
   apply(rename_tac k A i j)(*strict*)
   apply(subgoal_tac "X" for X)
    apply(rename_tac k A i j)(*strict*)
    prefer 2
    apply(rule Esplit_derivation_enforces_EValidSplitExt_no_pop_in_prods_before_nonterminal)
            apply(rename_tac k A i j)(*strict*)
            apply(force)
           apply(rename_tac k A i j)(*strict*)
           apply(force)
          apply(rename_tac k A i j)(*strict*)
          apply(force)
         apply(rename_tac k A i j)(*strict*)
         apply(force)
        apply(rename_tac k A i j)(*strict*)
        apply(force)
       apply(rename_tac k A i j)(*strict*)
       apply(force)
      apply(rename_tac k A i j)(*strict*)
      apply(force)
     apply(rename_tac k A i j)(*strict*)
     apply(force)
    apply(rename_tac k A i j)(*strict*)
    apply(force)
   apply(rename_tac k A i j)(*strict*)
   apply(force)
  apply(simp add: EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal_def)
  apply(rule allI)
  apply(rename_tac k)(*strict*)
  apply(rule impI)
  apply(rule impI)
  apply(rule allI)
  apply(rename_tac k i)(*strict*)
  apply(rule impI)
  apply(erule exE)+
  apply(rename_tac k i A)(*strict*)
  apply(rule Esplit_derivation_enforces_EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal)
         apply(rename_tac k i A)(*strict*)
         apply(force)
        apply(rename_tac k i A)(*strict*)
        apply(force)
       apply(rename_tac k i A)(*strict*)
       apply(force)
      apply(rename_tac k i A)(*strict*)
      apply(force)
     apply(rename_tac k i A)(*strict*)
     apply(force)
    apply(rename_tac k i A)(*strict*)
    apply(force)
   apply(rename_tac k i A)(*strict*)
   apply(force)
  apply(rename_tac k i A)(*strict*)
  apply(force)
  done

hide_fact Esplit_derivation_enforces_EValidSplitExt_ident_line_is_always_at_the_latest_nonterminal
  (* important entirely_ignored_can_not_happend_to_early *)
  (* important Esplit_derivation_enforces_EValidSplitExt *)
  (* important restrict_equal_before_step_nonterminal *)

end
